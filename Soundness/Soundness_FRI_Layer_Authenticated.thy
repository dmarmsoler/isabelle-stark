(*  Title:      Stark/Soundness_FRI_Layer_Authenticated.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Layer_Authenticated
  imports Soundness_FRI_Layer_Merkle
begin

text \<open>
  Authenticated FRI layer evidence paired with transcript layer evidence.

  The exact equality between the layer chunk recorded in
  @{term accepted_fri_opening_transcript} and the layer chunk authenticated by
  the verifier is still intentionally not asserted here.  Instead this theory
  packages the checked facts that are currently available without a broad
  replay induction: the transcript gives a local FRI step, and the verifier
  execution gives an authenticated FRI chunk at the same root, layer length,
  and replayed query index.
\<close>

context soundness
begin

definition generic_fri_transcript_step_with_authenticated_chunk
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "generic_fri_transcript_step_with_authenticated_chunk roots challenges
      query_idxs round_layers final_state round_idx layer_idx \<longleftrightarrow>
    fri_round_layer_evidence roots challenges query_idxs round_idx
      layer_idx round_layers \<and>
    (\<exists>auth_chunk.
      fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        auth_chunk final_state)"

lemma generic_fri_transcript_step_with_authenticated_chunkI:
  assumes step:
    "fri_round_layer_evidence roots challenges query_idxs round_idx
      layer_idx round_layers"
    and auth:
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        auth_chunk final_state"
  shows
    "generic_fri_transcript_step_with_authenticated_chunk roots challenges
      query_idxs round_layers final_state round_idx layer_idx"
  using assms
  unfolding generic_fri_transcript_step_with_authenticated_chunk_def
  by blast

lemma generic_fri_transcript_step_with_authenticated_chunkE:
  assumes
    "generic_fri_transcript_step_with_authenticated_chunk roots challenges
      query_idxs round_layers final_state round_idx layer_idx"
  obtains auth_chunk where
    "fri_round_layer_evidence roots challenges query_idxs round_idx
      layer_idx round_layers"
    "fri_layer_chunk_authenticated (roots ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      auth_chunk final_state"
  using assms
  unfolding generic_fri_transcript_step_with_authenticated_chunk_def
  by blast

definition generic_fri_authenticated_same_layer_opening_conflict
  :: "'f list \<Rightarrow> nat list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "generic_fri_authenticated_same_layer_opening_conflict roots query_idxs
      final_state \<longleftrightarrow>
    (\<exists>round_idx round_idx' layer_idx opn opn'.
      round_idx < length query_idxs \<and>
      round_idx' < length query_idxs \<and>
      layer_idx < length roots \<and>
      authenticated_opening_in final_state opn \<and>
      authenticated_opening_in final_state opn' \<and>
      opening_root opn = roots ! layer_idx \<and>
      opening_root opn' = roots ! layer_idx \<and>
      opening_length opn = fri_evidence_layer_len roots layer_idx \<and>
      opening_length opn' = fri_evidence_layer_len roots layer_idx \<and>
      (opening_index opn =
        fri_evidence_layer_idx roots query_idxs round_idx layer_idx \<or>
       opening_index opn =
        fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)) \<and>
      (opening_index opn' =
        fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<or>
       opening_index opn' =
        fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)) \<and>
      opening_index opn = opening_index opn' \<and>
      opening_value opn \<noteq> opening_value opn')"

lemma generic_fri_authenticated_same_layer_opening_conflictI:
  assumes round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length roots"
    and auth: "authenticated_opening_in final_state opn"
      "authenticated_opening_in final_state opn'"
    and root: "opening_root opn = roots ! layer_idx"
      "opening_root opn' = roots ! layer_idx"
    and len:
      "opening_length opn = fri_evidence_layer_len roots layer_idx"
      "opening_length opn' = fri_evidence_layer_len roots layer_idx"
    and idx:
      "opening_index opn =
        fri_evidence_layer_idx roots query_idxs round_idx layer_idx \<or>
       opening_index opn =
        fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)"
      "opening_index opn' =
        fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<or>
       opening_index opn' =
        fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)"
    and same_index: "opening_index opn = opening_index opn'"
    and neq: "opening_value opn \<noteq> opening_value opn'"
  shows
    "generic_fri_authenticated_same_layer_opening_conflict roots query_idxs
      final_state"
  unfolding generic_fri_authenticated_same_layer_opening_conflict_def
  by (intro exI[of _ round_idx] exI[of _ round_idx']
      exI[of _ layer_idx] exI[of _ opn] exI[of _ opn'] conjI)
    (use assms in auto)

lemma generic_fri_authenticated_same_layer_opening_conflict_imp_partial_merkle:
  assumes
    "generic_fri_authenticated_same_layer_opening_conflict roots query_idxs
      final_state"
  shows "partial_merkle_inconsistency_bad s (Some (result, final_state))"
proof -
  from assms obtain round_idx round_idx' layer_idx opn opn' where
    auth: "authenticated_opening_in final_state opn"
      "authenticated_opening_in final_state opn'"
    and roots:
      "opening_root opn = roots ! layer_idx"
      "opening_root opn' = roots ! layer_idx"
    and lengths:
      "opening_length opn = fri_evidence_layer_len roots layer_idx"
      "opening_length opn' = fri_evidence_layer_len roots layer_idx"
    and same_index: "opening_index opn = opening_index opn'"
    and neq: "opening_value opn \<noteq> opening_value opn'"
    unfolding generic_fri_authenticated_same_layer_opening_conflict_def
    by blast
  have same_root: "opening_root opn = opening_root opn'"
    using roots by simp
  have same_length: "opening_length opn = opening_length opn'"
    using lengths by simp
  show ?thesis
    unfolding partial_merkle_inconsistency_bad_def accepted_def
    by (intro conjI exI[of _ result] exI[of _ final_state]
        exI[of _ opn] exI[of _ opn'])
      (use auth same_root same_length same_index neq in simp_all)
qed

lemma generic_fri_authenticated_same_layer_opening_conflictI_base_base:
  assumes round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length roots"
    and auth:
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        chunk final_state"
    and auth':
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        chunk' final_state"
    and chunk:
      "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
        xp xp_path xn xn_path chunk"
    and chunk':
      "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
        yp yp_path yn yn_path chunk'"
    and same_index:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
       fri_evidence_layer_idx roots query_idxs round_idx' layer_idx"
    and neq: "xp \<noteq> yp"
  shows
    "generic_fri_authenticated_same_layer_opening_conflict roots query_idxs
      final_state"
proof -
  from fri_layer_chunk_authenticated_matching_values[OF auth chunk]
  obtain xp_path' xn_path' where auth_xp:
    "authenticated_opening_in final_state
      \<lparr>opening_root = roots ! layer_idx,
       opening_length = fri_evidence_layer_len roots layer_idx,
       opening_index = fri_evidence_layer_idx roots query_idxs round_idx
         layer_idx,
       opening_value = xp,
       opening_path = xp_path'\<rparr>"
    by blast
  from fri_layer_chunk_authenticated_matching_values[OF auth' chunk']
  obtain yp_path' yn_path' where auth_yp:
    "authenticated_opening_in final_state
      \<lparr>opening_root = roots ! layer_idx,
       opening_length = fri_evidence_layer_len roots layer_idx,
       opening_index = fri_evidence_layer_idx roots query_idxs round_idx'
         layer_idx,
       opening_value = yp,
       opening_path = yp_path'\<rparr>"
    by blast
  let ?opn =
    "\<lparr>opening_root = roots ! layer_idx,
     opening_length = fri_evidence_layer_len roots layer_idx,
     opening_index = fri_evidence_layer_idx roots query_idxs round_idx
       layer_idx,
     opening_value = xp,
     opening_path = xp_path'\<rparr>"
  let ?opn' =
    "\<lparr>opening_root = roots ! layer_idx,
     opening_length = fri_evidence_layer_len roots layer_idx,
     opening_index = fri_evidence_layer_idx roots query_idxs round_idx'
       layer_idx,
     opening_value = yp,
     opening_path = yp_path'\<rparr>"
  show ?thesis
    by (rule generic_fri_authenticated_same_layer_opening_conflictI
        [OF round_bound round_bound' layer_bound auth_xp auth_yp])
      (use same_index neq in simp_all)
qed

lemma generic_fri_authenticated_same_layer_opening_conflictI_base_sibling:
  assumes round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length roots"
    and auth:
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        chunk final_state"
    and auth':
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        chunk' final_state"
    and chunk:
      "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
        xp xp_path xn xn_path chunk"
    and chunk':
      "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
        yp yp_path yn yn_path chunk'"
    and same_index:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
       fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)"
    and neq: "xp \<noteq> yn"
  shows
    "generic_fri_authenticated_same_layer_opening_conflict roots query_idxs
      final_state"
proof -
  from fri_layer_chunk_authenticated_matching_values[OF auth chunk]
  obtain xp_path' xn_path' where auth_xp:
    "authenticated_opening_in final_state
      \<lparr>opening_root = roots ! layer_idx,
       opening_length = fri_evidence_layer_len roots layer_idx,
       opening_index = fri_evidence_layer_idx roots query_idxs round_idx
         layer_idx,
       opening_value = xp,
       opening_path = xp_path'\<rparr>"
    by blast
  from fri_layer_chunk_authenticated_matching_values[OF auth' chunk']
  obtain yp_path' yn_path' where auth_yn:
    "authenticated_opening_in final_state
      \<lparr>opening_root = roots ! layer_idx,
       opening_length = fri_evidence_layer_len roots layer_idx,
       opening_index =
         fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx),
       opening_value = yn,
       opening_path = yn_path'\<rparr>"
    by blast
  show ?thesis
    by (rule generic_fri_authenticated_same_layer_opening_conflictI
        [OF round_bound round_bound' layer_bound auth_xp auth_yn])
      (use same_index neq in simp_all)
qed

lemma generic_fri_authenticated_same_layer_opening_conflictI_sibling_base:
  assumes round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length roots"
    and auth:
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        chunk final_state"
    and auth':
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        chunk' final_state"
    and chunk:
      "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
        xp xp_path xn xn_path chunk"
    and chunk':
      "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
        yp yp_path yn yn_path chunk'"
    and same_index:
      "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
       fri_evidence_layer_idx roots query_idxs round_idx' layer_idx"
    and neq: "xn \<noteq> yp"
  shows
    "generic_fri_authenticated_same_layer_opening_conflict roots query_idxs
      final_state"
proof -
  from fri_layer_chunk_authenticated_matching_values[OF auth chunk]
  obtain xp_path' xn_path' where auth_xn:
    "authenticated_opening_in final_state
      \<lparr>opening_root = roots ! layer_idx,
       opening_length = fri_evidence_layer_len roots layer_idx,
       opening_index =
         fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx),
       opening_value = xn,
       opening_path = xn_path'\<rparr>"
    by blast
  from fri_layer_chunk_authenticated_matching_values[OF auth' chunk']
  obtain yp_path' yn_path' where auth_yp:
    "authenticated_opening_in final_state
      \<lparr>opening_root = roots ! layer_idx,
       opening_length = fri_evidence_layer_len roots layer_idx,
       opening_index = fri_evidence_layer_idx roots query_idxs round_idx'
         layer_idx,
       opening_value = yp,
       opening_path = yp_path'\<rparr>"
    by blast
  show ?thesis
    by (rule generic_fri_authenticated_same_layer_opening_conflictI
        [OF round_bound round_bound' layer_bound auth_xn auth_yp])
      (use same_index neq in simp_all)
qed

lemma generic_fri_authenticated_same_layer_opening_conflictI_sibling_sibling:
  assumes round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length roots"
    and auth:
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        chunk final_state"
    and auth':
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        chunk' final_state"
    and chunk:
      "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
        xp xp_path xn xn_path chunk"
    and chunk':
      "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
        yp yp_path yn yn_path chunk'"
    and same_index:
      "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
       fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)"
    and neq: "xn \<noteq> yn"
  shows
    "generic_fri_authenticated_same_layer_opening_conflict roots query_idxs
      final_state"
proof -
  from fri_layer_chunk_authenticated_matching_values[OF auth chunk]
  obtain xp_path' xn_path' where auth_xn:
    "authenticated_opening_in final_state
      \<lparr>opening_root = roots ! layer_idx,
       opening_length = fri_evidence_layer_len roots layer_idx,
       opening_index =
         fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx),
       opening_value = xn,
       opening_path = xn_path'\<rparr>"
    by blast
  from fri_layer_chunk_authenticated_matching_values[OF auth' chunk']
  obtain yp_path' yn_path' where auth_yn:
    "authenticated_opening_in final_state
      \<lparr>opening_root = roots ! layer_idx,
       opening_length = fri_evidence_layer_len roots layer_idx,
       opening_index =
         fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx),
       opening_value = yn,
       opening_path = yn_path'\<rparr>"
    by blast
  show ?thesis
    by (rule generic_fri_authenticated_same_layer_opening_conflictI
        [OF round_bound round_bound' layer_bound auth_xn auth_yn])
      (use same_index neq in simp_all)
qed

definition generic_fri_recorded_layer_chunk_authenticated
  :: "'f list \<Rightarrow> nat list \<Rightarrow> 'f list list list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "generic_fri_recorded_layer_chunk_authenticated roots query_idxs
      round_layers final_state round_idx layer_idx \<longleftrightarrow>
    fri_layer_chunk_authenticated (roots ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (round_layers ! round_idx ! layer_idx) final_state"

definition generic_fri_authenticated_slot_recorded_chunk_gap
  :: "'f list \<Rightarrow> nat list \<Rightarrow> 'f list list list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "generic_fri_authenticated_slot_recorded_chunk_gap roots query_idxs
      round_layers final_state \<longleftrightarrow>
    (\<exists>round_idx layer_idx auth_chunk.
      round_idx < length query_idxs \<and>
      layer_idx < length roots \<and>
      fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        auth_chunk final_state \<and>
      \<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
        round_layers final_state round_idx layer_idx)"

lemma generic_fri_transcript_step_auth_missing_imp_authenticated_slot_recorded_chunk_gap:
  assumes step:
    "generic_fri_transcript_step_with_authenticated_chunk roots challenges
      query_idxs round_layers final_state round_idx layer_idx"
    and missing:
      "\<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
        round_layers final_state round_idx layer_idx"
  shows
    "generic_fri_authenticated_slot_recorded_chunk_gap roots query_idxs
      round_layers final_state"
proof -
  from step obtain auth_chunk where evidence:
    "fri_round_layer_evidence roots challenges query_idxs round_idx layer_idx
      round_layers"
    and auth:
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        auth_chunk final_state"
    by (rule generic_fri_transcript_step_with_authenticated_chunkE)
  from evidence have round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length roots"
    by (auto elim: fri_round_layer_evidenceE)
  show ?thesis
    unfolding generic_fri_authenticated_slot_recorded_chunk_gap_def
    by (intro exI conjI)
      (rule round_bound, rule layer_bound, rule auth, rule missing)
qed

definition generic_fri_sampled_same_layer_recorded_auth_gap
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "generic_fri_sampled_same_layer_recorded_auth_gap roots challenges
      query_idxs round_layers final_state \<longleftrightarrow>
    (\<exists>round_idx round_idx' layer_idx.
      round_idx < length query_idxs \<and>
      round_idx' < length query_idxs \<and>
      layer_idx < length challenges \<and>
      generic_fri_sampled_same_layer_opening_conflict roots challenges
        query_idxs round_layers \<and>
      (\<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
        round_layers final_state round_idx layer_idx \<or>
       \<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
        round_layers final_state round_idx' layer_idx))"

definition generic_fri_sampled_same_layer_authenticated_recorded_auth_gap
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "generic_fri_sampled_same_layer_authenticated_recorded_auth_gap roots
      challenges query_idxs round_layers final_state \<longleftrightarrow>
    (\<exists>round_idx round_idx' layer_idx.
      round_idx < length query_idxs \<and>
      round_idx' < length query_idxs \<and>
      layer_idx < length challenges \<and>
      generic_fri_sampled_same_layer_opening_conflict roots challenges
        query_idxs round_layers \<and>
      ((generic_fri_transcript_step_with_authenticated_chunk roots challenges
          query_idxs round_layers final_state round_idx layer_idx \<and>
        \<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
          round_layers final_state round_idx layer_idx) \<or>
       (generic_fri_transcript_step_with_authenticated_chunk roots challenges
          query_idxs round_layers final_state round_idx' layer_idx \<and>
        \<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
          round_layers final_state round_idx' layer_idx)))"

lemma generic_fri_authenticated_recorded_auth_gap_imp_slot_recorded_chunk_gap:
  assumes
    "generic_fri_sampled_same_layer_authenticated_recorded_auth_gap roots
      challenges query_idxs round_layers final_state"
  shows
    "generic_fri_authenticated_slot_recorded_chunk_gap roots query_idxs
      round_layers final_state"
proof -
  from assms obtain round_idx round_idx' layer_idx where
    gap:
      "(generic_fri_transcript_step_with_authenticated_chunk roots challenges
          query_idxs round_layers final_state round_idx layer_idx \<and>
        \<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
          round_layers final_state round_idx layer_idx) \<or>
       (generic_fri_transcript_step_with_authenticated_chunk roots challenges
          query_idxs round_layers final_state round_idx' layer_idx \<and>
        \<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
          round_layers final_state round_idx' layer_idx)"
    unfolding generic_fri_sampled_same_layer_authenticated_recorded_auth_gap_def
    by blast
  then show ?thesis
  proof
    assume left:
      "generic_fri_transcript_step_with_authenticated_chunk roots challenges
        query_idxs round_layers final_state round_idx layer_idx \<and>
       \<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
        round_layers final_state round_idx layer_idx"
    show ?thesis
      by (rule
          generic_fri_transcript_step_auth_missing_imp_authenticated_slot_recorded_chunk_gap
          [of roots challenges query_idxs round_layers final_state round_idx
            layer_idx])
        (use left in simp_all)
  next
    assume right:
      "generic_fri_transcript_step_with_authenticated_chunk roots challenges
        query_idxs round_layers final_state round_idx' layer_idx \<and>
       \<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
        round_layers final_state round_idx' layer_idx"
    show ?thesis
      by (rule
          generic_fri_transcript_step_auth_missing_imp_authenticated_slot_recorded_chunk_gap
          [of roots challenges query_idxs round_layers final_state round_idx'
            layer_idx])
        (use right in simp_all)
  qed
qed

lemma generic_fri_recorded_auth_gap_imp_authenticated_recorded_auth_gap:
  assumes gap:
    "generic_fri_sampled_same_layer_recorded_auth_gap roots challenges
      query_idxs round_layers final_state"
    and auth_step:
      "\<And>round_idx layer_idx.
        round_idx < length query_idxs \<Longrightarrow>
        layer_idx < length challenges \<Longrightarrow>
        generic_fri_transcript_step_with_authenticated_chunk roots
          challenges query_idxs round_layers final_state round_idx layer_idx"
  shows
    "generic_fri_sampled_same_layer_authenticated_recorded_auth_gap roots
      challenges query_idxs round_layers final_state"
proof -
  from gap obtain round_idx round_idx' layer_idx where
    round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
    and conflict:
      "generic_fri_sampled_same_layer_opening_conflict roots challenges
        query_idxs round_layers"
    and missing:
      "\<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
        round_layers final_state round_idx layer_idx \<or>
       \<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
        round_layers final_state round_idx' layer_idx"
    unfolding generic_fri_sampled_same_layer_recorded_auth_gap_def
    by blast
  show ?thesis
  proof (cases
      "\<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
        round_layers final_state round_idx layer_idx")
    case True
    have step:
      "generic_fri_transcript_step_with_authenticated_chunk roots challenges
        query_idxs round_layers final_state round_idx layer_idx"
      by (rule auth_step[OF round_bound layer_bound])
    show ?thesis
      unfolding
        generic_fri_sampled_same_layer_authenticated_recorded_auth_gap_def
      by (intro exI conjI disjI1)
        (rule round_bound, rule round_bound', rule layer_bound,
          rule conflict, rule step, rule True)
  next
    case False
    then have missing':
      "\<not> generic_fri_recorded_layer_chunk_authenticated roots query_idxs
        round_layers final_state round_idx' layer_idx"
      using missing by simp
    have step:
      "generic_fri_transcript_step_with_authenticated_chunk roots challenges
        query_idxs round_layers final_state round_idx' layer_idx"
      by (rule auth_step[OF round_bound' layer_bound])
    show ?thesis
      unfolding
        generic_fri_sampled_same_layer_authenticated_recorded_auth_gap_def
      by (intro exI conjI disjI2)
        (rule round_bound, rule round_bound', rule layer_bound,
          rule conflict, rule step, rule missing')
  qed
qed

definition generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state \<longleftrightarrow>
    (\<exists>round_idx round_idx' layer_idx
        xp xp_path xn xn_path yp yp_path yn yn_path.
      round_idx < length query_idxs \<and>
      round_idx' < length query_idxs \<and>
      layer_idx < length challenges \<and>
      fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx) \<and>
      fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
        yp yp_path yn yn_path
        (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx'
          layer_idx yp yn)
        (round_layers ! round_idx' ! layer_idx) \<and>
      fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (round_layers ! round_idx ! layer_idx) final_state \<and>
      fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (round_layers ! round_idx' ! layer_idx) final_state \<and>
      ((fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xp \<noteq> yp) \<or>
       (fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xp \<noteq> yn) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xn \<noteq> yp) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xn \<noteq> yn)))"

lemma generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_imp_authenticated:
  assumes conflict:
    "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state"
    and len_challenges: "length challenges = length roots"
  shows
    "generic_fri_authenticated_same_layer_opening_conflict roots query_idxs
      final_state"
proof -
  from conflict obtain round_idx round_idx' layer_idx
      xp xp_path xn xn_path yp yp_path yn yn_path where
    round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound_ch: "layer_idx < length challenges"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx)"
    and step':
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
        yp yp_path yn yn_path
        (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx'
          layer_idx yp yn)
        (round_layers ! round_idx' ! layer_idx)"
    and auth:
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (round_layers ! round_idx ! layer_idx) final_state"
    and auth':
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (round_layers ! round_idx' ! layer_idx) final_state"
    and cases:
      "(fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xp \<noteq> yp) \<or>
       (fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xp \<noteq> yn) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xn \<noteq> yp) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xn \<noteq> yn)"
    unfolding
      generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_def
    by blast
  have layer_bound: "layer_idx < length roots"
    using layer_bound_ch len_challenges by simp
  have chunk:
    "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
      xp xp_path xn xn_path (round_layers ! round_idx ! layer_idx)"
    using fri_layer_step_evidenceD(4)[OF step] .
  have chunk':
    "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
      yp yp_path yn yn_path (round_layers ! round_idx' ! layer_idx)"
    using fri_layer_step_evidenceD(4)[OF step'] .
  from cases show ?thesis
  proof
    assume c:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xp \<noteq> yp"
    show ?thesis
      by (rule generic_fri_authenticated_same_layer_opening_conflictI_base_base
          [OF round_bound round_bound' layer_bound auth auth' chunk chunk'])
        (use c in simp_all)
  next
    assume rest:
      "(fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xp \<noteq> yn) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xn \<noteq> yp) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xn \<noteq> yn)"
    then show ?thesis
    proof
      assume c:
        "fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xp \<noteq> yn"
      show ?thesis
        by (rule generic_fri_authenticated_same_layer_opening_conflictI_base_sibling
            [OF round_bound round_bound' layer_bound auth auth' chunk chunk'])
          (use c in simp_all)
    next
      assume rest':
        "(fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xn \<noteq> yp) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xn \<noteq> yn)"
      then show ?thesis
      proof
        assume c:
          "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xn \<noteq> yp"
        show ?thesis
          by (rule generic_fri_authenticated_same_layer_opening_conflictI_sibling_base
              [OF round_bound round_bound' layer_bound auth auth' chunk chunk'])
            (use c in simp_all)
      next
        assume c:
          "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xn \<noteq> yn"
        show ?thesis
          by (rule generic_fri_authenticated_same_layer_opening_conflictI_sibling_sibling
              [OF round_bound round_bound' layer_bound auth auth' chunk chunk'])
            (use c in simp_all)
      qed
    qed
  qed
qed

lemma generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_imp_sampled:
  assumes
    "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state"
  shows
    "generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
  using assms
  unfolding
    generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_def
    generic_fri_sampled_same_layer_opening_conflict_def
  by blast

lemma generic_fri_sampled_same_layer_imp_authenticated_or_recorded_auth_gap:
  assumes conflict:
    "generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
  shows
    "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state \<or>
     generic_fri_sampled_same_layer_recorded_auth_gap roots challenges
      query_idxs round_layers final_state"
proof -
  from conflict obtain round_idx round_idx' layer_idx
      xp xp_path xn xn_path yp yp_path yn yn_path where
    round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx)"
    and step':
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
        yp yp_path yn yn_path
        (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx'
          layer_idx yp yn)
        (round_layers ! round_idx' ! layer_idx)"
    and cases:
      "(fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xp \<noteq> yp) \<or>
       (fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xp \<noteq> yn) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xn \<noteq> yp) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xn \<noteq> yn)"
    unfolding generic_fri_sampled_same_layer_opening_conflict_def
    by blast
  show ?thesis
  proof (cases
      "generic_fri_recorded_layer_chunk_authenticated roots query_idxs
        round_layers final_state round_idx layer_idx \<and>
       generic_fri_recorded_layer_chunk_authenticated roots query_idxs
        round_layers final_state round_idx' layer_idx")
    case True
    have auth:
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (round_layers ! round_idx ! layer_idx) final_state"
      using True
      unfolding generic_fri_recorded_layer_chunk_authenticated_def
      by simp
    have auth':
      "fri_layer_chunk_authenticated (roots ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (round_layers ! round_idx' ! layer_idx) final_state"
      using True
      unfolding generic_fri_recorded_layer_chunk_authenticated_def
      by simp
    have
      "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        roots challenges query_idxs round_layers final_state"
      unfolding
        generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_def
      by (intro exI conjI)
        (rule round_bound, rule round_bound', rule layer_bound, rule step,
          rule step', rule auth, rule auth', rule cases)
    then show ?thesis by simp
  next
    case False
    have
      "generic_fri_sampled_same_layer_recorded_auth_gap roots challenges
        query_idxs round_layers final_state"
      unfolding generic_fri_sampled_same_layer_recorded_auth_gap_def
      by (intro exI conjI)
        (rule round_bound, rule round_bound', rule layer_bound,
          rule conflict, use False in simp)
    then show ?thesis by simp
  qed
qed

lemma generic_fri_sampled_same_layer_auth_gap_imp_recorded_auth_gap:
  assumes conflict:
    "generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
    and no_auth:
      "\<not> generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        roots challenges query_idxs round_layers final_state"
  shows
    "generic_fri_sampled_same_layer_recorded_auth_gap roots challenges
      query_idxs round_layers final_state"
  using generic_fri_sampled_same_layer_imp_authenticated_or_recorded_auth_gap
    [OF conflict, of final_state] no_auth
  by blast

lemma generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_imp_partial_merkle:
  assumes conflict:
    "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state"
    and len_challenges: "length challenges = length roots"
  shows "partial_merkle_inconsistency_bad s (Some (result, final_state))"
proof -
  have auth_conflict:
    "generic_fri_authenticated_same_layer_opening_conflict roots query_idxs
      final_state"
    by (rule
        generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_imp_authenticated
        [OF conflict len_challenges])
  show ?thesis
    by (rule generic_fri_authenticated_same_layer_opening_conflict_imp_partial_merkle
        [OF auth_conflict])
qed

definition generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      nat list \<Rightarrow> 'f list list list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      candidate_table roots challenges final_value query_idxs round_layers
      final_state \<longleftrightarrow>
    generic_fri_sampled_base_opening_conflict candidate_table roots
      challenges query_idxs round_layers \<or>
    generic_fri_sampled_next_value_conflict roots challenges query_idxs
      round_layers \<or>
    generic_fri_sampled_successor_opening_conflict roots challenges
      query_idxs round_layers \<or>
    generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state \<or>
    generic_fri_sampled_final_value_conflict roots challenges final_value
      query_idxs round_layers"

definition generic_fri_sampled_assignment_conflict_without_same_layer
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      nat list \<Rightarrow> 'f list list list \<Rightarrow> bool"
where
  "generic_fri_sampled_assignment_conflict_without_same_layer
      candidate_table roots challenges final_value query_idxs round_layers
      \<longleftrightarrow>
    generic_fri_sampled_base_opening_conflict candidate_table roots
      challenges query_idxs round_layers \<or>
    generic_fri_sampled_next_value_conflict roots challenges query_idxs
      round_layers \<or>
    generic_fri_sampled_successor_opening_conflict roots challenges
      query_idxs round_layers \<or>
    generic_fri_sampled_final_value_conflict roots challenges final_value
      query_idxs round_layers"

lemma generic_fri_sampled_assignment_conflict_without_same_layer_split:
  assumes
    "generic_fri_sampled_assignment_conflict_without_same_layer
      candidate_table roots challenges final_value query_idxs round_layers"
  shows
    "generic_fri_sampled_base_opening_conflict candidate_table roots
      challenges query_idxs round_layers \<or>
     generic_fri_sampled_next_value_conflict roots challenges query_idxs
      round_layers \<or>
     generic_fri_sampled_successor_opening_conflict roots challenges
      query_idxs round_layers \<or>
     generic_fri_sampled_final_value_conflict roots challenges final_value
      query_idxs round_layers"
  using assms
  unfolding generic_fri_sampled_assignment_conflict_without_same_layer_def
  by blast

lemma generic_fri_sampled_assignment_conflict_without_same_layerI_base:
  assumes
    "generic_fri_sampled_base_opening_conflict candidate_table roots
      challenges query_idxs round_layers"
  shows
    "generic_fri_sampled_assignment_conflict_without_same_layer
      candidate_table roots challenges final_value query_idxs round_layers"
  using assms
  unfolding generic_fri_sampled_assignment_conflict_without_same_layer_def
  by blast

lemma generic_fri_sampled_assignment_conflict_without_same_layerI_next:
  assumes
    "generic_fri_sampled_next_value_conflict roots challenges query_idxs
      round_layers"
  shows
    "generic_fri_sampled_assignment_conflict_without_same_layer
      candidate_table roots challenges final_value query_idxs round_layers"
  using assms
  unfolding generic_fri_sampled_assignment_conflict_without_same_layer_def
  by blast

lemma generic_fri_sampled_assignment_conflict_without_same_layerI_successor:
  assumes
    "generic_fri_sampled_successor_opening_conflict roots challenges
      query_idxs round_layers"
  shows
    "generic_fri_sampled_assignment_conflict_without_same_layer
      candidate_table roots challenges final_value query_idxs round_layers"
  using assms
  unfolding generic_fri_sampled_assignment_conflict_without_same_layer_def
  by blast

lemma generic_fri_sampled_assignment_conflict_without_same_layerI_final:
  assumes
    "generic_fri_sampled_final_value_conflict roots challenges final_value
      query_idxs round_layers"
  shows
    "generic_fri_sampled_assignment_conflict_without_same_layer
      candidate_table roots challenges final_value query_idxs round_layers"
  using assms
  unfolding generic_fri_sampled_assignment_conflict_without_same_layer_def
  by blast

lemma generic_fri_sampled_assignment_conflict_without_same_layer_iff:
  "generic_fri_sampled_assignment_conflict_without_same_layer
      candidate_table roots challenges final_value query_idxs round_layers
    \<longleftrightarrow>
    generic_fri_sampled_base_opening_conflict candidate_table roots
      challenges query_idxs round_layers \<or>
    generic_fri_sampled_next_value_conflict roots challenges query_idxs
      round_layers \<or>
    generic_fri_sampled_successor_opening_conflict roots challenges
      query_idxs round_layers \<or>
    generic_fri_sampled_final_value_conflict roots challenges final_value
      query_idxs round_layers"
  unfolding generic_fri_sampled_assignment_conflict_without_same_layer_def
  by simp

lemma generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_split:
  assumes
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      candidate_table roots challenges final_value query_idxs round_layers
      final_state"
  shows
    "generic_fri_sampled_assignment_conflict_without_same_layer
      candidate_table roots challenges final_value query_idxs round_layers \<or>
     generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state"
  using assms
  unfolding
    generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_def
    generic_fri_sampled_assignment_conflict_without_same_layer_def
  by blast

lemma generic_fri_sampled_assignment_conflict_with_authenticated_same_layerI_without:
  assumes
    "generic_fri_sampled_assignment_conflict_without_same_layer
      candidate_table roots challenges final_value query_idxs round_layers"
  shows
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      candidate_table roots challenges final_value query_idxs round_layers
      final_state"
  using assms
  unfolding
    generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_def
    generic_fri_sampled_assignment_conflict_without_same_layer_def
  by blast

lemma generic_fri_sampled_assignment_conflict_with_authenticated_same_layerI_same:
  assumes
    "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state"
  shows
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      candidate_table roots challenges final_value query_idxs round_layers
      final_state"
  using assms
  unfolding generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_def
  by blast

lemma generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_iff:
  "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      candidate_table roots challenges final_value query_idxs round_layers
      final_state \<longleftrightarrow>
    generic_fri_sampled_assignment_conflict_without_same_layer
      candidate_table roots challenges final_value query_idxs round_layers \<or>
    generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state"
proof
  assume
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      candidate_table roots challenges final_value query_idxs round_layers
      final_state"
  then show
    "generic_fri_sampled_assignment_conflict_without_same_layer
      candidate_table roots challenges final_value query_idxs round_layers \<or>
    generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state"
    by (rule generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_split)
next
  assume
    "generic_fri_sampled_assignment_conflict_without_same_layer
      candidate_table roots challenges final_value query_idxs round_layers \<or>
    generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state"
  then show
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      candidate_table roots challenges final_value query_idxs round_layers
      final_state"
    by (elim disjE)
      (rule generic_fri_sampled_assignment_conflict_with_authenticated_same_layerI_without,
        assumption,
       rule generic_fri_sampled_assignment_conflict_with_authenticated_same_layerI_same,
        assumption)
qed

lemma generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_imp_sampled:
  assumes
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      candidate_table roots challenges final_value query_idxs round_layers
      final_state"
  shows
    "generic_fri_sampled_assignment_conflict candidate_table roots challenges
      final_value query_idxs round_layers"
  using assms
    generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_imp_sampled
  unfolding
    generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_def
    generic_fri_sampled_assignment_conflict_def
  by blast

lemma generic_fri_sampled_assignment_conflict_imp_authenticated_or_same_layer_auth_gap:
  assumes
    "generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
  shows
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      candidate_table roots challenges final_value query_idxs round_layers
      final_state \<or>
     (generic_fri_sampled_same_layer_opening_conflict roots challenges
        query_idxs round_layers \<and>
      \<not> generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        roots challenges query_idxs round_layers final_state)"
  using assms
  unfolding generic_fri_sampled_assignment_conflict_def
    generic_fri_sampled_assignment_conflict_with_authenticated_same_layer_def
    generic_fri_sampled_assignment_conflict_without_same_layer_def
  by blast

lemma generic_fri_authenticated_same_layer_branch_imp_partial_merkle:
  assumes
    "generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
      roots challenges query_idxs round_layers final_state"
    and "length challenges = length roots"
  shows "partial_merkle_inconsistency_bad s (Some (result, final_state))"
  by (rule
      generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks_imp_partial_merkle
      [OF assms])

lemma generic_fri_sampled_same_layer_opening_conflict_imp_authenticated_if_recorded:
  assumes conflict:
    "generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
    and len_challenges: "length challenges = length roots"
    and recorded:
      "\<And>round_idx layer_idx.
        round_idx < length query_idxs \<Longrightarrow>
        layer_idx < length roots \<Longrightarrow>
        generic_fri_recorded_layer_chunk_authenticated roots query_idxs
          round_layers final_state round_idx layer_idx"
  shows
    "generic_fri_authenticated_same_layer_opening_conflict roots query_idxs
      final_state"
proof -
  from conflict obtain round_idx round_idx' layer_idx
      xp xp_path xn xn_path yp yp_path yn yn_path where
    round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound_ch: "layer_idx < length challenges"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx)"
    and step':
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
        yp yp_path yn yn_path
        (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx'
          layer_idx yp yn)
        (round_layers ! round_idx' ! layer_idx)"
    and cases:
      "(fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xp \<noteq> yp) \<or>
       (fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xp \<noteq> yn) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xn \<noteq> yp) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xn \<noteq> yn)"
    unfolding generic_fri_sampled_same_layer_opening_conflict_def
      fri_evidence_layer_len_def fri_evidence_layer_idx_def
      fri_evidence_next_idx_def fri_evidence_next_value_def
    by blast
  have layer_bound: "layer_idx < length roots"
    using layer_bound_ch len_challenges by simp
  have chunk:
    "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
      xp xp_path xn xn_path (round_layers ! round_idx ! layer_idx)"
    using fri_layer_step_evidenceD(4)[OF step] .
  have chunk':
    "fri_layer_opening_chunk (fri_evidence_layer_len roots layer_idx)
      yp yp_path yn yn_path (round_layers ! round_idx' ! layer_idx)"
    using fri_layer_step_evidenceD(4)[OF step'] .
  have auth:
    "fri_layer_chunk_authenticated (roots ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (round_layers ! round_idx ! layer_idx) final_state"
    using recorded[OF round_bound layer_bound]
    unfolding generic_fri_recorded_layer_chunk_authenticated_def .
  have auth':
    "fri_layer_chunk_authenticated (roots ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
      (round_layers ! round_idx' ! layer_idx) final_state"
    using recorded[OF round_bound' layer_bound]
    unfolding generic_fri_recorded_layer_chunk_authenticated_def .
  from cases show ?thesis
  proof
    assume c:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xp \<noteq> yp"
    show ?thesis
      by (rule generic_fri_authenticated_same_layer_opening_conflictI_base_base
          [OF round_bound round_bound' layer_bound auth auth' chunk chunk'])
        (use c in simp_all)
  next
    assume rest:
      "(fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xp \<noteq> yn) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xn \<noteq> yp) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xn \<noteq> yn)"
    then show ?thesis
    proof
      assume c:
        "fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xp \<noteq> yn"
      show ?thesis
        by (rule generic_fri_authenticated_same_layer_opening_conflictI_base_sibling
            [OF round_bound round_bound' layer_bound auth auth' chunk chunk'])
          (use c in simp_all)
    next
      assume rest':
        "(fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xn \<noteq> yp) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xn \<noteq> yn)"
      then show ?thesis
      proof
        assume c:
          "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
            fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
          xn \<noteq> yp"
        show ?thesis
          by (rule generic_fri_authenticated_same_layer_opening_conflictI_sibling_base
              [OF round_bound round_bound' layer_bound auth auth' chunk chunk'])
            (use c in simp_all)
      next
        assume c:
          "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
            fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
          xn \<noteq> yn"
        show ?thesis
          by (rule generic_fri_authenticated_same_layer_opening_conflictI_sibling_sibling
              [OF round_bound round_bound' layer_bound auth auth' chunk chunk'])
            (use c in simp_all)
      qed
    qed
  qed
qed

lemma accepted_fri_opening_transcript_trace_step_with_authenticated_chunk_at:
  assumes fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and round_bound: "i < rounds"
    and layer_bound: "j < length trace_roots"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length trace_roots) (clength * scale) ! j \<and>
        fri_layer_indices (length trace_roots) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length trace_roots) (clength * scale) ! j"
  shows
    "generic_fri_transcript_step_with_authenticated_chunk trace_roots
      trace_bs query_idxs trace_round_layers final_state i j"
proof -
  have step:
    "fri_round_layer_evidence trace_roots trace_bs query_idxs i j
      trace_round_layers"
    by (rule accepted_fri_opening_transcript_trace_round_layer_evidence
        [OF fri_openings round_bound layer_bound])
  from accepted_fri_opening_transcript_trace_selected_chunk_authenticated_at
      [OF fri_openings out_eq round_bound layer_bound raw_layer]
  obtain auth_chunk where auth:
    "fri_layer_chunk_authenticated (trace_roots ! j)
      (fri_layer_lengths (length trace_roots) (clength * scale) ! j)
      (fri_layer_indices (length trace_roots) (query_idxs ! i)
        (clength * scale) ! j)
      auth_chunk final_state"
    by blast
  have auth_compact:
    "fri_layer_chunk_authenticated (trace_roots ! j)
      (fri_evidence_layer_len trace_roots j)
      (fri_evidence_layer_idx trace_roots query_idxs i j)
      auth_chunk final_state"
    using auth
    unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
    by simp
  show ?thesis
    by (rule generic_fri_transcript_step_with_authenticated_chunkI
        [OF step auth_compact])
qed

lemma accepted_fri_opening_transcript_composition_step_with_authenticated_chunk_at:
  assumes fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and round_bound: "i < rounds"
    and layer_bound: "j < length composition_roots"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length composition_roots) (clength * scale) ! j \<and>
        fri_layer_indices (length composition_roots) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length composition_roots) (clength * scale) ! j"
  shows
    "generic_fri_transcript_step_with_authenticated_chunk composition_roots
      composition_bs query_idxs composition_round_layers final_state i j"
proof -
  have step:
    "fri_round_layer_evidence composition_roots composition_bs query_idxs i j
      composition_round_layers"
    by (rule accepted_fri_opening_transcript_composition_round_layer_evidence
        [OF fri_openings round_bound layer_bound])
  from
    accepted_fri_opening_transcript_composition_selected_chunk_authenticated_at
      [OF fri_openings out_eq round_bound layer_bound raw_layer]
  obtain auth_chunk where auth:
    "fri_layer_chunk_authenticated (composition_roots ! j)
      (fri_layer_lengths (length composition_roots) (clength * scale) ! j)
      (fri_layer_indices (length composition_roots) (query_idxs ! i)
        (clength * scale) ! j)
      auth_chunk final_state"
    by blast
  have auth_compact:
    "fri_layer_chunk_authenticated (composition_roots ! j)
      (fri_evidence_layer_len composition_roots j)
      (fri_evidence_layer_idx composition_roots query_idxs i j)
      auth_chunk final_state"
    using auth
    unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
    by simp
  show ?thesis
    by (rule generic_fri_transcript_step_with_authenticated_chunkI
        [OF step auth_compact])
qed

end

end
