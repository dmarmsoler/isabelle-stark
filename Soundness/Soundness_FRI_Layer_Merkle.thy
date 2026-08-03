(*  Title:      Stark/Soundness_FRI_Layer_Merkle.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Layer_Merkle
  imports Soundness_FRI_Header_Tied_Reduction
begin

text \<open>
  Authenticated-opening facts for sampled FRI layer chunks.

  The sampled-assignment conflict predicates are stated over transcript chunks.
  This layer connects those chunks back to the Merkle checks performed by the
  verifier.  It is intentionally local: it extracts only sampled openings from
  the verifier execution and does not reconstruct complete FRI tables.
\<close>

context soundness
begin

definition fri_layer_chunk_authenticated
  :: "'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "fri_layer_chunk_authenticated rt len idx chunk s \<longleftrightarrow>
    (\<exists>xp xp_path xn xn_path.
      fri_layer_opening_chunk len xp xp_path xn xn_path chunk \<and>
      authenticated_opening_in s
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path\<rparr> \<and>
      authenticated_opening_in s
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = xn,
         opening_path = xn_path\<rparr>)"

definition fri_mfold_chunks_authenticated
  :: "('f \<times> 'f) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f list list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "fri_mfold_chunks_authenticated bfs len idx chunks s \<longleftrightarrow>
    length chunks = length bfs \<and>
    (\<forall>j < length bfs.
      fri_layer_chunk_authenticated (snd (bfs ! j))
        (fri_layer_lengths (length bfs) len ! j)
        (fri_layer_indices (length bfs) idx len ! j)
        (chunks ! j) s)"

lemma fri_layers_transcript_nth_length:
  assumes layers: "fri_layers_transcript n len layer_chunks chunk"
    and j_bound: "j < n"
  shows
    "length (layer_chunks ! j) =
      2 + 2 * floor_log (fri_layer_lengths n len ! j)"
proof -
  from fri_layers_transcript_nth_opening[OF layers j_bound]
  obtain xp xp_path xn xn_path where
    layer_open:
      "fri_layer_opening_chunk (fri_layer_lengths n len ! j)
        xp xp_path xn xn_path (layer_chunks ! j)"
    by blast
  show ?thesis
    using fri_layer_opening_chunk_length[OF layer_open] .
qed

lemma fri_layers_transcript_unique:
  assumes left: "fri_layers_transcript n len layer_chunks chunk"
    and right: "fri_layers_transcript n len layer_chunks' chunk"
  shows "layer_chunks = layer_chunks'"
proof -
  have len_left: "length layer_chunks = n"
    using left unfolding fri_layers_transcript_def by simp
  have len_right: "length layer_chunks' = n"
    using right unfolding fri_layers_transcript_def by simp
  have concat_eq:
    "List.concat layer_chunks @ [] = List.concat layer_chunks'"
    using left right unfolding fri_layers_transcript_def by simp
  have same_lens:
    "\<And>j. j < length layer_chunks \<Longrightarrow>
      length (layer_chunks ! j) = length (layer_chunks' ! j)"
    using fri_layers_transcript_nth_length[OF left]
      fri_layers_transcript_nth_length[OF right]
      len_left len_right
    by simp
  have "layer_chunks = layer_chunks' \<and> ([] :: 'f list) = []"
    by (rule concat_append_eq_concat_same_chunk_lengths
        [OF _ same_lens concat_eq])
      (use len_left len_right in simp)
  then show ?thesis
    by simp
qed

lemma query_round_fri_layer_transcripts_unique:
  assumes left:
      "query_round_fri_layer_transcripts idx trace_roots composition_roots
        chunk trace_layers composition_layers"
    and right:
      "query_round_fri_layer_transcripts idx trace_roots composition_roots
        chunk trace_layers' composition_layers'"
  shows "trace_layers = trace_layers'"
    and "composition_layers = composition_layers'"
proof -
  from left obtain query_chunk trace_fri_chunk composition_fri_chunk
      leaves paths where
    chunk_left:
      "chunk = query_chunk @ trace_fri_chunk @ composition_fri_chunk"
    and query_left:
      "query_decommitment_transcript idx leaves paths query_chunk"
    and trace_left:
      "fri_layers_transcript (length trace_roots) (clength * scale)
        trace_layers trace_fri_chunk"
    and composition_left:
      "fri_layers_transcript (length composition_roots) (clength * scale)
        composition_layers composition_fri_chunk"
    unfolding query_round_fri_layer_transcripts_def by blast
  from right obtain query_chunk' trace_fri_chunk' composition_fri_chunk'
      leaves' paths' where
    chunk_right:
      "chunk = query_chunk' @ trace_fri_chunk' @ composition_fri_chunk'"
    and query_right:
      "query_decommitment_transcript idx leaves' paths' query_chunk'"
    and trace_right:
      "fri_layers_transcript (length trace_roots) (clength * scale)
        trace_layers' trace_fri_chunk'"
    and composition_right:
      "fri_layers_transcript (length composition_roots) (clength * scale)
        composition_layers' composition_fri_chunk'"
    unfolding query_round_fri_layer_transcripts_def by blast
  have len_query:
    "length query_chunk = length query_chunk'"
    using query_decommitment_transcript_length[OF query_left]
      query_decommitment_transcript_length[OF query_right]
    by simp
  have len_trace:
    "length trace_fri_chunk = length trace_fri_chunk'"
    using fri_layers_transcript_length[OF trace_left]
      fri_layers_transcript_length[OF trace_right]
    by simp
  have trace_chunk_eq: "trace_fri_chunk = trace_fri_chunk'"
  proof -
    have left_drop:
      "drop (length query_chunk) chunk =
        trace_fri_chunk @ composition_fri_chunk"
      using chunk_left by simp
    have right_drop:
      "drop (length query_chunk) chunk =
        trace_fri_chunk' @ composition_fri_chunk'"
      using chunk_right len_query by simp
    have left_take:
      "trace_fri_chunk =
        take (length trace_fri_chunk) (drop (length query_chunk) chunk)"
      using left_drop by simp
    have right_take:
      "trace_fri_chunk' =
        take (length trace_fri_chunk') (drop (length query_chunk) chunk)"
      using right_drop by simp
    show ?thesis
      using left_take right_take len_trace by simp
  qed
  have composition_chunk_eq:
    "composition_fri_chunk = composition_fri_chunk'"
  proof -
    have left_drop:
      "drop (length query_chunk + length trace_fri_chunk) chunk =
        composition_fri_chunk"
      using chunk_left by simp
    have right_drop:
      "drop (length query_chunk + length trace_fri_chunk) chunk =
        composition_fri_chunk'"
      using chunk_right len_query len_trace by simp
    show ?thesis
      using left_drop right_drop by simp
  qed
  have trace_right':
    "fri_layers_transcript (length trace_roots) (clength * scale)
      trace_layers' trace_fri_chunk"
    using trace_right trace_chunk_eq by simp
  have composition_right':
    "fri_layers_transcript (length composition_roots) (clength * scale)
      composition_layers' composition_fri_chunk"
    using composition_right composition_chunk_eq by simp
  show "trace_layers = trace_layers'"
    by (rule fri_layers_transcript_unique[OF trace_left trace_right'])
  show "composition_layers = composition_layers'"
    by (rule fri_layers_transcript_unique
        [OF composition_left composition_right'])
qed

lemma fri_layer_chunk_authenticatedI:
  assumes "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and "authenticated_opening_in s
      \<lparr>opening_root = rt,
       opening_length = len,
       opening_index = idx,
       opening_value = xp,
       opening_path = xp_path\<rparr>"
    and "authenticated_opening_in s
      \<lparr>opening_root = rt,
       opening_length = len,
       opening_index = fri_sibling_index len idx,
       opening_value = xn,
       opening_path = xn_path\<rparr>"
  shows "fri_layer_chunk_authenticated rt len idx chunk s"
  using assms unfolding fri_layer_chunk_authenticated_def by blast

lemma fri_layer_chunk_authenticatedE:
  assumes "fri_layer_chunk_authenticated rt len idx chunk s"
  obtains xp xp_path xn xn_path where
    "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    "authenticated_opening_in s
      \<lparr>opening_root = rt,
       opening_length = len,
       opening_index = idx,
       opening_value = xp,
       opening_path = xp_path\<rparr>"
    "authenticated_opening_in s
      \<lparr>opening_root = rt,
       opening_length = len,
       opening_index = fri_sibling_index len idx,
       opening_value = xn,
       opening_path = xn_path\<rparr>"
  using assms unfolding fri_layer_chunk_authenticated_def by blast

lemma fri_layer_chunk_authenticated_matching_values:
  assumes auth: "fri_layer_chunk_authenticated rt len idx chunk s"
    and chunk:
      "fri_layer_opening_chunk len yp yp_path yn yn_path chunk"
  obtains xp_path xn_path where
    "fri_layer_opening_chunk len yp xp_path yn xn_path chunk"
    "authenticated_opening_in s
      \<lparr>opening_root = rt,
       opening_length = len,
       opening_index = idx,
       opening_value = yp,
       opening_path = xp_path\<rparr>"
    "authenticated_opening_in s
      \<lparr>opening_root = rt,
       opening_length = len,
       opening_index = fri_sibling_index len idx,
       opening_value = yn,
       opening_path = xn_path\<rparr>"
proof -
  from auth obtain xp xp_path xn xn_path where
    chunk': "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and xp_auth:
      "authenticated_opening_in s
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path\<rparr>"
    and xn_auth:
      "authenticated_opening_in s
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = xn,
         opening_path = xn_path\<rparr>"
    by (rule fri_layer_chunk_authenticatedE)
  have xp_eq: "xp = yp"
    by (rule fri_layer_opening_chunk_values_unique(1)[OF chunk' chunk])
  have xn_eq: "xn = yn"
    by (rule fri_layer_opening_chunk_values_unique(2)[OF chunk' chunk])
  have chunk_y:
    "fri_layer_opening_chunk len yp xp_path yn xn_path chunk"
    using chunk' xp_eq xn_eq by simp
  show ?thesis
    by (rule that[OF chunk_y])
      (use xp_auth xn_auth xp_eq xn_eq in simp_all)
qed

lemma authenticated_openings_values_eq_if_no_partial_merkle:
  assumes no_bad:
      "\<not> partial_merkle_inconsistency_bad s
        (Some (result, final_state))"
    and first: "authenticated_opening_in final_state opn"
    and second: "authenticated_opening_in final_state opn'"
    and same_root: "opening_root opn = opening_root opn'"
    and same_length: "opening_length opn = opening_length opn'"
    and same_index: "opening_index opn = opening_index opn'"
  shows "opening_value opn = opening_value opn'"
proof (rule ccontr)
  assume neq: "opening_value opn \<noteq> opening_value opn'"
  have "partial_merkle_inconsistency_bad s
      (Some (result, final_state))"
    unfolding partial_merkle_inconsistency_bad_def accepted_def
    by (intro conjI exI[of _ result] exI[of _ final_state]
        exI[of _ opn] exI[of _ opn'])
      (use first second same_root same_length same_index neq in simp_all)
  then show False using no_bad by contradiction
qed

lemma fri_layer_authenticated_base_values_eq_if_no_partial_merkle:
  assumes no_bad:
      "\<not> partial_merkle_inconsistency_bad s
        (Some (result, final_state))"
    and auth:
      "fri_layer_chunk_authenticated rt len idx chunk final_state"
    and auth':
      "fri_layer_chunk_authenticated rt len idx chunk' final_state"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and chunk':
      "fri_layer_opening_chunk len yp yp_path yn yn_path chunk'"
  shows "xp = yp"
proof (rule ccontr)
  assume neq: "xp \<noteq> yp"
  from fri_layer_chunk_authenticated_matching_values[OF auth chunk]
  obtain xp_path' xn_path' where
    xp_auth:
      "authenticated_opening_in final_state
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path'\<rparr>"
    by blast
  from fri_layer_chunk_authenticated_matching_values[OF auth' chunk']
  obtain yp_path' yn_path' where
    yp_auth:
      "authenticated_opening_in final_state
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = yp,
         opening_path = yp_path'\<rparr>"
    by blast
  have "partial_merkle_inconsistency_bad s
      (Some (result, final_state))"
    unfolding partial_merkle_inconsistency_bad_def accepted_def
    by (intro conjI exI[of _ result] exI[of _ final_state]
        exI[of _ "\<lparr>opening_root = rt,
          opening_length = len,
          opening_index = idx,
          opening_value = xp,
          opening_path = xp_path'\<rparr>"]
        exI[of _ "\<lparr>opening_root = rt,
          opening_length = len,
          opening_index = idx,
          opening_value = yp,
          opening_path = yp_path'\<rparr>"])
      (use xp_auth yp_auth neq in simp_all)
  then show False using no_bad by contradiction
qed

lemma fri_layer_authenticated_sibling_values_eq_if_no_partial_merkle:
  assumes no_bad:
      "\<not> partial_merkle_inconsistency_bad s
        (Some (result, final_state))"
    and auth:
      "fri_layer_chunk_authenticated rt len idx chunk final_state"
    and auth':
      "fri_layer_chunk_authenticated rt len idx chunk' final_state"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and chunk':
      "fri_layer_opening_chunk len yp yp_path yn yn_path chunk'"
  shows "xn = yn"
proof (rule ccontr)
  assume neq: "xn \<noteq> yn"
  from fri_layer_chunk_authenticated_matching_values[OF auth chunk]
  obtain xp_path' xn_path' where
    xn_auth:
      "authenticated_opening_in final_state
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = xn,
         opening_path = xn_path'\<rparr>"
    by blast
  from fri_layer_chunk_authenticated_matching_values[OF auth' chunk']
  obtain yp_path' yn_path' where
    yn_auth:
      "authenticated_opening_in final_state
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = yn,
         opening_path = yn_path'\<rparr>"
    by blast
  have "partial_merkle_inconsistency_bad s
      (Some (result, final_state))"
    unfolding partial_merkle_inconsistency_bad_def accepted_def
    by (intro conjI exI[of _ result] exI[of _ final_state]
        exI[of _ "\<lparr>opening_root = rt,
          opening_length = len,
          opening_index = fri_sibling_index len idx,
          opening_value = xn,
          opening_path = xn_path'\<rparr>"]
        exI[of _ "\<lparr>opening_root = rt,
          opening_length = len,
          opening_index = fri_sibling_index len idx,
          opening_value = yn,
          opening_path = yn_path'\<rparr>"])
      (use xn_auth yn_auth neq in simp_all)
  then show False using no_bad by contradiction
qed

lemma fri_layer_authenticated_base_sibling_values_eq_if_no_partial_merkle:
  assumes no_bad:
      "\<not> partial_merkle_inconsistency_bad s
        (Some (result, final_state))"
    and auth:
      "fri_layer_chunk_authenticated rt len idx chunk final_state"
    and auth':
      "fri_layer_chunk_authenticated rt len idx' chunk' final_state"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and chunk':
      "fri_layer_opening_chunk len yp yp_path yn yn_path chunk'"
    and same_index: "idx = fri_sibling_index len idx'"
  shows "xp = yn"
proof -
  from fri_layer_chunk_authenticated_matching_values[OF auth chunk]
  obtain xp_path' xn_path' where
    xp_auth:
      "authenticated_opening_in final_state
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path'\<rparr>"
    by blast
  from fri_layer_chunk_authenticated_matching_values[OF auth' chunk']
  obtain yp_path' yn_path' where
    yn_auth:
      "authenticated_opening_in final_state
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx',
         opening_value = yn,
         opening_path = yn_path'\<rparr>"
    by blast
  show ?thesis
    using authenticated_openings_values_eq_if_no_partial_merkle
      [OF no_bad xp_auth yn_auth] same_index
    by simp
qed

lemma fri_layer_authenticated_sibling_base_values_eq_if_no_partial_merkle:
  assumes no_bad:
      "\<not> partial_merkle_inconsistency_bad s
        (Some (result, final_state))"
    and auth:
      "fri_layer_chunk_authenticated rt len idx chunk final_state"
    and auth':
      "fri_layer_chunk_authenticated rt len idx' chunk' final_state"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and chunk':
      "fri_layer_opening_chunk len yp yp_path yn yn_path chunk'"
    and same_index: "fri_sibling_index len idx = idx'"
  shows "xn = yp"
proof -
  from fri_layer_chunk_authenticated_matching_values[OF auth chunk]
  obtain xp_path' xn_path' where
    xn_auth:
      "authenticated_opening_in final_state
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = xn,
         opening_path = xn_path'\<rparr>"
    by blast
  from fri_layer_chunk_authenticated_matching_values[OF auth' chunk']
  obtain yp_path' yn_path' where
    yp_auth:
      "authenticated_opening_in final_state
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx',
         opening_value = yp,
         opening_path = yp_path'\<rparr>"
    by blast
  show ?thesis
    using authenticated_openings_values_eq_if_no_partial_merkle
      [OF no_bad xn_auth yp_auth] same_index
    by simp
qed

lemma fri_layer_authenticated_sibling_sibling_values_eq_if_no_partial_merkle:
  assumes no_bad:
      "\<not> partial_merkle_inconsistency_bad s
        (Some (result, final_state))"
    and auth:
      "fri_layer_chunk_authenticated rt len idx chunk final_state"
    and auth':
      "fri_layer_chunk_authenticated rt len idx' chunk' final_state"
    and chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and chunk':
      "fri_layer_opening_chunk len yp yp_path yn yn_path chunk'"
    and same_index:
      "fri_sibling_index len idx = fri_sibling_index len idx'"
  shows "xn = yn"
proof -
  from fri_layer_chunk_authenticated_matching_values[OF auth chunk]
  obtain xp_path' xn_path' where
    xn_auth:
      "authenticated_opening_in final_state
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = xn,
         opening_path = xn_path'\<rparr>"
    by blast
  from fri_layer_chunk_authenticated_matching_values[OF auth' chunk']
  obtain yp_path' yn_path' where
    yn_auth:
      "authenticated_opening_in final_state
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx',
         opening_value = yn,
         opening_path = yn_path'\<rparr>"
    by blast
  show ?thesis
    using authenticated_openings_values_eq_if_no_partial_merkle
      [OF no_bad xn_auth yn_auth] same_index
    by simp
qed

lemma fri_layer_chunk_authenticated_mono:
  assumes auth: "fri_layer_chunk_authenticated rt len idx chunk s"
    and ext: "s \<le> t"
  shows "fri_layer_chunk_authenticated rt len idx chunk t"
  using auth
  unfolding fri_layer_chunk_authenticated_def
  by (meson authenticated_opening_in_mono ext)

lemma fri_mfold_chunks_authenticated_mono:
  assumes auth: "fri_mfold_chunks_authenticated bfs len idx chunks s"
    and ext: "s \<le> t"
  shows "fri_mfold_chunks_authenticated bfs len idx chunks t"
  using auth
  unfolding fri_mfold_chunks_authenticated_def
  by (meson fri_layer_chunk_authenticated_mono ext)

lemma fri_layer_opening_step_authenticated_chunk:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes len_pos: "0 < len"
    and idx_bound: "idx < len"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
  obtains xp xp_path xn xn_path where
    "fri_layer_opening_chunk len xp xp_path xn xn_path
      ([xp] @ xp_path @ [xn] @ xn_path)"
    "authenticated_opening_in t
      \<lparr>opening_root = rt,
       opening_length = len,
       opening_index = idx,
       opening_value = xp,
       opening_path = xp_path\<rparr>"
    "authenticated_opening_in t
      \<lparr>opening_root = rt,
       opening_length = len,
       opening_index = fri_sibling_index len idx,
       opening_value = xn,
       opening_path = xn_path\<rparr>"
proof -
  from outcome[unfolded fri_layer_opening_step_unfold_finish]
  obtain xp s1 xp_path s2 xn s3 xn_path s4 where
    read_xp: "Some (xp, s1) \<in> set_dist (execute read s)"
    and read_xp_path:
      "Some (xp_path, s2) \<in>
        set_dist (execute (ntimes read (floor_log len)) s1)"
    and read_xn: "Some (xn, s3) \<in> set_dist (execute read s2)"
    and read_xn_path:
      "Some (xn_path, s4) \<in>
        set_dist (execute (ntimes read (floor_log len)) s3)"
    and finish:
      "Some (out, t) \<in>
        set_dist
          (execute
            (fri_layer_opening_finish b rt idx x len pw
              xp xp_path xn xn_path) s4)"
    by (auto elim!: set_dist_bindE)
  have xp_path_length: "length xp_path = floor_log len"
    using ntimes_read_any_outcome[OF read_xp_path] by simp
  have xn_path_length: "length xn_path = floor_log len"
    using ntimes_read_any_outcome[OF read_xn_path] by simp
  have sibling_bound: "(idx + len div 2) mod len < len"
    using len_pos by simp
  from fri_layer_opening_finish_authenticated_openings
      [OF idx_bound sibling_bound xp_path_length xn_path_length finish]
  have xp_auth:
      "authenticated_opening_in t
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path\<rparr>"
    and xn_auth:
      "authenticated_opening_in t
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = xn,
         opening_path = xn_path\<rparr>"
    unfolding fri_sibling_index_def
    by blast+
  have chunk:
    "fri_layer_opening_chunk len xp xp_path xn xn_path
      ([xp] @ xp_path @ [xn] @ xn_path)"
    using xp_path_length xn_path_length
    unfolding fri_layer_opening_chunk_def by simp
  show ?thesis
    by (rule that[OF chunk xp_auth xn_auth])
qed

lemma fri_layer_opening_step_authenticated_chunk_pred:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes len_pos: "0 < len"
    and idx_bound: "idx < len"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
  obtains chunk where "fri_layer_chunk_authenticated rt len idx chunk t"
proof -
  from fri_layer_opening_step_authenticated_chunk
      [OF len_pos idx_bound outcome]
  obtain xp xp_path xn xn_path where
    chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path
        ([xp] @ xp_path @ [xn] @ xn_path)"
    and xp_auth:
      "authenticated_opening_in t
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path\<rparr>"
    and xn_auth:
      "authenticated_opening_in t
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = xn,
         opening_path = xn_path\<rparr>"
    by blast
  have "fri_layer_chunk_authenticated rt len idx
      ([xp] @ xp_path @ [xn] @ xn_path) t"
    by (rule fri_layer_chunk_authenticatedI[OF chunk xp_auth xn_auth])
  then show ?thesis
    by (rule that)
qed

lemma fri_layer_opening_step_outcome_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes len_pos: "0 < len"
    and idx_bound: "idx < len"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
  obtains xp xp_path xn xn_path x' chunk where
    "out = (idx mod (len div 2), x', len div 2, pw + pw)"
    "xp = x"
    "x' = fri_fold_value b xp xn
      (fri_fold_denominator ((h ^ idx) * shift) pw)"
    "chunk = [xp] @ xp_path @ [xn] @ xn_path"
    "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    "PTranscript s = chunk @ PTranscript t"
    "PState t = foldl concat (PState s) chunk"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
    "authenticated_opening_in t
      \<lparr>opening_root = rt,
       opening_length = len,
       opening_index = idx,
       opening_value = xp,
       opening_path = xp_path\<rparr>"
    "authenticated_opening_in t
      \<lparr>opening_root = rt,
       opening_length = len,
       opening_index = fri_sibling_index len idx,
       opening_value = xn,
       opening_path = xn_path\<rparr>"
proof -
  from outcome obtain xp s1 xp_path s2 xn s3 xn_path s4 s5 ap1 s6 s7
      ap2 s8 s9 where
    read_xp: "Some (xp, s1) \<in> set_dist (execute read s)"
    and read_xp_path:
      "Some (xp_path, s2) \<in>
        set_dist (execute (ntimes read (floor_log len)) s1)"
    and read_xn: "Some (xn, s3) \<in> set_dist (execute read s2)"
    and read_xn_path:
      "Some (xn_path, s4) \<in>
        set_dist (execute (ntimes read (floor_log len)) s3)"
    and assert_xp: "Some ((), s5) \<in> set_dist (execute (assert (xp = x)) s4)"
    and check1:
      "Some (ap1, s6) \<in>
        set_dist (execute (check_authentication_path len idx xp xp_path) s5)"
    and assert_ap1:
      "Some ((), s7) \<in> set_dist (execute (assert (ap1 = rt)) s6)"
    and check2:
      "Some (ap2, s8) \<in>
        set_dist (execute
          (check_authentication_path len ((idx + len div 2) mod len) xn
            xn_path) s7)"
    and assert_ap2:
      "Some ((), s9) \<in> set_dist (execute (assert (ap2 = rt)) s8)"
    and ret:
      "Some (out, t) \<in>
        set_dist (execute
          (return
            (idx mod (len div 2),
              (xp + xn) div 2 +
                b * ((xp - xn) div (2 * ((h ^ idx) * shift) ^ pw)),
              len div 2, pw + pw)) s9)"
    unfolding fri_layer_opening_step_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  from read_outcome[OF read_xp] obtain rest1 where
    tr_s: "PTranscript s = xp # rest1"
    and st_s1: "PState s1 = concat (PState s) xp"
    and tr_s1: "PTranscript s1 = rest1"
    and ext_s_s1: "s \<le> s1"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  have xp_path_res:
    "length xp_path = floor_log len \<and>
     PTranscript s1 = xp_path @ PTranscript s2 \<and>
     PState s2 = foldl concat (PState s1) xp_path \<and>
     s1 \<le> s2 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    using ntimes_read_any_outcome[OF read_xp_path] by simp
  from read_outcome[OF read_xn] obtain rest3 where
    tr_s2: "PTranscript s2 = xn # rest3"
    and st_s3: "PState s3 = concat (PState s2) xn"
    and tr_s3: "PTranscript s3 = rest3"
    and ext_s2_s3: "s2 \<le> s3"
    and query_count_s3: "PQueryCounter s3 = PQueryCounter s2"
    by blast
  have xn_path_res:
    "length xn_path = floor_log len \<and>
     PTranscript s3 = xn_path @ PTranscript s4 \<and>
     PState s4 = foldl concat (PState s3) xn_path \<and>
     s3 \<le> s4 \<and>
     PQueryCounter s4 = PQueryCounter s3"
    using ntimes_read_any_outcome[OF read_xn_path] by simp
  have xp_eq: "xp = x"
    using assert_xp unfolding assert_def
    by (cases "xp = x") (auto simp: throw_no_outcome)
  have s5_eq: "s5 = s4"
    using assert_xp xp_eq unfolding assert_def by simp
  have s5_s6: "s5 \<le> s6"
    by (rule check_authentication_path_hash_extends[OF check1])
  have st_s6: "PState s6 = PState s5"
    using check_authentication_path_preserves_channel(1)[OF check1] .
  have tr_s6: "PTranscript s6 = PTranscript s5"
    using check_authentication_path_preserves_channel(2)[OF check1] .
  have query_count_s6: "PQueryCounter s6 = PQueryCounter s5"
    using check_authentication_path_preserves_channel(6)[OF check1] .
  have ap1_eq: "ap1 = rt"
    using assert_ap1 unfolding assert_def
    by (cases "ap1 = rt") (auto simp: throw_no_outcome)
  have s7_eq: "s7 = s6"
    using assert_ap1 ap1_eq unfolding assert_def by simp
  have s7_s8: "s7 \<le> s8"
    by (rule check_authentication_path_hash_extends[OF check2])
  have st_s8: "PState s8 = PState s7"
    using check_authentication_path_preserves_channel(1)[OF check2] .
  have tr_s8: "PTranscript s8 = PTranscript s7"
    using check_authentication_path_preserves_channel(2)[OF check2] .
  have query_count_s8: "PQueryCounter s8 = PQueryCounter s7"
    using check_authentication_path_preserves_channel(6)[OF check2] .
  have ap2_eq: "ap2 = rt"
    using assert_ap2 unfolding assert_def
    by (cases "ap2 = rt") (auto simp: throw_no_outcome)
  have s9_eq: "s9 = s8"
    using assert_ap2 ap2_eq unfolding assert_def by simp
  let ?x' =
    "(xp + xn) div 2 +
      b * ((xp - xn) div (2 * ((h ^ idx) * shift) ^ pw))"
  let ?chunk = "[xp] @ xp_path @ [xn] @ xn_path"
  have out_t:
    "out = (idx mod (len div 2), ?x', len div 2, pw + pw) \<and> t = s9"
    using ret by simp
  have x'_fold:
    "?x' = fri_fold_value b xp xn
      (fri_fold_denominator ((h ^ idx) * shift) pw)"
    unfolding fri_fold_value_def fri_fold_denominator_def by simp
  have chunk_shape:
    "fri_layer_opening_chunk len xp xp_path xn xn_path ?chunk"
    using xp_path_res xn_path_res unfolding fri_layer_opening_chunk_def by simp
  have tr_t: "PTranscript s = ?chunk @ PTranscript t"
    using tr_s tr_s1 xp_path_res tr_s2 tr_s3 xn_path_res s5_eq tr_s6
      s7_eq tr_s8 s9_eq out_t
    by simp
  have st_t: "PState t = foldl concat (PState s) ?chunk"
    using st_s1 xp_path_res st_s3 xn_path_res s5_eq st_s6 s7_eq st_s8
      s9_eq out_t
    by simp
  have s_t: "s \<le> t"
    using ext_s_s1 xp_path_res ext_s2_s3 xn_path_res s5_s6 s7_s8 out_t
    unfolding s5_eq s7_eq s9_eq
    by (meson hash_ext_trans)
  have query_count_t: "PQueryCounter t = PQueryCounter s"
    using out_t query_count_s1
      xp_path_res query_count_s3 xn_path_res query_count_s6 query_count_s8
      s5_eq s7_eq s9_eq
    by simp
  have sibling_bound: "(idx + len div 2) mod len < len"
    using len_pos by simp
  have xp_path_length: "length xp_path = floor_log len"
    using xp_path_res by simp
  have xn_path_length: "length xn_path = floor_log len"
    using xn_path_res by simp
  have s6_t: "s6 \<le> t"
    using s7_s8 out_t unfolding s7_eq s9_eq by simp
  have xp_bound:
    "merkle_path_bound rt len idx xp xp_path t"
  proof -
    have "merkle_path_bound ap1 len idx xp xp_path s6"
      by (rule check_authentication_path_outcome_bound[OF check1])
    then have "merkle_path_bound rt len idx xp xp_path s6"
      unfolding ap1_eq .
    then show ?thesis
      by (rule merkle_path_bound_mono[OF _ s6_t])
  qed
  have xn_bound:
    "merkle_path_bound rt len (fri_sibling_index len idx) xn xn_path t"
  proof -
    have "merkle_path_bound ap2 len ((idx + len div 2) mod len)
        xn xn_path s8"
      by (rule check_authentication_path_outcome_bound[OF check2])
    then show ?thesis
      using ap2_eq out_t unfolding fri_sibling_index_def s9_eq by simp
  qed
  have xp_auth:
    "authenticated_opening_in t
      \<lparr>opening_root = rt, opening_length = len,
       opening_index = idx, opening_value = xp,
       opening_path = xp_path\<rparr>"
    unfolding authenticated_opening_in_def
    using idx_bound xp_path_length xp_bound by simp
  have xn_auth:
    "authenticated_opening_in t
      \<lparr>opening_root = rt, opening_length = len,
       opening_index = fri_sibling_index len idx,
       opening_value = xn, opening_path = xn_path\<rparr>"
    unfolding authenticated_opening_in_def
    using sibling_bound xn_path_length xn_bound
    unfolding fri_sibling_index_def by simp
  show ?thesis
  proof (rule that)
    show "out = (idx mod (len div 2), ?x', len div 2, pw + pw)"
      using out_t by simp
    show "xp = x"
      by (rule xp_eq)
    show "?x' =
      fri_fold_value b xp xn
        (fri_fold_denominator ((h ^ idx) * shift) pw)"
      by (rule x'_fold)
    show "?chunk = [xp] @ xp_path @ [xn] @ xn_path"
      by simp
    show "fri_layer_opening_chunk len xp xp_path xn xn_path ?chunk"
      by (rule chunk_shape)
    show "PTranscript s = ?chunk @ PTranscript t"
      by (rule tr_t)
    show "PState t = foldl concat (PState s) ?chunk"
      by (rule st_t)
    show "s \<le> t"
      by (rule s_t)
    show "PQueryCounter t = PQueryCounter s"
      by (rule query_count_t)
    show "authenticated_opening_in t
      \<lparr>opening_root = rt, opening_length = len,
       opening_index = idx, opening_value = xp,
       opening_path = xp_path\<rparr>"
      by (rule xp_auth)
    show "authenticated_opening_in t
      \<lparr>opening_root = rt, opening_length = len,
       opening_index = fri_sibling_index len idx,
       opening_value = xn, opening_path = xn_path\<rparr>"
      by (rule xn_auth)
  qed
qed

lemma mfold_fri_layer_opening_steps_hash_extends:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (out, t) \<in>
      set_dist
        (execute (mfold (idx, x, len, pw)
          (map fri_layer_opening_step bfs)) s)"
  shows "s \<le> t"
proof -
  from mfold_fri_layer_openings_outcome[OF outcome]
  obtain layer_chunks chunk where
    "s \<le> t"
    by blast
  then show ?thesis .
qed

lemma mfold_fri_layer_opening_steps_authenticated_opening_mono:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes auth: "authenticated_opening_in s opening"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute (mfold (idx, x, len, pw)
            (map fri_layer_opening_step bfs)) s)"
  shows "authenticated_opening_in t opening"
  by (rule authenticated_opening_in_mono
      [OF auth mfold_fri_layer_opening_steps_hash_extends[OF outcome]])

lemma mfold_fri_layer_opening_head_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes len_pos: "0 < len"
    and idx_bound: "idx < len"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw)
              (map fri_layer_opening_step ((b, rt) # bfs))) s)"
  obtains chunk where "fri_layer_chunk_authenticated rt len idx chunk t"
proof -
  from outcome obtain out1 s1 where
    head:
      "Some (out1, s1) \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist (execute (mfold out1 (map fri_layer_opening_step bfs)) s1)"
    by (auto elim!: set_dist_bindE)
  from fri_layer_opening_step_authenticated_chunk_pred
      [OF len_pos idx_bound head]
  obtain chunk where auth_s1:
    "fri_layer_chunk_authenticated rt len idx chunk s1"
    by blast
  obtain idx1 x1 len1 pw1 where out1_eq:
    "out1 = (idx1, x1, len1, pw1)"
    by (cases out1)
  have s1_t: "s1 \<le> t"
    by (rule mfold_fri_layer_opening_steps_hash_extends
        [OF tail[unfolded out1_eq]])
  have "fri_layer_chunk_authenticated rt len idx chunk t"
    by (rule fri_layer_chunk_authenticated_mono[OF auth_s1 s1_t])
  then show ?thesis
    by (rule that)
qed

lemma mfold_fri_layer_opening_selected_chunk_authenticated_at_exists:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw)
              (map fri_layer_opening_step bfs)) s)"
    and j_bound: "j < length bfs"
    and layer_len_pos:
      "0 < fri_layer_lengths (length bfs) len ! j"
    and layer_idx_bound:
      "fri_layer_indices (length bfs) idx len ! j <
        fri_layer_lengths (length bfs) len ! j"
  shows "\<exists>chunk.
    fri_layer_chunk_authenticated (snd (bfs ! j))
      (fri_layer_lengths (length bfs) len ! j)
      (fri_layer_indices (length bfs) idx len ! j)
      chunk t"
  using outcome j_bound layer_len_pos layer_idx_bound
proof (induction bfs arbitrary: idx x len pw s out t j)
  case Nil
  then show ?case by simp
next
  case (Cons bf bfs)
  obtain b rt where bf_eq: "bf = (b, rt)"
    by (cases bf)
  from Cons.prems(1)[unfolded bf_eq]
  obtain idx1 x1 len1 pw1 s1 where
    head:
      "Some ((idx1, x1, len1, pw1), s1) \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx1, x1, len1, pw1)
              (map fri_layer_opening_step bfs)) s1)"
    by (auto elim!: set_dist_bindE)
  show ?case
  proof (cases j)
    case 0
    have len_pos: "0 < len"
      using Cons.prems(3) 0 by simp
    have idx_bound: "idx < len"
      using Cons.prems(4) 0 by simp
    from fri_layer_opening_step_authenticated_chunk_pred
        [OF len_pos idx_bound head]
    obtain chunk where auth_s1:
      "fri_layer_chunk_authenticated rt len idx chunk s1"
      by blast
    have s1_t: "s1 \<le> t"
      by (rule mfold_fri_layer_opening_steps_hash_extends
          [OF tail])
    have auth_t:
      "fri_layer_chunk_authenticated rt len idx chunk t"
      by (rule fri_layer_chunk_authenticated_mono[OF auth_s1 s1_t])
    show ?thesis
      using auth_t 0 bf_eq by auto
  next
    case (Suc k)
    from fri_layer_opening_step_outcome[OF head]
    obtain xp xp_path xn xn_path x' where out1_eq:
      "(idx1, x1, len1, pw1) =
        (idx mod (len div 2), x', len div 2, pw + pw)"
      by blast
    have k_bound: "k < length bfs"
      using Cons.prems(2) Suc by simp
    have tail_len_pos:
      "0 < fri_layer_lengths (length bfs) (len div 2) ! k"
      using Cons.prems(3) Suc by simp
    have tail_idx_bound:
      "fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! k <
        fri_layer_lengths (length bfs) (len div 2) ! k"
      using Cons.prems(4) Suc by simp
    show ?thesis
      using Cons.IH[OF tail[unfolded out1_eq] k_bound
            tail_len_pos tail_idx_bound] Suc
      by auto
  qed
qed

lemma mfold_fri_layer_opening_selected_chunk_authenticated_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw)
              (map fri_layer_opening_step bfs)) s)"
    and j_bound: "j < length bfs"
    and layer_len_pos:
      "0 < fri_layer_lengths (length bfs) len ! j"
    and layer_idx_bound:
      "fri_layer_indices (length bfs) idx len ! j <
        fri_layer_lengths (length bfs) len ! j"
  obtains chunk where
    "fri_layer_chunk_authenticated (snd (bfs ! j))
      (fri_layer_lengths (length bfs) len ! j)
      (fri_layer_indices (length bfs) idx len ! j)
      chunk t"
  using mfold_fri_layer_opening_selected_chunk_authenticated_at_exists
    [OF outcome j_bound layer_len_pos layer_idx_bound]
  by blast

lemma receive_query_commits_selected_chunk_authenticated_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw) (receive_query_commits bfs)) s)"
    and j_bound: "j < length bfs"
    and layer_len_pos:
      "0 < fri_layer_lengths (length bfs) len ! j"
    and layer_idx_bound:
      "fri_layer_indices (length bfs) idx len ! j <
        fri_layer_lengths (length bfs) len ! j"
  obtains chunk where
    "fri_layer_chunk_authenticated (snd (bfs ! j))
      (fri_layer_lengths (length bfs) len ! j)
      (fri_layer_indices (length bfs) idx len ! j)
      chunk t"
proof -
  have map_eq: "receive_query_commits bfs = map fri_layer_opening_step bfs"
    unfolding receive_query_commits_def fri_layer_opening_step_def
    by (simp add: fun_eq_iff split: prod.splits)
  show ?thesis
    by (rule mfold_fri_layer_opening_selected_chunk_authenticated_at
        [OF outcome[unfolded map_eq] j_bound layer_len_pos
          layer_idx_bound that])
qed

lemma receive_query_commits_mfold_hash_extends:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (out, t) \<in>
      set_dist
        (execute (mfold (idx, x, len, pw)
          (receive_query_commits bfs)) s)"
  shows "s \<le> t"
proof -
  have map_eq: "receive_query_commits bfs = map fri_layer_opening_step bfs"
    unfolding receive_query_commits_def fri_layer_opening_step_def
    by (simp add: fun_eq_iff split: prod.splits)
  show ?thesis
    by (rule mfold_fri_layer_opening_steps_hash_extends
        [OF outcome[unfolded map_eq]])
qed

lemma receive_query_commits_mfold_authenticated_opening_mono:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes auth: "authenticated_opening_in s opening"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute (mfold (idx, x, len, pw)
            (receive_query_commits bfs)) s)"
  shows "authenticated_opening_in t opening"
  by (rule authenticated_opening_in_mono
      [OF auth receive_query_commits_mfold_hash_extends[OF outcome]])

lemma receive_query_commits_mfold_head_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes len_pos: "0 < len"
    and idx_bound: "idx < len"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw)
              (receive_query_commits ((b, rt) # bfs))) s)"
  obtains chunk where "fri_layer_chunk_authenticated rt len idx chunk t"
proof -
  have map_eq:
    "receive_query_commits ((b, rt) # bfs) =
      map fri_layer_opening_step ((b, rt) # bfs)"
    unfolding receive_query_commits_def fri_layer_opening_step_def
    by (simp add: fun_eq_iff split: prod.splits)
  from mfold_fri_layer_opening_head_chunk_authenticated
      [OF len_pos idx_bound outcome[unfolded map_eq]]
  obtain chunk where "fri_layer_chunk_authenticated rt len idx chunk t"
    by blast
  then show ?thesis
    by (rule that)
qed

lemma verifier_query_round_after_index_trace_fri_head_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
  obtains idx chunk where
    "idx = index (to_nat raw)"
    "fri_layer_chunk_authenticated rt (clength * scale) idx chunk t"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have len_pos: "0 < clength * scale"
    using eval_domain_nontrivial by linarith
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  from receive_query_commits_mfold_head_chunk_authenticated
      [OF len_pos idx_bound trace_fri[unfolded f_fl_eq]]
  obtain chunk where auth_s2:
    "fri_layer_chunk_authenticated rt (clength * scale) ?idx chunk s2"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  have s3_s4: "s3 \<le> s4"
    by (rule receive_query_commits_mfold_hash_extends[OF comp_fri])
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  have s2_t: "s2 \<le> t"
    using s3_s4 unfolding s3_eq t_eq by simp
  have auth_t:
    "fri_layer_chunk_authenticated rt (clength * scale) ?idx chunk t"
    by (rule fri_layer_chunk_authenticated_mono[OF auth_s2 s2_t])
  show ?thesis
    by (rule that[OF refl auth_t])
qed

lemma verifier_query_round_after_index_trace_fri_selected_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
    and j_bound: "j < length f_fl"
    and layer_len_pos:
      "0 < fri_layer_lengths (length f_fl) (clength * scale) ! j"
    and layer_idx_bound:
      "fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length f_fl) (clength * scale) ! j"
  obtains chunk where
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  from receive_query_commits_selected_chunk_authenticated_at
      [OF trace_fri j_bound layer_len_pos layer_idx_bound]
  obtain chunk where auth_s2:
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) ?idx (clength * scale) ! j)
      chunk s2"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  have s3_s4: "s3 \<le> s4"
    by (rule receive_query_commits_mfold_hash_extends[OF comp_fri])
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  have s2_t: "s2 \<le> t"
    using s3_s4 unfolding s3_eq t_eq by simp
  have auth_t:
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) ?idx (clength * scale) ! j)
      chunk t"
    by (rule fri_layer_chunk_authenticated_mono[OF auth_s2 s2_t])
  then show ?thesis
    by (rule that)
qed

lemma verifier_query_round_after_index_composition_fri_head_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, rt) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
  obtains idx chunk where
    "idx = index (to_nat raw)"
    "fri_layer_chunk_authenticated rt (clength * scale) idx chunk t"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have len_pos: "0 < clength * scale"
    using eval_domain_nontrivial by linarith
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  from receive_query_commits_mfold_head_chunk_authenticated
      [OF len_pos idx_bound comp_fri[unfolded fl_eq]]
  obtain chunk where auth_s4:
    "fri_layer_chunk_authenticated rt (clength * scale) ?idx chunk s4"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  have auth_t:
    "fri_layer_chunk_authenticated rt (clength * scale) ?idx chunk t"
    using auth_s4 unfolding t_eq .
  show ?thesis
    by (rule that[OF refl auth_t])
qed

lemma verifier_query_round_after_index_composition_fri_selected_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
    and j_bound: "j < length fl"
    and layer_len_pos:
      "0 < fri_layer_lengths (length fl) (clength * scale) ! j"
    and layer_idx_bound:
      "fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length fl) (clength * scale) ! j"
  obtains chunk where
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  from receive_query_commits_selected_chunk_authenticated_at
      [OF comp_fri j_bound layer_len_pos layer_idx_bound]
  obtain chunk where auth_s4:
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) ?idx (clength * scale) ! j)
      chunk s4"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  have auth_t:
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) ?idx (clength * scale) ! j)
      chunk t"
    using auth_s4 unfolding t_eq .
  then show ?thesis
    by (rule that)
qed

lemma verifier_query_round_program_trace_fri_head_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx chunk where
    "idx = index (to_nat raw)"
    "fri_layer_chunk_authenticated rt (clength * scale) idx chunk t"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    raw:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  from verifier_query_round_after_index_trace_fri_head_chunk_authenticated
      [OF f_fl_eq tail]
  obtain idx chunk where
    idx_eq: "idx = index (to_nat raw)"
    and auth: "fri_layer_chunk_authenticated rt (clength * scale) idx chunk t"
    by blast
  show ?thesis
    by (rule that[OF idx_eq auth])
qed

lemma verifier_query_round_program_trace_fri_selected_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and j_bound: "j < length f_fl"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length f_fl) (clength * scale) ! j \<and>
        fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length f_fl) (clength * scale) ! j"
  obtains raw chunk where
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    raw:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  have layer_len_pos:
    "0 < fri_layer_lengths (length f_fl) (clength * scale) ! j"
    using raw_layer[of raw] by simp
  have layer_idx_bound:
    "fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! j <
      fri_layer_lengths (length f_fl) (clength * scale) ! j"
    using raw_layer[of raw] by simp
  from verifier_query_round_after_index_trace_fri_selected_chunk_authenticated
      [OF tail j_bound layer_len_pos layer_idx_bound]
  obtain chunk where auth:
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
    by blast
  show ?thesis
    by (rule that[OF auth])
qed

lemma verifier_query_round_program_trace_fri_selected_chunk_authenticated_with_lookup:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and j_bound: "j < length f_fl"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length f_fl) (clength * scale) ! j \<and>
        fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length f_fl) (clength * scale) ! j"
  obtains raw chunk where
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    raw:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  have layer_len_pos:
    "0 < fri_layer_lengths (length f_fl) (clength * scale) ! j"
    using raw_layer[of raw] by simp
  have layer_idx_bound:
    "fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! j <
      fri_layer_lengths (length f_fl) (clength * scale) ! j"
    using raw_layer[of raw] by simp
  from verifier_query_round_after_index_trace_fri_selected_chunk_authenticated
      [OF tail j_bound layer_len_pos layer_idx_bound]
  obtain chunk where auth:
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
    by blast
  have lookup_s0:
    "fmlookup (HashMap s0)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF raw] by simp
  have s0_t: "s0 \<le> t"
    using verifier_query_round_after_index_program_outcome[OF tail] by simp
  have lookup_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF lookup_s0 s0_t])
  show ?thesis
    by (rule that[OF auth lookup_t])
qed

lemma verifier_query_round_program_composition_fri_head_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, rt) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx chunk where
    "idx = index (to_nat raw)"
    "fri_layer_chunk_authenticated rt (clength * scale) idx chunk t"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    raw:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  from verifier_query_round_after_index_composition_fri_head_chunk_authenticated
      [OF fl_eq tail]
  obtain idx chunk where
    idx_eq: "idx = index (to_nat raw)"
    and auth: "fri_layer_chunk_authenticated rt (clength * scale) idx chunk t"
    by blast
  show ?thesis
    by (rule that[OF idx_eq auth])
qed

lemma verifier_query_round_program_composition_fri_selected_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and j_bound: "j < length fl"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length fl) (clength * scale) ! j \<and>
        fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length fl) (clength * scale) ! j"
  obtains raw chunk where
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    raw:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  have layer_len_pos:
    "0 < fri_layer_lengths (length fl) (clength * scale) ! j"
    using raw_layer[of raw] by simp
  have layer_idx_bound:
    "fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! j <
      fri_layer_lengths (length fl) (clength * scale) ! j"
    using raw_layer[of raw] by simp
  from
    verifier_query_round_after_index_composition_fri_selected_chunk_authenticated
      [OF tail j_bound layer_len_pos layer_idx_bound]
  obtain chunk where auth:
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
    by blast
  show ?thesis
    by (rule that[OF auth])
qed

lemma verifier_query_round_program_composition_fri_selected_chunk_authenticated_with_lookup:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and j_bound: "j < length fl"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length fl) (clength * scale) ! j \<and>
        fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length fl) (clength * scale) ! j"
  obtains raw chunk where
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    raw:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  have layer_len_pos:
    "0 < fri_layer_lengths (length fl) (clength * scale) ! j"
    using raw_layer[of raw] by simp
  have layer_idx_bound:
    "fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! j <
      fri_layer_lengths (length fl) (clength * scale) ! j"
    using raw_layer[of raw] by simp
  from
    verifier_query_round_after_index_composition_fri_selected_chunk_authenticated
      [OF tail j_bound layer_len_pos layer_idx_bound]
  obtain chunk where auth:
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
    by blast
  have lookup_s0:
    "fmlookup (HashMap s0)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF raw] by simp
  have s0_t: "s0 \<le> t"
    using verifier_query_round_after_index_program_outcome[OF tail] by simp
  have lookup_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF lookup_s0 s0_t])
  show ?thesis
    by (rule that[OF auth lookup_t])
qed

lemma ntimes_verifier_query_rounds_selected_trace_fri_head_chunk_authenticated_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
    and i_bound: "i < n"
  obtains raw idx chunk where
    "idx = index (to_nat raw)"
    "fri_layer_chunk_authenticated rt (clength * scale) idx chunk t"
proof -
  let ?round = "verifier_query_round_program fr f_fl f_final as fl final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix x suffix s_i s_suc where
    round:
      "Some (x, s_suc) \<in> set_dist (execute ?round s_i)"
    and suffix:
      "Some (suffix, t) \<in>
        set_dist (execute (ntimes ?round (n - Suc i)) s_suc)"
    by blast
  have x_eq: "x = ()"
    by (cases x) simp
  from verifier_query_round_program_trace_fri_head_chunk_authenticated
      [OF f_fl_eq round[unfolded x_eq]]
  obtain raw idx chunk where
    idx_eq: "idx = index (to_nat raw)"
    and auth_suc:
      "fri_layer_chunk_authenticated rt (clength * scale) idx chunk s_suc"
    by blast
  have s_suc_t: "s_suc \<le> t"
    using ntimes_verifier_query_rounds_outcome[OF suffix] by blast
  have auth_t:
    "fri_layer_chunk_authenticated rt (clength * scale) idx chunk t"
    by (rule fri_layer_chunk_authenticated_mono[OF auth_suc s_suc_t])
  show ?thesis
    by (rule that[OF idx_eq auth_t])
qed

lemma ntimes_verifier_query_rounds_selected_trace_fri_chunk_authenticated_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
    and i_bound: "i < n"
    and j_bound: "j < length f_fl"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length f_fl) (clength * scale) ! j \<and>
        fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length f_fl) (clength * scale) ! j"
  obtains raw chunk where
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
proof -
  let ?round = "verifier_query_round_program fr f_fl f_final as fl final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix x suffix s_i s_suc where
    round:
      "Some (x, s_suc) \<in> set_dist (execute ?round s_i)"
    and suffix:
      "Some (suffix, t) \<in>
        set_dist (execute (ntimes ?round (n - Suc i)) s_suc)"
    by blast
  have x_eq: "x = ()"
    by (cases x) simp
  from verifier_query_round_program_trace_fri_selected_chunk_authenticated
      [OF round[unfolded x_eq] j_bound raw_layer]
  obtain raw chunk where auth_suc:
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk s_suc"
    by blast
  have s_suc_t: "s_suc \<le> t"
    using ntimes_verifier_query_rounds_outcome[OF suffix] by blast
  have auth_t:
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
    by (rule fri_layer_chunk_authenticated_mono[OF auth_suc s_suc_t])
  show ?thesis
    by (rule that[OF auth_t])
qed

lemma ntimes_verifier_query_rounds_selected_trace_fri_chunk_authenticated_with_prefix_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
    and i_bound: "i < n"
    and j_bound: "j < length f_fl"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length f_fl) (clength * scale) ! j \<and>
        fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length f_fl) (clength * scale) ! j"
  obtains raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
      suffix_chunks layer_chunk where
    "idx = index (to_nat raw)"
    "length prefix_query_idxs = i"
    "length prefix_chunks = i"
    "length suffix_query_idxs = n - Suc i"
    "length suffix_chunks = n - Suc i"
    "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    "\<And>k. k < i \<Longrightarrow>
      verifier_query_round_chunk (prefix_query_idxs ! k)
        (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    "\<And>k. k < n - Suc i \<Longrightarrow>
      verifier_query_round_chunk (suffix_query_idxs ! k)
        (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
    "PTranscript s =
      List.concat (prefix_chunks @ chunk # suffix_chunks) @ PTranscript t"
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) idx (clength * scale) ! j)
      layer_chunk t"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s + i)
        (state_after_query_chunks (PState s) prefix_chunks i)) =
      Some raw"
proof -
  let ?round = "verifier_query_round_program fr f_fl f_final as fl final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix x suffix s_i s_suc where
    prefix:
      "Some (prefix, s_i) \<in>
        set_dist (execute (ntimes ?round i) s)"
    and round:
      "Some (x, s_suc) \<in> set_dist (execute ?round s_i)"
    and suffix:
      "Some (suffix, t) \<in>
        set_dist (execute (ntimes ?round (n - Suc i)) s_suc)"
    by blast
  have x_eq: "x = ()"
    by (cases x) simp
  show ?thesis
  proof (rule query_opening_ntimes_prefix_transcript_state_alignment
      [OF prefix])
    fix prefix_query_idxs prefix_chunks
    assume len_prefix_idxs: "length prefix_query_idxs = i"
      and len_prefix_chunks: "length prefix_chunks = i"
      and transcript_prefix:
        "PTranscript s = List.concat prefix_chunks @ PTranscript s_i"
      and state_i:
        "PState s_i =
          state_after_query_chunks (PState s) prefix_chunks i"
      and counter_i: "PQueryCounter s_i = PQueryCounter s + i"
      and prefix_ext: "s \<le> s_i"
      and prefix_rounds:
        "\<And>k. k < i \<Longrightarrow>
          verifier_query_round_chunk (prefix_query_idxs ! k)
            (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    show ?thesis
    proof (rule verifier_query_round_program_outcome_with_authenticated_trace_openings
        [OF round[unfolded x_eq]])
      fix raw idx chunk openings
      assume idx_eq: "idx = index (to_nat raw)"
        and chunk_shape:
          "verifier_query_round_chunk idx (map snd f_fl) (map snd fl)
            chunk"
        and transcript_round:
          "PTranscript s_i = chunk @ PTranscript s_suc"
        and state_suc:
          "PState s_suc = foldl concat (PState s_i) chunk"
        and round_ext: "s_i \<le> s_suc"
        and counter_suc: "PQueryCounter s_suc = Suc (PQueryCounter s_i)"
        and lookup_suc:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
            Some raw"
        and len_openings:
          "length openings = length (powers_scaled idx)"
        and trace_indices:
          "map opening_index openings = powers_scaled idx"
        and trace_table_suc:
          "partial_authenticated_table fr (scale * clength) openings
            s_suc"
      show ?thesis
      proof (rule
          verifier_query_round_program_trace_fri_selected_chunk_authenticated_with_lookup
            [OF round[unfolded x_eq] j_bound raw_layer])
        fix raw' layer_chunk
        assume auth_suc:
          "fri_layer_chunk_authenticated (snd (f_fl ! j))
            (fri_layer_lengths (length f_fl) (clength * scale) ! j)
            (fri_layer_indices (length f_fl) (index (to_nat raw'))
              (clength * scale) ! j)
            layer_chunk s_suc"
          and lookup_suc':
            "fmlookup (HashMap s_suc)
              (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
            Some raw'"
        have raw'_eq: "raw' = raw"
          using lookup_suc lookup_suc' by simp
        show ?thesis
        proof (rule query_opening_ntimes_suffix_transcript_state_alignment
            [OF suffix])
          fix suffix_query_idxs suffix_chunks
          assume len_suffix_idxs: "length suffix_query_idxs = n - Suc i"
            and len_suffix_chunks:
              "length suffix_chunks = n - Suc i"
            and transcript_suffix:
              "PTranscript s_suc =
                List.concat suffix_chunks @ PTranscript t"
            and suffix_state:
              "PState t =
                state_after_query_chunks (PState s_suc) suffix_chunks
                  (n - Suc i)"
            and suffix_counter:
              "PQueryCounter t = PQueryCounter s_suc + (n - Suc i)"
            and suffix_ext: "s_suc \<le> t"
            and suffix_rounds:
              "\<And>k. k < n - Suc i \<Longrightarrow>
                verifier_query_round_chunk (suffix_query_idxs ! k)
                  (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
          have transcript_all:
            "PTranscript s =
              List.concat (prefix_chunks @ chunk # suffix_chunks) @
                PTranscript t"
            using transcript_prefix transcript_round transcript_suffix
            by simp
          have auth_t_raw:
            "fri_layer_chunk_authenticated (snd (f_fl ! j))
              (fri_layer_lengths (length f_fl) (clength * scale) ! j)
              (fri_layer_indices (length f_fl) (index (to_nat raw))
                (clength * scale) ! j)
              layer_chunk t"
            by (rule fri_layer_chunk_authenticated_mono
                [OF auth_suc[unfolded raw'_eq] suffix_ext])
          have auth_t:
            "fri_layer_chunk_authenticated (snd (f_fl ! j))
              (fri_layer_lengths (length f_fl) (clength * scale) ! j)
              (fri_layer_indices (length f_fl) idx (clength * scale) ! j)
              layer_chunk t"
            using auth_t_raw idx_eq by simp
          have lookup_t:
            "fmlookup (HashMap t)
              (QueryIndexChallenge (PQueryCounter s + i)
                (state_after_query_chunks (PState s) prefix_chunks i)) =
              Some raw"
            using hash_extension_lookup[OF lookup_suc suffix_ext]
            unfolding counter_i state_i .
          show ?thesis
            by (rule that[OF idx_eq len_prefix_idxs len_prefix_chunks
                  len_suffix_idxs len_suffix_chunks chunk_shape
                  prefix_rounds suffix_rounds transcript_all auth_t
                  lookup_t])
        qed
      qed
    qed
  qed
qed

lemma ntimes_verifier_query_rounds_selected_trace_fri_chunk_aligned_with_replay_at:
  fixes query_state final_state :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    and i_bound: "i < rounds"
    and j_bound: "j < length f_fl"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length f_fl) (clength * scale) ! j \<and>
        fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length f_fl) (clength * scale) ! j"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
  obtains layer_chunk where
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) (query_idxs ! i)
        (clength * scale) ! j)
      layer_chunk final_state"
proof (rule
    ntimes_verifier_query_rounds_selected_trace_fri_chunk_authenticated_with_prefix_at
      [OF outcome i_bound j_bound raw_layer])
  fix raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
      suffix_chunks layer_chunk
  assume selected_idx: "idx = index (to_nat raw)"
    and len_prefix_idxs: "length prefix_query_idxs = i"
    and len_prefix_chunks: "length prefix_chunks = i"
    and len_suffix_idxs: "length suffix_query_idxs = rounds - Suc i"
    and len_suffix_chunks: "length suffix_chunks = rounds - Suc i"
    and chunk_shape:
      "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    and prefix_rounds:
      "\<And>k. k < i \<Longrightarrow>
        verifier_query_round_chunk (prefix_query_idxs ! k)
          (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    and suffix_rounds:
      "\<And>k. k < rounds - Suc i \<Longrightarrow>
        verifier_query_round_chunk (suffix_query_idxs ! k)
          (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
    and selected_transcript:
      "PTranscript query_state =
        List.concat (prefix_chunks @ chunk # suffix_chunks) @
          PTranscript final_state"
    and auth:
      "fri_layer_chunk_authenticated (snd (f_fl ! j))
        (fri_layer_lengths (length f_fl) (clength * scale) ! j)
        (fri_layer_indices (length f_fl) idx (clength * scale) ! j)
        layer_chunk final_state"
    and selected_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) prefix_chunks i)) =
        Some raw"
  let ?selected_chunks = "prefix_chunks @ chunk # suffix_chunks"
  have len_selected_chunks: "length ?selected_chunks = rounds"
    using len_prefix_chunks len_suffix_chunks i_bound by simp
  have selected_chunk_lens:
    "\<And>k. k < rounds \<Longrightarrow>
      length (?selected_chunks ! k) =
        verifier_query_round_transcript_length (query_idxs ! k)
          (map snd f_fl) (map snd fl)"
  proof -
    fix k
    assume k_bound: "k < rounds"
    show
      "length (?selected_chunks ! k) =
        verifier_query_round_transcript_length (query_idxs ! k)
          (map snd f_fl) (map snd fl)"
    proof (cases "k < i")
      case True
      have nth_eq: "?selected_chunks ! k = prefix_chunks ! k"
        using True len_prefix_chunks by (simp add: nth_append)
      have
        "length (prefix_chunks ! k) =
          verifier_query_round_transcript_length
            (prefix_query_idxs ! k) (map snd f_fl) (map snd fl)"
        by (rule verifier_query_round_chunk_length[OF prefix_rounds[OF True]])
      then show ?thesis
        using nth_eq
        by (simp add: verifier_query_round_transcript_length_index_irrelevant)
    next
      case False
      show ?thesis
      proof (cases "k = i")
        case True
        have nth_eq: "?selected_chunks ! k = chunk"
          using True len_prefix_chunks by (simp add: nth_append)
        have
          "length chunk =
            verifier_query_round_transcript_length idx
              (map snd f_fl) (map snd fl)"
          by (rule verifier_query_round_chunk_length[OF chunk_shape])
        then show ?thesis
          using nth_eq
          by (simp add:
              verifier_query_round_transcript_length_index_irrelevant)
      next
        case False
        let ?k = "k - Suc i"
        have ge: "Suc i \<le> k"
          using \<open>\<not> k < i\<close> False by linarith
        have k_bound': "?k < rounds - Suc i"
          using ge k_bound by linarith
        have nth_eq: "?selected_chunks ! k = suffix_chunks ! ?k"
          using ge len_prefix_chunks by (simp add: nth_append)
        have
          "length (suffix_chunks ! ?k) =
            verifier_query_round_transcript_length
              (suffix_query_idxs ! ?k) (map snd f_fl) (map snd fl)"
          by (rule verifier_query_round_chunk_length
              [OF suffix_rounds[OF k_bound']])
        then show ?thesis
          using nth_eq
          by (simp add:
              verifier_query_round_transcript_length_index_irrelevant)
      qed
    qed
  qed
  have query_chunk_lens:
    "\<And>k. k < rounds \<Longrightarrow>
      length (query_chunks ! k) =
        verifier_query_round_transcript_length (query_idxs ! k)
          (map snd f_fl) (map snd fl)"
    using query_chunk verifier_query_round_chunk_length by blast
  have concat_eq: "List.concat ?selected_chunks = List.concat query_chunks"
    using selected_transcript transcript_query by simp
  have chunks_eq: "?selected_chunks = query_chunks"
  proof -
    have same_lens:
      "\<And>k. k < length ?selected_chunks \<Longrightarrow>
        length (?selected_chunks ! k) = length (query_chunks ! k)"
      using selected_chunk_lens query_chunk_lens len_selected_chunks by simp
    have concat_eq_empty:
      "List.concat ?selected_chunks @ [] = List.concat query_chunks"
      using concat_eq by simp
    have len_eq: "length ?selected_chunks = length query_chunks"
      using len_selected_chunks len_query_chunks by simp
    have "?selected_chunks = query_chunks \<and> ([] :: 'f list) = []"
      by (rule concat_append_eq_concat_same_chunk_lengths
          [OF len_eq same_lens concat_eq_empty])
    then show ?thesis
      by simp
  qed
  have prefix_state_eq:
    "state_after_query_chunks (PState query_state) prefix_chunks i =
      state_after_query_chunks (PState query_state) query_chunks i"
  proof -
    have
      "state_after_query_chunks (PState query_state) ?selected_chunks i =
        state_after_query_chunks (PState query_state) prefix_chunks i"
      by (rule state_after_query_chunks_append_prefix[OF len_prefix_chunks])
    then show ?thesis
      using chunks_eq by simp
  qed
  have selected_lookup_global:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge (PQueryCounter query_state + i)
        (state_after_query_chunks (PState query_state) query_chunks i)) =
      Some raw"
    using selected_lookup prefix_state_eq by simp
  have raw_eq: "raw = raw_idxs ! i"
    using selected_lookup_global replay_lookup[OF i_bound] by simp
  have idx_eq: "idx = query_idxs ! i"
    using selected_idx raw_eq query_idxs_eq len_raw i_bound by simp
  show ?thesis
    by (rule that[of layer_chunk]) (use auth idx_eq in simp)
qed

lemma ntimes_verifier_query_rounds_selected_composition_fri_head_chunk_authenticated_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, rt) # fl_tail"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
    and i_bound: "i < n"
  obtains raw idx chunk where
    "idx = index (to_nat raw)"
    "fri_layer_chunk_authenticated rt (clength * scale) idx chunk t"
proof -
  let ?round = "verifier_query_round_program fr f_fl f_final as fl final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix x suffix s_i s_suc where
    round:
      "Some (x, s_suc) \<in> set_dist (execute ?round s_i)"
    and suffix:
      "Some (suffix, t) \<in>
        set_dist (execute (ntimes ?round (n - Suc i)) s_suc)"
    by blast
  have x_eq: "x = ()"
    by (cases x) simp
  from verifier_query_round_program_composition_fri_head_chunk_authenticated
      [OF fl_eq round[unfolded x_eq]]
  obtain raw idx chunk where
    idx_eq: "idx = index (to_nat raw)"
    and auth_suc:
      "fri_layer_chunk_authenticated rt (clength * scale) idx chunk s_suc"
    by blast
  have s_suc_t: "s_suc \<le> t"
    using ntimes_verifier_query_rounds_outcome[OF suffix] by blast
  have auth_t:
    "fri_layer_chunk_authenticated rt (clength * scale) idx chunk t"
    by (rule fri_layer_chunk_authenticated_mono[OF auth_suc s_suc_t])
  show ?thesis
    by (rule that[OF idx_eq auth_t])
qed

lemma ntimes_verifier_query_rounds_selected_composition_fri_chunk_authenticated_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
    and i_bound: "i < n"
    and j_bound: "j < length fl"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length fl) (clength * scale) ! j \<and>
        fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length fl) (clength * scale) ! j"
  obtains raw chunk where
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
proof -
  let ?round = "verifier_query_round_program fr f_fl f_final as fl final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix x suffix s_i s_suc where
    round:
      "Some (x, s_suc) \<in> set_dist (execute ?round s_i)"
    and suffix:
      "Some (suffix, t) \<in>
        set_dist (execute (ntimes ?round (n - Suc i)) s_suc)"
    by blast
  have x_eq: "x = ()"
    by (cases x) simp
  from
    verifier_query_round_program_composition_fri_selected_chunk_authenticated
      [OF round[unfolded x_eq] j_bound raw_layer]
  obtain raw chunk where auth_suc:
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk s_suc"
    by blast
  have s_suc_t: "s_suc \<le> t"
    using ntimes_verifier_query_rounds_outcome[OF suffix] by blast
  have auth_t:
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! j)
      chunk t"
    by (rule fri_layer_chunk_authenticated_mono[OF auth_suc s_suc_t])
  show ?thesis
    by (rule that[OF auth_t])
qed

lemma ntimes_verifier_query_rounds_selected_composition_fri_chunk_authenticated_with_prefix_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
    and i_bound: "i < n"
    and j_bound: "j < length fl"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length fl) (clength * scale) ! j \<and>
        fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length fl) (clength * scale) ! j"
  obtains raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
      suffix_chunks layer_chunk where
    "idx = index (to_nat raw)"
    "length prefix_query_idxs = i"
    "length prefix_chunks = i"
    "length suffix_query_idxs = n - Suc i"
    "length suffix_chunks = n - Suc i"
    "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    "\<And>k. k < i \<Longrightarrow>
      verifier_query_round_chunk (prefix_query_idxs ! k)
        (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    "\<And>k. k < n - Suc i \<Longrightarrow>
      verifier_query_round_chunk (suffix_query_idxs ! k)
        (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
    "PTranscript s =
      List.concat (prefix_chunks @ chunk # suffix_chunks) @ PTranscript t"
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) idx (clength * scale) ! j)
      layer_chunk t"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s + i)
        (state_after_query_chunks (PState s) prefix_chunks i)) =
      Some raw"
proof -
  let ?round = "verifier_query_round_program fr f_fl f_final as fl final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix x suffix s_i s_suc where
    prefix:
      "Some (prefix, s_i) \<in>
        set_dist (execute (ntimes ?round i) s)"
    and round:
      "Some (x, s_suc) \<in> set_dist (execute ?round s_i)"
    and suffix:
      "Some (suffix, t) \<in>
        set_dist (execute (ntimes ?round (n - Suc i)) s_suc)"
    by blast
  have x_eq: "x = ()"
    by (cases x) simp
  show ?thesis
  proof (rule query_opening_ntimes_prefix_transcript_state_alignment
      [OF prefix])
    fix prefix_query_idxs prefix_chunks
    assume len_prefix_idxs: "length prefix_query_idxs = i"
      and len_prefix_chunks: "length prefix_chunks = i"
      and transcript_prefix:
        "PTranscript s = List.concat prefix_chunks @ PTranscript s_i"
      and state_i:
        "PState s_i =
          state_after_query_chunks (PState s) prefix_chunks i"
      and counter_i: "PQueryCounter s_i = PQueryCounter s + i"
      and prefix_ext: "s \<le> s_i"
      and prefix_rounds:
        "\<And>k. k < i \<Longrightarrow>
          verifier_query_round_chunk (prefix_query_idxs ! k)
            (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    show ?thesis
    proof (rule verifier_query_round_program_outcome_with_authenticated_trace_openings
        [OF round[unfolded x_eq]])
      fix raw idx chunk openings
      assume idx_eq: "idx = index (to_nat raw)"
        and chunk_shape:
          "verifier_query_round_chunk idx (map snd f_fl) (map snd fl)
            chunk"
        and transcript_round:
          "PTranscript s_i = chunk @ PTranscript s_suc"
        and state_suc:
          "PState s_suc = foldl concat (PState s_i) chunk"
        and round_ext: "s_i \<le> s_suc"
        and counter_suc: "PQueryCounter s_suc = Suc (PQueryCounter s_i)"
        and lookup_suc:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
            Some raw"
        and len_openings:
          "length openings = length (powers_scaled idx)"
        and trace_indices:
          "map opening_index openings = powers_scaled idx"
        and trace_table_suc:
          "partial_authenticated_table fr (scale * clength) openings
            s_suc"
      show ?thesis
      proof (rule
          verifier_query_round_program_composition_fri_selected_chunk_authenticated_with_lookup
            [OF round[unfolded x_eq] j_bound raw_layer])
        fix raw' layer_chunk
        assume auth_suc:
          "fri_layer_chunk_authenticated (snd (fl ! j))
            (fri_layer_lengths (length fl) (clength * scale) ! j)
            (fri_layer_indices (length fl) (index (to_nat raw'))
              (clength * scale) ! j)
            layer_chunk s_suc"
          and lookup_suc':
            "fmlookup (HashMap s_suc)
              (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
            Some raw'"
        have raw'_eq: "raw' = raw"
          using lookup_suc lookup_suc' by simp
        show ?thesis
        proof (rule query_opening_ntimes_suffix_transcript_state_alignment
            [OF suffix])
          fix suffix_query_idxs suffix_chunks
          assume len_suffix_idxs: "length suffix_query_idxs = n - Suc i"
            and len_suffix_chunks:
              "length suffix_chunks = n - Suc i"
            and transcript_suffix:
              "PTranscript s_suc =
                List.concat suffix_chunks @ PTranscript t"
            and suffix_state:
              "PState t =
                state_after_query_chunks (PState s_suc) suffix_chunks
                  (n - Suc i)"
            and suffix_counter:
              "PQueryCounter t = PQueryCounter s_suc + (n - Suc i)"
            and suffix_ext: "s_suc \<le> t"
            and suffix_rounds:
              "\<And>k. k < n - Suc i \<Longrightarrow>
                verifier_query_round_chunk (suffix_query_idxs ! k)
                  (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
          have transcript_all:
            "PTranscript s =
              List.concat (prefix_chunks @ chunk # suffix_chunks) @
                PTranscript t"
            using transcript_prefix transcript_round transcript_suffix
            by simp
          have auth_t_raw:
            "fri_layer_chunk_authenticated (snd (fl ! j))
              (fri_layer_lengths (length fl) (clength * scale) ! j)
              (fri_layer_indices (length fl) (index (to_nat raw))
                (clength * scale) ! j)
              layer_chunk t"
            by (rule fri_layer_chunk_authenticated_mono
                [OF auth_suc[unfolded raw'_eq] suffix_ext])
          have auth_t:
            "fri_layer_chunk_authenticated (snd (fl ! j))
              (fri_layer_lengths (length fl) (clength * scale) ! j)
              (fri_layer_indices (length fl) idx (clength * scale) ! j)
              layer_chunk t"
            using auth_t_raw idx_eq by simp
          have lookup_t:
            "fmlookup (HashMap t)
              (QueryIndexChallenge (PQueryCounter s + i)
                (state_after_query_chunks (PState s) prefix_chunks i)) =
              Some raw"
            using hash_extension_lookup[OF lookup_suc suffix_ext]
            unfolding counter_i state_i .
          show ?thesis
            by (rule that[OF idx_eq len_prefix_idxs len_prefix_chunks
                  len_suffix_idxs len_suffix_chunks chunk_shape
                  prefix_rounds suffix_rounds transcript_all auth_t
                  lookup_t])
        qed
      qed
    qed
  qed
qed

lemma ntimes_verifier_query_rounds_selected_composition_fri_chunk_aligned_with_replay_at:
  fixes query_state final_state :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    and i_bound: "i < rounds"
    and j_bound: "j < length fl"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length fl) (clength * scale) ! j \<and>
        fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! j <
        fri_layer_lengths (length fl) (clength * scale) ! j"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
  obtains layer_chunk where
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) (query_idxs ! i)
        (clength * scale) ! j)
      layer_chunk final_state"
proof (rule
    ntimes_verifier_query_rounds_selected_composition_fri_chunk_authenticated_with_prefix_at
      [OF outcome i_bound j_bound raw_layer])
  fix raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
      suffix_chunks layer_chunk
  assume selected_idx: "idx = index (to_nat raw)"
    and len_prefix_idxs: "length prefix_query_idxs = i"
    and len_prefix_chunks: "length prefix_chunks = i"
    and len_suffix_idxs: "length suffix_query_idxs = rounds - Suc i"
    and len_suffix_chunks: "length suffix_chunks = rounds - Suc i"
    and chunk_shape:
      "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    and prefix_rounds:
      "\<And>k. k < i \<Longrightarrow>
        verifier_query_round_chunk (prefix_query_idxs ! k)
          (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    and suffix_rounds:
      "\<And>k. k < rounds - Suc i \<Longrightarrow>
        verifier_query_round_chunk (suffix_query_idxs ! k)
          (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
    and selected_transcript:
      "PTranscript query_state =
        List.concat (prefix_chunks @ chunk # suffix_chunks) @
          PTranscript final_state"
    and auth:
      "fri_layer_chunk_authenticated (snd (fl ! j))
        (fri_layer_lengths (length fl) (clength * scale) ! j)
        (fri_layer_indices (length fl) idx (clength * scale) ! j)
        layer_chunk final_state"
    and selected_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) prefix_chunks i)) =
        Some raw"
  let ?selected_chunks = "prefix_chunks @ chunk # suffix_chunks"
  have len_selected_chunks: "length ?selected_chunks = rounds"
    using len_prefix_chunks len_suffix_chunks i_bound by simp
  have selected_chunk_lens:
    "\<And>k. k < rounds \<Longrightarrow>
      length (?selected_chunks ! k) =
        verifier_query_round_transcript_length (query_idxs ! k)
          (map snd f_fl) (map snd fl)"
  proof -
    fix k
    assume k_bound: "k < rounds"
    show
      "length (?selected_chunks ! k) =
        verifier_query_round_transcript_length (query_idxs ! k)
          (map snd f_fl) (map snd fl)"
    proof (cases "k < i")
      case True
      have nth_eq: "?selected_chunks ! k = prefix_chunks ! k"
        using True len_prefix_chunks by (simp add: nth_append)
      have
        "length (prefix_chunks ! k) =
          verifier_query_round_transcript_length
            (prefix_query_idxs ! k) (map snd f_fl) (map snd fl)"
        by (rule verifier_query_round_chunk_length[OF prefix_rounds[OF True]])
      then show ?thesis
        using nth_eq
        by (simp add: verifier_query_round_transcript_length_index_irrelevant)
    next
      case False
      show ?thesis
      proof (cases "k = i")
        case True
        have nth_eq: "?selected_chunks ! k = chunk"
          using True len_prefix_chunks by (simp add: nth_append)
        have
          "length chunk =
            verifier_query_round_transcript_length idx
              (map snd f_fl) (map snd fl)"
          by (rule verifier_query_round_chunk_length[OF chunk_shape])
        then show ?thesis
          using nth_eq
          by (simp add:
              verifier_query_round_transcript_length_index_irrelevant)
      next
        case False
        let ?k = "k - Suc i"
        have ge: "Suc i \<le> k"
          using \<open>\<not> k < i\<close> False by linarith
        have k_bound': "?k < rounds - Suc i"
          using ge k_bound by linarith
        have nth_eq: "?selected_chunks ! k = suffix_chunks ! ?k"
          using ge len_prefix_chunks by (simp add: nth_append)
        have
          "length (suffix_chunks ! ?k) =
            verifier_query_round_transcript_length
              (suffix_query_idxs ! ?k) (map snd f_fl) (map snd fl)"
          by (rule verifier_query_round_chunk_length
              [OF suffix_rounds[OF k_bound']])
        then show ?thesis
          using nth_eq
          by (simp add:
              verifier_query_round_transcript_length_index_irrelevant)
      qed
    qed
  qed
  have query_chunk_lens:
    "\<And>k. k < rounds \<Longrightarrow>
      length (query_chunks ! k) =
        verifier_query_round_transcript_length (query_idxs ! k)
          (map snd f_fl) (map snd fl)"
    using query_chunk verifier_query_round_chunk_length by blast
  have concat_eq: "List.concat ?selected_chunks = List.concat query_chunks"
    using selected_transcript transcript_query by simp
  have chunks_eq: "?selected_chunks = query_chunks"
  proof -
    have same_lens:
      "\<And>k. k < length ?selected_chunks \<Longrightarrow>
        length (?selected_chunks ! k) = length (query_chunks ! k)"
      using selected_chunk_lens query_chunk_lens len_selected_chunks by simp
    have concat_eq_empty:
      "List.concat ?selected_chunks @ [] = List.concat query_chunks"
      using concat_eq by simp
    have len_eq: "length ?selected_chunks = length query_chunks"
      using len_selected_chunks len_query_chunks by simp
    have "?selected_chunks = query_chunks \<and> ([] :: 'f list) = []"
      by (rule concat_append_eq_concat_same_chunk_lengths
          [OF len_eq same_lens concat_eq_empty])
    then show ?thesis
      by simp
  qed
  have prefix_state_eq:
    "state_after_query_chunks (PState query_state) prefix_chunks i =
      state_after_query_chunks (PState query_state) query_chunks i"
  proof -
    have
      "state_after_query_chunks (PState query_state) ?selected_chunks i =
        state_after_query_chunks (PState query_state) prefix_chunks i"
      by (rule state_after_query_chunks_append_prefix[OF len_prefix_chunks])
    then show ?thesis
      using chunks_eq by simp
  qed
  have selected_lookup_global:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge (PQueryCounter query_state + i)
        (state_after_query_chunks (PState query_state) query_chunks i)) =
      Some raw"
    using selected_lookup prefix_state_eq by simp
  have raw_eq: "raw = raw_idxs ! i"
    using selected_lookup_global replay_lookup[OF i_bound] by simp
  have idx_eq: "idx = query_idxs ! i"
    using selected_idx raw_eq query_idxs_eq len_raw i_bound by simp
  show ?thesis
    by (rule that[of layer_chunk]) (use auth idx_eq in simp)
qed

lemma accepted_fri_opening_transcript_trace_selected_chunk_authenticated_at:
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
  obtains layer_chunk where
    "fri_layer_chunk_authenticated (trace_roots ! j)
      (fri_layer_lengths (length trace_roots) (clength * scale) ! j)
      (fri_layer_indices (length trace_roots) (query_idxs ! i)
        (clength * scale) ! j)
      layer_chunk final_state"
proof -
  from fri_openings obtain result' final_state' fr f_fl as fl query_state
      raw_idxs query_chunks where
    out_def: "out = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and outcome:
      "Some (result', final_state') \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr f_fl trace_final as fl
              composition_final)
            rounds)
          query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state'"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    unfolding accepted_fri_opening_transcript_def by blast
  have result_eq: "result' = result"
    using out_def out_eq by simp
  have final_state_eq: "final_state' = final_state"
    using out_def out_eq by simp
  have outcome':
    "Some (result, final_state) \<in>
      set_dist (execute
        (ntimes
          (verifier_query_round_program fr f_fl trace_final as fl
            composition_final)
          rounds)
        query_state)"
    using outcome result_eq final_state_eq by simp
  have j_bound_f: "j < length f_fl"
    using layer_bound trace_roots_eq by simp
  have raw_layer_f:
    "\<And>raw.
      0 < fri_layer_lengths (length f_fl) (clength * scale) ! j \<and>
      fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! j <
      fri_layer_lengths (length f_fl) (clength * scale) ! j"
    using raw_layer trace_roots_eq by simp
  have query_chunk_f:
    "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (query_idxs ! i)
        (map snd f_fl) (map snd fl) (query_chunks ! i)"
    using query_chunk trace_roots_eq composition_roots_eq by simp
  from ntimes_verifier_query_rounds_selected_trace_fri_chunk_aligned_with_replay_at
      [OF outcome' round_bound j_bound_f raw_layer_f len_raw query_idxs_eq
        len_query_chunks transcript_query[unfolded final_state_eq]
        query_chunk_f replay_lookup[unfolded final_state_eq]]
  obtain layer_chunk where auth:
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) (query_idxs ! i)
        (clength * scale) ! j)
      layer_chunk final_state"
    by blast
  have root_eq: "trace_roots ! j = snd (f_fl ! j)"
    using trace_roots_eq layer_bound by simp
  show ?thesis
    by (rule that[of layer_chunk])
      (use auth trace_roots_eq root_eq in simp)
qed

lemma accepted_fri_opening_transcript_composition_selected_chunk_authenticated_at:
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
  obtains layer_chunk where
    "fri_layer_chunk_authenticated (composition_roots ! j)
      (fri_layer_lengths (length composition_roots) (clength * scale) ! j)
      (fri_layer_indices (length composition_roots) (query_idxs ! i)
        (clength * scale) ! j)
      layer_chunk final_state"
proof -
  from fri_openings obtain result' final_state' fr f_fl as fl query_state
      raw_idxs query_chunks where
    out_def: "out = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and outcome:
      "Some (result', final_state') \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr f_fl trace_final as fl
              composition_final)
            rounds)
          query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state'"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    unfolding accepted_fri_opening_transcript_def by blast
  have result_eq: "result' = result"
    using out_def out_eq by simp
  have final_state_eq: "final_state' = final_state"
    using out_def out_eq by simp
  have outcome':
    "Some (result, final_state) \<in>
      set_dist (execute
        (ntimes
          (verifier_query_round_program fr f_fl trace_final as fl
            composition_final)
          rounds)
        query_state)"
    using outcome result_eq final_state_eq by simp
  have j_bound_f: "j < length fl"
    using layer_bound composition_roots_eq by simp
  have raw_layer_f:
    "\<And>raw.
      0 < fri_layer_lengths (length fl) (clength * scale) ! j \<and>
      fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! j <
      fri_layer_lengths (length fl) (clength * scale) ! j"
    using raw_layer composition_roots_eq by simp
  have query_chunk_f:
    "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (query_idxs ! i)
        (map snd f_fl) (map snd fl) (query_chunks ! i)"
    using query_chunk trace_roots_eq composition_roots_eq by simp
  from ntimes_verifier_query_rounds_selected_composition_fri_chunk_aligned_with_replay_at
      [OF outcome' round_bound j_bound_f raw_layer_f len_raw query_idxs_eq
        len_query_chunks transcript_query[unfolded final_state_eq]
        query_chunk_f replay_lookup[unfolded final_state_eq]]
  obtain layer_chunk where auth:
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) (query_idxs ! i)
        (clength * scale) ! j)
      layer_chunk final_state"
    by blast
  have root_eq: "composition_roots ! j = snd (fl ! j)"
    using composition_roots_eq layer_bound by simp
  show ?thesis
    by (rule that[of layer_chunk])
      (use auth composition_roots_eq root_eq in simp)
qed

end

end
