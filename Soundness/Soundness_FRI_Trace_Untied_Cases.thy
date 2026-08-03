(*  Title:      Stark/Soundness_FRI_Trace_Untied_Cases.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Trace_Untied_Cases
  imports Soundness_FRI_Trace_Candidate_Blocker
begin

text \<open>
  Case split for the remaining trace FRI untied-witness residual.

  The broad residual says that the reachable low-degree witness consumed by
  the verifier and the separate non-low-degree reachable witness disagree in
  at least one of: authenticated root, query-index list, or sampled openings.
  This theory exposes these three causes as separate events so subsequent
  proof layers can bound them independently.
\<close>

context soundness
begin

definition trace_fri_header_tied_low_candidate_untied_reachable_witness_case
  :: "('f \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
        'f authenticated_opening list list \<Rightarrow>
        'f authenticated_opening list list \<Rightarrow> bool) \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_untied_reachable_witness_case P s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        fr0 query_idxs0 trace_openings0 trace_table0.
      trace_fri_reachable_header_tie_gap s out \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      trace_table_low_degree trace_table \<and>
      accepted_with_partial_trace_openings s out fr0 query_idxs0
        trace_openings0 \<and>
      partial_trace_table_candidate trace_table0 trace_openings0 \<and>
      \<not> trace_table_low_degree trace_table0 \<and>
      P fr0 fr query_idxs0 fri_query_idxs trace_openings0 trace_openings)"

lemma trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI:
  assumes
    "trace_fri_reachable_header_tie_gap s out"
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    "verifier_header_transcript s fr trace_roots trace_final as fri_dg
      composition_roots composition_final rest"
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "trace_table_low_degree trace_table"
    "accepted_with_partial_trace_openings s out fr0 query_idxs0
      trace_openings0"
    "partial_trace_table_candidate trace_table0 trace_openings0"
    "\<not> trace_table_low_degree trace_table0"
    "P fr0 fr query_idxs0 fri_query_idxs trace_openings0 trace_openings"
  shows
    "trace_fri_header_tied_low_candidate_untied_reachable_witness_case
      P s out"
  unfolding
    trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
  by (intro exI conjI)
    (rule assms)+

definition trace_fri_header_tied_low_candidate_untied_root_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_untied_root_gap s out
    \<longleftrightarrow>
    trace_fri_header_tied_low_candidate_untied_reachable_witness_case
      (\<lambda>fr0 fr _ _ _ _. fr0 \<noteq> fr) s out"

definition trace_fri_header_tied_low_candidate_untied_query_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_untied_query_gap s out
    \<longleftrightarrow>
    trace_fri_header_tied_low_candidate_untied_reachable_witness_case
      (\<lambda>_ _ query_idxs0 fri_query_idxs _ _.
        query_idxs0 \<noteq> fri_query_idxs) s out"

definition trace_fri_header_tied_low_candidate_untied_openings_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_untied_openings_gap s out
    \<longleftrightarrow>
    trace_fri_header_tied_low_candidate_untied_reachable_witness_case
      (\<lambda>_ _ _ _ trace_openings0 trace_openings.
        trace_openings0 \<noteq> trace_openings) s out"

definition trace_fri_header_tied_low_candidate_untied_normalized_openings_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_untied_normalized_openings_gap s out
    \<longleftrightarrow>
    trace_fri_header_tied_low_candidate_untied_reachable_witness_case
      (\<lambda>fr0 fr query_idxs0 fri_query_idxs trace_openings0 trace_openings.
        fr0 = fr \<and> query_idxs0 = fri_query_idxs \<and>
        trace_openings0 \<noteq> trace_openings) s out"

definition trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap s out
    \<longleftrightarrow>
    trace_fri_header_tied_low_candidate_untied_reachable_witness_case
      (\<lambda>fr0 fr query_idxs0 fri_query_idxs trace_openings0 trace_openings.
        (fr0 \<noteq> fr \<or> query_idxs0 \<noteq> fri_query_idxs) \<and>
        trace_openings0 \<noteq> trace_openings) s out"

lemma trace_fri_header_tied_low_candidate_untied_reachable_witness_gap_imp_cases:
  assumes
    "trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
  shows
    "trace_fri_header_tied_low_candidate_untied_root_gap s out \<or>
     trace_fri_header_tied_low_candidate_untied_query_gap s out \<or>
     trace_fri_header_tied_low_candidate_untied_openings_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table fr0 query_idxs0 trace_openings0 trace_table0 where
    gap: "trace_fri_reachable_header_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and low: "trace_table_low_degree trace_table"
    and partial0:
      "accepted_with_partial_trace_openings s out fr0 query_idxs0
        trace_openings0"
    and candidate0:
      "partial_trace_table_candidate trace_table0 trace_openings0"
    and not_low0: "\<not> trace_table_low_degree trace_table0"
    and mismatch:
      "fr0 \<noteq> fr \<or> query_idxs0 \<noteq> fri_query_idxs \<or>
        trace_openings0 \<noteq> trace_openings"
    unfolding
      trace_fri_header_tied_low_candidate_untied_reachable_witness_gap_def
    by blast
  from mismatch show ?thesis
  proof
    assume root_mismatch: "fr0 \<noteq> fr"
    have "trace_fri_header_tied_low_candidate_untied_root_gap s out"
      unfolding trace_fri_header_tied_low_candidate_untied_root_gap_def
      by (rule
          trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI)
        (rule gap, rule fri_openings, rule header, rule partial,
          rule candidate, rule low, rule partial0, rule candidate0,
          rule not_low0, rule root_mismatch)
    then show ?thesis by simp
  next
    assume tail:
      "query_idxs0 \<noteq> fri_query_idxs \<or>
        trace_openings0 \<noteq> trace_openings"
    then show ?thesis
    proof
      assume query_mismatch: "query_idxs0 \<noteq> fri_query_idxs"
      have "trace_fri_header_tied_low_candidate_untied_query_gap s out"
        unfolding trace_fri_header_tied_low_candidate_untied_query_gap_def
        by (rule
            trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI)
          (rule gap, rule fri_openings, rule header, rule partial,
            rule candidate, rule low, rule partial0, rule candidate0,
            rule not_low0, rule query_mismatch)
      then show ?thesis by simp
    next
      assume openings_mismatch:
        "trace_openings0 \<noteq> trace_openings"
      have "trace_fri_header_tied_low_candidate_untied_openings_gap s out"
        unfolding trace_fri_header_tied_low_candidate_untied_openings_gap_def
        by (rule
            trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI)
          (rule gap, rule fri_openings, rule header, rule partial,
            rule candidate, rule low, rule partial0, rule candidate0,
            rule not_low0, rule openings_mismatch)
      then show ?thesis by simp
    qed
  qed
qed

lemma trace_fri_header_tied_low_candidate_untied_root_gap_imp_witness_gap:
  assumes "trace_fri_header_tied_low_candidate_untied_root_gap s out"
  shows
    "trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
  using assms
  unfolding
    trace_fri_header_tied_low_candidate_untied_reachable_witness_gap_def
    trace_fri_header_tied_low_candidate_untied_root_gap_def
    trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
  by blast

lemma trace_fri_header_tied_low_candidate_untied_query_gap_imp_witness_gap:
  assumes "trace_fri_header_tied_low_candidate_untied_query_gap s out"
  shows
    "trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
  using assms
  unfolding
    trace_fri_header_tied_low_candidate_untied_reachable_witness_gap_def
    trace_fri_header_tied_low_candidate_untied_query_gap_def
    trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
  by blast

lemma trace_fri_header_tied_low_candidate_untied_openings_gap_imp_witness_gap:
  assumes "trace_fri_header_tied_low_candidate_untied_openings_gap s out"
  shows
    "trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
  using assms
  unfolding
    trace_fri_header_tied_low_candidate_untied_reachable_witness_gap_def
    trace_fri_header_tied_low_candidate_untied_openings_gap_def
    trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
  by blast

lemma merkle_path_bound_unique_path_if_clean:
  assumes clean: "\<not> hash_map_output_collision s"
    and first: "merkle_path_bound rt len idx v path s"
    and second: "merkle_path_bound rt len idx v path' s"
    and same_length: "length path = length path'"
  shows "path = path'"
  using first second same_length
proof (induction path arbitrary: path' rt len idx)
  case Nil
  then show ?case by simp
next
  case (Cons sibling path)
  from Cons.prems(3) obtain sibling' path'' where
    path': "path' = sibling' # path''"
    and lengths: "length path = length path''"
    by (cases path') auto
  show ?case
  proof (cases "idx < len div 2")
    case True
    obtain child where
      child:
        "merkle_path_bound child (len div 2) idx v path s"
      and first_lookup:
        "fmlookup (HashMap s) (MerkleNode child sibling) = Some rt"
      using Cons.prems(1) True by auto
    obtain child' where
      child':
        "merkle_path_bound child' (len div 2) idx v path'' s"
      and second_lookup:
        "fmlookup (HashMap s) (MerkleNode child' sibling') = Some rt"
      using Cons.prems(2) True path' by auto
    have node_eq:
      "MerkleNode child sibling = MerkleNode child' sibling'"
    proof (rule ccontr)
      assume neq:
        "MerkleNode child sibling \<noteq> MerkleNode child' sibling'"
      have "hash_map_output_collision s"
        by (rule hash_map_output_collisionI
            [OF neq first_lookup second_lookup])
      then show False using clean by contradiction
    qed
    have child_eq: "child = child'" using node_eq by simp
    have sibling_eq: "sibling = sibling'" using node_eq by simp
    have path_eq: "path = path''"
      by (rule Cons.IH[OF child _ lengths])
        (use child' child_eq in simp)
    show ?thesis
      using path' sibling_eq path_eq by simp
  next
    case False
    obtain child where
      child:
        "merkle_path_bound child (len div 2) (idx - len div 2)
          v path s"
      and first_lookup:
        "fmlookup (HashMap s) (MerkleNode sibling child) = Some rt"
      using Cons.prems(1) False by auto
    obtain child' where
      child':
        "merkle_path_bound child' (len div 2) (idx - len div 2)
          v path'' s"
      and second_lookup:
        "fmlookup (HashMap s) (MerkleNode sibling' child') = Some rt"
      using Cons.prems(2) False path' by auto
    have node_eq:
      "MerkleNode sibling child = MerkleNode sibling' child'"
    proof (rule ccontr)
      assume neq:
        "MerkleNode sibling child \<noteq> MerkleNode sibling' child'"
      have "hash_map_output_collision s"
        by (rule hash_map_output_collisionI
            [OF neq first_lookup second_lookup])
      then show False using clean by contradiction
    qed
    have child_eq: "child = child'" using node_eq by simp
    have sibling_eq: "sibling = sibling'" using node_eq by simp
    have path_eq: "path = path''"
      by (rule Cons.IH[OF child _ lengths])
        (use child' child_eq in simp)
    show ?thesis
      using path' sibling_eq path_eq by simp
  qed
qed

lemma authenticated_opening_eq_if_clean:
  assumes clean: "\<not> hash_map_output_collision s"
    and first: "authenticated_opening_in s opening"
    and second: "authenticated_opening_in s opening'"
    and same_root: "opening_root opening = opening_root opening'"
    and same_length: "opening_length opening = opening_length opening'"
    and same_index: "opening_index opening = opening_index opening'"
    and same_value: "opening_value opening = opening_value opening'"
  shows "opening = opening'"
proof -
  have path_lengths:
    "length (opening_path opening) = length (opening_path opening')"
    using first second same_length
    unfolding authenticated_opening_in_def by simp
  have first_bound:
    "merkle_path_bound
      (opening_root opening)
      (opening_length opening)
      (opening_index opening)
      (opening_value opening)
      (opening_path opening)
      s"
    using first unfolding authenticated_opening_in_def by blast
  have second_bound:
    "merkle_path_bound
      (opening_root opening)
      (opening_length opening)
      (opening_index opening)
      (opening_value opening)
      (opening_path opening')
      s"
    using second same_root same_length same_index same_value
    unfolding authenticated_opening_in_def by simp
  have paths:
    "opening_path opening = opening_path opening'"
    by (rule merkle_path_bound_unique_path_if_clean
        [OF clean first_bound second_bound path_lengths])
  show ?thesis
    using same_root same_length same_index same_value paths
    by (cases "opening"; cases "opening'"; simp)
qed

lemma accepted_with_partial_trace_openings_same_root_query_openings_eq_if_clean:
  assumes partial:
    "accepted_with_partial_trace_openings s (Some (result, final_state)) fr
      query_idxs trace_openings"
    and partial0:
    "accepted_with_partial_trace_openings s (Some (result, final_state)) fr
      query_idxs trace_openings0"
    and clean: "\<not> hash_map_output_collision final_state"
  shows "trace_openings0 = trace_openings"
proof -
  have len_openings: "length trace_openings = rounds"
    using partial unfolding accepted_with_partial_trace_openings_def by blast
  have len_openings0: "length trace_openings0 = rounds"
    using partial0 unfolding accepted_with_partial_trace_openings_def by blast
  have outer_len: "length trace_openings0 = length trace_openings"
    using len_openings len_openings0 by simp
  have outer_nth:
    "\<And>i. i < length trace_openings0 \<Longrightarrow>
      trace_openings0 ! i = trace_openings ! i"
  proof -
    fix i
    assume i_bound0: "i < length trace_openings0"
    then have i_bound: "i < rounds"
      using len_openings0 by simp
    have idxs:
      "map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
      using partial i_bound
      unfolding accepted_with_partial_trace_openings_def by blast
    have idxs0:
      "map opening_index (trace_openings0 ! i) =
        powers_scaled (query_idxs ! i)"
      using partial0 i_bound
      unfolding accepted_with_partial_trace_openings_def by blast
    have table:
      "partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
      using partial i_bound
      unfolding accepted_with_partial_trace_openings_def by blast
    have table0:
      "partial_authenticated_table fr (scale * clength)
        (trace_openings0 ! i) final_state"
      using partial0 i_bound
      unfolding accepted_with_partial_trace_openings_def by blast
    have len_inner:
      "length (trace_openings0 ! i) = length (trace_openings ! i)"
      using idxs idxs0 by (metis length_map)
  have inner_nth:
    "\<And>j. j < length (trace_openings0 ! i) \<Longrightarrow>
        nth (nth trace_openings0 i) j = nth (nth trace_openings i) j"
    proof -
      fix j
      assume j_bound0: "j < length (trace_openings0 ! i)"
      have j_bound: "j < length (trace_openings ! i)"
        using j_bound0 len_inner by simp
      define opn0 where "opn0 = nth (nth trace_openings0 i) j"
      define opn where "opn = nth (nth trace_openings i) j"
      have opn0_in: "opn0 \<in> set (trace_openings0 ! i)"
        unfolding opn0_def using j_bound0 by simp
      have opn_in: "opn \<in> set (trace_openings ! i)"
        unfolding opn_def using j_bound by simp
      have auth0: "authenticated_opening_in final_state opn0"
        using table0 opn0_in unfolding partial_authenticated_table_def
        by blast
      have auth: "authenticated_opening_in final_state opn"
        using table opn_in unfolding partial_authenticated_table_def
        by blast
      have root0: "opening_root opn0 = fr"
        using table0 opn0_in unfolding partial_authenticated_table_def
        by blast
      have root: "opening_root opn = fr"
        using table opn_in unfolding partial_authenticated_table_def
        by blast
      have length0: "opening_length opn0 = scale * clength"
        using table0 opn0_in unfolding partial_authenticated_table_def
        by blast
      have length: "opening_length opn = scale * clength"
        using table opn_in unfolding partial_authenticated_table_def
        by blast
      have same_index: "opening_index opn0 = opening_index opn"
      proof -
        have "map opening_index (trace_openings0 ! i) ! j =
            map opening_index (trace_openings ! i) ! j"
          using idxs idxs0 by simp
        then show ?thesis
          unfolding opn0_def opn_def using j_bound0 j_bound by simp
      qed
      have same_value: "opening_value opn0 = opening_value opn"
      proof (rule ccontr)
        assume neq: "opening_value opn0 \<noteq> opening_value opn"
        have "hash_map_output_collision final_state"
          by (rule inconsistent_authenticated_openings_imp_hash_collision
              [OF auth0 auth])
            (use root0 root length0 length same_index neq in simp_all)
        then show False using clean by contradiction
      qed
      have opn_eq: "opn0 = opn"
        by (rule authenticated_opening_eq_if_clean[OF clean auth0 auth])
          (use root0 root length0 length same_index same_value in simp_all)
      show "nth (nth trace_openings0 i) j = nth (nth trace_openings i) j"
        using opn_eq unfolding opn0_def opn_def by simp
    qed
    show "trace_openings0 ! i = trace_openings ! i"
      using len_inner inner_nth by (metis nth_equalityI)
  qed
  show ?thesis
    using outer_len outer_nth by (metis nth_equalityI)
qed

lemma trace_fri_header_tied_low_candidate_untied_normalized_openings_gap_imp_hash_collision:
  assumes
    "trace_fri_header_tied_low_candidate_untied_normalized_openings_gap s out"
  shows "hash_map_output_collision_bad s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table fr0 query_idxs0 trace_openings0 trace_table0 where
    partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and partial0:
      "accepted_with_partial_trace_openings s out fr0 query_idxs0
        trace_openings0"
    and root_eq: "fr0 = fr"
    and query_eq: "query_idxs0 = fri_query_idxs"
    and openings_neq: "trace_openings0 \<noteq> trace_openings"
    unfolding
      trace_fri_header_tied_low_candidate_untied_normalized_openings_gap_def
      trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
    by blast
  from partial obtain result final_state where out:
    "out = Some (result, final_state)"
    unfolding accepted_with_partial_trace_openings_def by blast
  show ?thesis
  proof (cases "hash_map_output_collision final_state")
    case True
    then show ?thesis
      unfolding hash_map_output_collision_bad_def accepted_def
      using out by simp
  next
    case clean: False
    have partial_some:
      "accepted_with_partial_trace_openings s (Some (result, final_state))
        fr fri_query_idxs trace_openings"
      using partial out by simp
    have partial0_some:
      "accepted_with_partial_trace_openings s (Some (result, final_state))
        fr fri_query_idxs trace_openings0"
      using partial0 out root_eq query_eq by simp
    have "trace_openings0 = trace_openings"
      by (rule
          accepted_with_partial_trace_openings_same_root_query_openings_eq_if_clean
          [OF partial_some partial0_some clean])
    then show ?thesis
      using openings_neq by contradiction
  qed
qed

lemma trace_fri_header_tied_low_candidate_untied_normalized_openings_gap_mono_hash_collision:
  "wp_event verify_monad
    (trace_fri_header_tied_low_candidate_untied_normalized_openings_gap s) s \<le>
    wp_event verify_monad (hash_map_output_collision_bad s) s"
  by (rule wp_event_mono)
    (rule
      trace_fri_header_tied_low_candidate_untied_normalized_openings_gap_imp_hash_collision)

lemma trace_fri_header_tied_low_candidate_untied_openings_gap_imp_normalized_or_nonnormalized:
  assumes "trace_fri_header_tied_low_candidate_untied_openings_gap s out"
  shows
    "trace_fri_header_tied_low_candidate_untied_normalized_openings_gap s out \<or>
     trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table fr0 query_idxs0 trace_openings0 trace_table0 where
    gap: "trace_fri_reachable_header_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and low: "trace_table_low_degree trace_table"
    and partial0:
      "accepted_with_partial_trace_openings s out fr0 query_idxs0
        trace_openings0"
    and candidate0:
      "partial_trace_table_candidate trace_table0 trace_openings0"
    and not_low0: "\<not> trace_table_low_degree trace_table0"
    and openings_neq: "trace_openings0 \<noteq> trace_openings"
    unfolding trace_fri_header_tied_low_candidate_untied_openings_gap_def
      trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
    by blast
  show ?thesis
  proof (cases "fr0 = fr \<and> query_idxs0 = fri_query_idxs")
    case True
    have "trace_fri_header_tied_low_candidate_untied_normalized_openings_gap
      s out"
      unfolding
        trace_fri_header_tied_low_candidate_untied_normalized_openings_gap_def
      by (rule
          trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI
          [OF gap fri_openings header partial candidate low partial0 candidate0
            not_low0])
        (use True openings_neq in simp)
    then show ?thesis by simp
  next
    case False
    then have diff: "fr0 \<noteq> fr \<or> query_idxs0 \<noteq> fri_query_idxs"
      by blast
    have "trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap
      s out"
      unfolding
        trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_def
      by (rule
          trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI
          [OF gap fri_openings header partial candidate low partial0 candidate0
            not_low0])
        (use diff openings_neq in simp)
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_header_tied_low_candidate_untied_openings_gap_bound_from_hash_and_nonnormalized:
  fixes hash_err nonnormalized_err :: prob
  assumes hash_bound:
    "wp_event verify_monad (hash_map_output_collision_bad s) s \<le>
      hash_err"
    and nonnormalized_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap s)
      s \<le> nonnormalized_err"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_openings_gap s) s \<le>
      hash_err + nonnormalized_err"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_openings_gap s) s \<le>
    wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_low_candidate_untied_normalized_openings_gap
          s out \<or>
        trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap
          s out) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_low_candidate_untied_openings_gap_imp_normalized_or_nonnormalized)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_normalized_openings_gap s)
        s +
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap
          s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> hash_err + nonnormalized_err"
    by (rule add_mono)
      (rule order_trans[
          OF trace_fri_header_tied_low_candidate_untied_normalized_openings_gap_mono_hash_collision
          hash_bound],
       rule nonnormalized_bound)
  finally show ?thesis .
qed

lemma trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_imp_root_or_query:
  assumes
    "trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap
      s out"
  shows
    "trace_fri_header_tied_low_candidate_untied_root_gap s out \<or>
     trace_fri_header_tied_low_candidate_untied_query_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table fr0 query_idxs0 trace_openings0 trace_table0 where
    gap: "trace_fri_reachable_header_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and low: "trace_table_low_degree trace_table"
    and partial0:
      "accepted_with_partial_trace_openings s out fr0 query_idxs0
        trace_openings0"
    and candidate0:
      "partial_trace_table_candidate trace_table0 trace_openings0"
    and not_low0: "\<not> trace_table_low_degree trace_table0"
    and mismatch: "fr0 \<noteq> fr \<or> query_idxs0 \<noteq> fri_query_idxs"
    unfolding
      trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_def
      trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
    by blast
  from mismatch show ?thesis
  proof
    assume root_mismatch: "fr0 \<noteq> fr"
    have "trace_fri_header_tied_low_candidate_untied_root_gap s out"
      unfolding trace_fri_header_tied_low_candidate_untied_root_gap_def
      by (rule
          trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI)
        (rule gap, rule fri_openings, rule header, rule partial,
          rule candidate, rule low, rule partial0, rule candidate0,
          rule not_low0, rule root_mismatch)
    then show ?thesis by simp
  next
    assume query_mismatch: "query_idxs0 \<noteq> fri_query_idxs"
    have "trace_fri_header_tied_low_candidate_untied_query_gap s out"
      unfolding trace_fri_header_tied_low_candidate_untied_query_gap_def
      by (rule
          trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI)
        (rule gap, rule fri_openings, rule header, rule partial,
          rule candidate, rule low, rule partial0, rule candidate0,
          rule not_low0, rule query_mismatch)
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_bound_from_root_query:
  fixes root_err query_err :: prob
  assumes root_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_root_gap s) s \<le>
      root_err"
    and query_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_query_gap s) s \<le>
        query_err"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap s)
      s \<le> root_err + query_err"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap s)
      s \<le>
    wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_low_candidate_untied_root_gap s out \<or>
        trace_fri_header_tied_low_candidate_untied_query_gap s out) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_imp_root_or_query)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_root_gap s) s +
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_query_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> root_err + query_err"
    by (rule add_mono[OF root_bound query_bound])
  finally show ?thesis .
qed

lemma trace_fri_header_tied_low_candidate_untied_root_gap_imp_query_or_openings:
  assumes "trace_fri_header_tied_low_candidate_untied_root_gap s out"
  shows
    "trace_fri_header_tied_low_candidate_untied_query_gap s out \<or>
     trace_fri_header_tied_low_candidate_untied_openings_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table fr0 query_idxs0 trace_openings0 trace_table0 where
    gap: "trace_fri_reachable_header_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and low: "trace_table_low_degree trace_table"
    and partial0:
      "accepted_with_partial_trace_openings s out fr0 query_idxs0
        trace_openings0"
    and candidate0:
      "partial_trace_table_candidate trace_table0 trace_openings0"
    and not_low0: "\<not> trace_table_low_degree trace_table0"
    and root_mismatch: "fr0 \<noteq> fr"
    unfolding trace_fri_header_tied_low_candidate_untied_root_gap_def
      trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
    by blast
  show ?thesis
  proof (cases "query_idxs0 \<noteq> fri_query_idxs")
    case True
    have "trace_fri_header_tied_low_candidate_untied_query_gap s out"
      unfolding trace_fri_header_tied_low_candidate_untied_query_gap_def
      by (rule
          trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI)
        (rule gap, rule fri_openings, rule header, rule partial,
          rule candidate, rule low, rule partial0, rule candidate0,
          rule not_low0, rule True)
    then show ?thesis by simp
  next
    case query_same: False
    show ?thesis
    proof (cases "trace_openings0 \<noteq> trace_openings")
      case True
      have "trace_fri_header_tied_low_candidate_untied_openings_gap s out"
        unfolding trace_fri_header_tied_low_candidate_untied_openings_gap_def
        by (rule
            trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI)
          (rule gap, rule fri_openings, rule header, rule partial,
            rule candidate, rule low, rule partial0, rule candidate0,
            rule not_low0, rule True)
      then show ?thesis by simp
    next
      case openings_same: False
      have same_query: "query_idxs0 = fri_query_idxs"
        using query_same by simp
      have same_openings: "trace_openings0 = trace_openings"
        using openings_same by simp
      have len_openings: "length trace_openings = rounds"
        using partial unfolding accepted_with_partial_trace_openings_def
        by blast
      have idxs0:
        "map opening_index (trace_openings ! 0) =
          powers_scaled (fri_query_idxs ! 0)"
        using partial rounds_positive
        unfolding accepted_with_partial_trace_openings_def by blast
      have nonempty: "trace_openings ! 0 \<noteq> []"
      proof -
        have "powers_scaled (fri_query_idxs ! 0) \<noteq> []"
          unfolding powers_scaled_def using powers_pos by simp
        then show ?thesis
          using idxs0 by auto
      qed
      then obtain opn where opn_in: "opn \<in> set (trace_openings ! 0)"
        by (cases "trace_openings ! 0") auto
      have table:
        "partial_authenticated_table fr (scale * clength)
          (trace_openings ! 0) (snd (the out))"
      proof -
        from partial obtain result final_state where
          out: "out = Some (result, final_state)"
          and table':
            "partial_authenticated_table fr (scale * clength)
              (trace_openings ! 0) final_state"
          using rounds_positive
          unfolding accepted_with_partial_trace_openings_def by blast
        then show ?thesis by simp
      qed
      have table0:
        "partial_authenticated_table fr0 (scale * clength)
          (trace_openings ! 0) (snd (the out))"
      proof -
        from partial0 obtain result final_state where
          out: "out = Some (result, final_state)"
          and table':
            "partial_authenticated_table fr0 (scale * clength)
              (trace_openings0 ! 0) final_state"
          using rounds_positive
          unfolding accepted_with_partial_trace_openings_def by blast
        then show ?thesis
          using same_openings by simp
      qed
      have "opening_root opn = fr"
        using table opn_in unfolding partial_authenticated_table_def by blast
      moreover have "opening_root opn = fr0"
        using table0 opn_in unfolding partial_authenticated_table_def by blast
      ultimately have "fr0 = fr" by simp
      then show ?thesis
        using root_mismatch by contradiction
    qed
  qed
qed

lemma trace_fri_header_tied_low_candidate_untied_gap_imp_query_or_openings:
  assumes
    "trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
  shows
    "trace_fri_header_tied_low_candidate_untied_query_gap s out \<or>
     trace_fri_header_tied_low_candidate_untied_openings_gap s out"
proof -
  have cases:
    "trace_fri_header_tied_low_candidate_untied_root_gap s out \<or>
     trace_fri_header_tied_low_candidate_untied_query_gap s out \<or>
     trace_fri_header_tied_low_candidate_untied_openings_gap s out"
    by (rule
        trace_fri_header_tied_low_candidate_untied_reachable_witness_gap_imp_cases
        [OF assms])
  then show ?thesis
  proof
    assume "trace_fri_header_tied_low_candidate_untied_root_gap s out"
    then show ?thesis
      by (rule
          trace_fri_header_tied_low_candidate_untied_root_gap_imp_query_or_openings)
  next
    assume
      "trace_fri_header_tied_low_candidate_untied_query_gap s out \<or>
       trace_fri_header_tied_low_candidate_untied_openings_gap s out"
    then show ?thesis .
  qed
qed

lemma trace_untied_powers_scaled_eq_imp_eq:
  assumes "powers_scaled idx = powers_scaled idx'"
  shows "idx = idx'"
proof -
  have left: "powers_scaled idx ! 0 = idx"
    unfolding powers_scaled_def using powers_pos by simp
  have right: "powers_scaled idx' ! 0 = idx'"
    unfolding powers_scaled_def using powers_pos by simp
  have "powers_scaled idx ! 0 = powers_scaled idx' ! 0"
    using assms by simp
  then show ?thesis
    using left right by simp
qed

lemma trace_fri_header_tied_low_candidate_untied_query_gap_imp_openings:
  assumes "trace_fri_header_tied_low_candidate_untied_query_gap s out"
  shows "trace_fri_header_tied_low_candidate_untied_openings_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table fr0 query_idxs0 trace_openings0 trace_table0 where
    gap: "trace_fri_reachable_header_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and low: "trace_table_low_degree trace_table"
    and partial0:
      "accepted_with_partial_trace_openings s out fr0 query_idxs0
        trace_openings0"
    and candidate0:
      "partial_trace_table_candidate trace_table0 trace_openings0"
    and not_low0: "\<not> trace_table_low_degree trace_table0"
    and query_mismatch: "query_idxs0 \<noteq> fri_query_idxs"
    unfolding trace_fri_header_tied_low_candidate_untied_query_gap_def
      trace_fri_header_tied_low_candidate_untied_reachable_witness_case_def
    by blast
  show ?thesis
  proof (cases "trace_openings0 \<noteq> trace_openings")
    case True
    show ?thesis
      unfolding trace_fri_header_tied_low_candidate_untied_openings_gap_def
      by (rule
          trace_fri_header_tied_low_candidate_untied_reachable_witness_caseI)
        (rule gap, rule fri_openings, rule header, rule partial,
          rule candidate, rule low, rule partial0, rule candidate0,
          rule not_low0, rule True)
  next
    case openings_same: False
    have same_openings: "trace_openings0 = trace_openings"
      using openings_same by simp
    have len_query: "length fri_query_idxs = rounds"
      using partial unfolding accepted_with_partial_trace_openings_def
      by blast
    have len_query0: "length query_idxs0 = rounds"
      using partial0 unfolding accepted_with_partial_trace_openings_def
      by blast
    have nth_round_eq:
      "\<And>i. i < rounds \<Longrightarrow> query_idxs0 ! i = fri_query_idxs ! i"
    proof -
      fix i
      assume i_bound: "i < rounds"
      have idxs:
        "map opening_index (trace_openings ! i) =
          powers_scaled (fri_query_idxs ! i)"
        using partial i_bound
        unfolding accepted_with_partial_trace_openings_def by blast
      have idxs0:
        "map opening_index (trace_openings0 ! i) =
          powers_scaled (query_idxs0 ! i)"
        using partial0 i_bound
        unfolding accepted_with_partial_trace_openings_def by blast
      have "powers_scaled (query_idxs0 ! i) =
          powers_scaled (fri_query_idxs ! i)"
        using idxs idxs0 same_openings by simp
      then show "query_idxs0 ! i = fri_query_idxs ! i"
        by (rule trace_untied_powers_scaled_eq_imp_eq)
    qed
    have len_eq: "length query_idxs0 = length fri_query_idxs"
      using len_query len_query0 by simp
    have "query_idxs0 = fri_query_idxs"
    proof (rule nth_equalityI)
      show "length query_idxs0 = length fri_query_idxs"
        by (rule len_eq)
    next
      fix i
      assume "i < length query_idxs0"
      then have "i < rounds"
        using len_query0 by simp
      then show "query_idxs0 ! i = fri_query_idxs ! i"
        by (rule nth_round_eq)
    qed
    then show ?thesis
      using query_mismatch by contradiction
  qed
qed

lemma trace_fri_header_tied_low_candidate_untied_gap_imp_openings:
  assumes
    "trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
  shows
    "trace_fri_header_tied_low_candidate_untied_openings_gap s out"
proof -
  have split:
    "trace_fri_header_tied_low_candidate_untied_query_gap s out \<or>
     trace_fri_header_tied_low_candidate_untied_openings_gap s out"
    by (rule
        trace_fri_header_tied_low_candidate_untied_gap_imp_query_or_openings
        [OF assms])
  then show ?thesis
  proof
    assume "trace_fri_header_tied_low_candidate_untied_query_gap s out"
    then show ?thesis
      by (rule
          trace_fri_header_tied_low_candidate_untied_query_gap_imp_openings)
  next
    assume "trace_fri_header_tied_low_candidate_untied_openings_gap s out"
    then show ?thesis .
  qed
qed

lemma trace_fri_header_tied_low_candidate_untied_gap_imp_hash_root_or_query:
  assumes
    "trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
  shows
    "hash_map_output_collision_bad s out \<or>
     trace_fri_header_tied_low_candidate_untied_root_gap s out \<or>
     trace_fri_header_tied_low_candidate_untied_query_gap s out"
proof -
  have openings:
    "trace_fri_header_tied_low_candidate_untied_openings_gap s out"
    by (rule trace_fri_header_tied_low_candidate_untied_gap_imp_openings
        [OF assms])
  have normalized_or:
    "trace_fri_header_tied_low_candidate_untied_normalized_openings_gap
        s out \<or>
     trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap
        s out"
    by (rule
        trace_fri_header_tied_low_candidate_untied_openings_gap_imp_normalized_or_nonnormalized
        [OF openings])
  then show ?thesis
  proof
    assume
      "trace_fri_header_tied_low_candidate_untied_normalized_openings_gap
        s out"
    then have "hash_map_output_collision_bad s out"
      by (rule
          trace_fri_header_tied_low_candidate_untied_normalized_openings_gap_imp_hash_collision)
    then show ?thesis by simp
  next
    assume
      "trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap
        s out"
    then show ?thesis
      using
        trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_imp_root_or_query
      by blast
  qed
qed

lemma wp_trace_fri_header_tied_low_candidate_untied_gap_bound_from_cases:
  fixes root_err query_err opening_err :: prob
  assumes root_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_root_gap s) s \<le>
      root_err"
    and query_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_query_gap s) s \<le>
        query_err"
    and openings_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_openings_gap s) s \<le>
        opening_err"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
      s \<le> root_err + (query_err + opening_err)"
proof -
  have split_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
      s \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_low_candidate_untied_root_gap s out \<or>
          trace_fri_header_tied_low_candidate_untied_query_gap s out \<or>
          trace_fri_header_tied_low_candidate_untied_openings_gap s out)
        s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_low_candidate_untied_reachable_witness_gap_imp_cases)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_root_gap s) s +
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_low_candidate_untied_query_gap s out \<or>
          trace_fri_header_tied_low_candidate_untied_openings_gap s out)
        s"
    by (rule wp_event_union_bound)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_root_gap s) s +
      (wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_query_gap s) s +
       wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_openings_gap s) s)"
    by (intro add_mono order_refl wp_event_union_bound)
  also have "... \<le> root_err + (query_err + opening_err)"
    by (intro add_mono root_bound query_bound openings_bound)
  finally show ?thesis .
qed

lemma wp_trace_fri_header_tied_low_candidate_untied_gap_bound_from_query_and_openings:
  fixes query_err opening_err :: prob
  assumes query_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_query_gap s) s \<le>
        query_err"
    and openings_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_openings_gap s) s \<le>
        opening_err"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
      s \<le> query_err + opening_err"
proof -
  have split_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
      s \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_low_candidate_untied_query_gap s out \<or>
          trace_fri_header_tied_low_candidate_untied_openings_gap s out)
        s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_low_candidate_untied_gap_imp_query_or_openings)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_query_gap s) s +
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_openings_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> query_err + opening_err"
    by (rule add_mono[OF query_bound openings_bound])
  finally show ?thesis .
qed

lemma wp_trace_fri_header_tied_low_candidate_untied_gap_bound_from_openings:
  fixes opening_err :: prob
  assumes openings_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_openings_gap s) s \<le>
      opening_err"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
      s \<le> opening_err"
  by (rule order_trans[OF _ openings_bound])
    (rule wp_event_mono,
      rule trace_fri_header_tied_low_candidate_untied_gap_imp_openings)

lemma trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied_cases:
  fixes header_err merkle_err root_err query_err opening_err :: prob
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
      header_err"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le>
      merkle_err"
    and root_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_root_gap s) s \<le>
        root_err"
    and query_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_query_gap s) s \<le>
        query_err"
    and openings_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_openings_gap s) s \<le>
        opening_err"
    and total_bound:
      "header_err + (merkle_err + (root_err + (query_err + opening_err)))
        \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have untied_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
      s \<le> root_err + (query_err + opening_err)"
    by (rule
        wp_trace_fri_header_tied_low_candidate_untied_gap_bound_from_cases
        [OF root_bound query_bound openings_bound])
  have reduction:
    "trace_fri_reachable_partial_candidate_reduction_assumption s"
    by (rule
        trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied
        [OF header_bound merkle_bound untied_bound])
      (rule total_bound)
  show ?thesis
    by (rule reduction)
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied_openings:
  fixes header_err merkle_err opening_err :: prob
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
      header_err"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le>
      merkle_err"
    and openings_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_openings_gap s) s \<le>
        opening_err"
    and total_bound:
      "header_err + (merkle_err + opening_err) \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have untied_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
      s \<le> opening_err"
    by (rule
        wp_trace_fri_header_tied_low_candidate_untied_gap_bound_from_openings
        [OF openings_bound])
  have reduction:
    "trace_fri_reachable_partial_candidate_reduction_assumption s"
    by (rule
        trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied
        [OF header_bound merkle_bound untied_bound])
      (rule total_bound)
  show ?thesis
    by (rule reduction)
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_header_merkle_hash_and_nonnormalized_openings:
  fixes header_err merkle_err hash_err nonnormalized_err :: prob
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
      header_err"
    and merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le>
      merkle_err"
    and hash_bound:
    "wp_event verify_monad (hash_map_output_collision_bad s) s \<le>
      hash_err"
    and nonnormalized_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap s)
      s \<le> nonnormalized_err"
    and total_bound:
      "header_err + (merkle_err + (hash_err + nonnormalized_err)) \<le>
        trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have openings_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_openings_gap s) s \<le>
      hash_err + nonnormalized_err"
    by (rule
        wp_trace_fri_header_tied_low_candidate_untied_openings_gap_bound_from_hash_and_nonnormalized
        [OF hash_bound nonnormalized_bound])
  show ?thesis
    by (rule
        trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied_openings
        [OF header_bound merkle_bound openings_bound])
      (rule total_bound)
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_header_merkle_hash_root_query:
  fixes header_err merkle_err hash_err root_err query_err :: prob
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
      header_err"
    and merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le>
      merkle_err"
    and hash_bound:
    "wp_event verify_monad (hash_map_output_collision_bad s) s \<le>
      hash_err"
    and root_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_root_gap s) s \<le>
      root_err"
    and query_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_query_gap s) s \<le>
      query_err"
    and total_bound:
      "header_err + (merkle_err + (hash_err + (root_err + query_err))) \<le>
        trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have nonnormalized_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap s)
      s \<le> root_err + query_err"
    by (rule
        wp_trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_bound_from_root_query
        [OF root_bound query_bound])
  show ?thesis
    by (rule
        trace_fri_reachable_partial_candidate_reduction_from_header_merkle_hash_and_nonnormalized_openings
        [OF header_bound merkle_bound hash_bound nonnormalized_bound])
      (rule total_bound)
qed

lemma wp_trace_fri_header_tied_low_candidate_untied_gap_bound_from_hash_root_query:
  fixes hash_err root_err query_err :: prob
  assumes hash_bound:
    "wp_event verify_monad (hash_map_output_collision_bad s) s \<le>
      hash_err"
    and root_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_root_gap s) s \<le>
        root_err"
    and query_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_query_gap s) s \<le>
        query_err"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
      s \<le> hash_err + (root_err + query_err)"
proof -
  have nonnormalized_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap s)
      s \<le> root_err + query_err"
    by (rule
        wp_trace_fri_header_tied_low_candidate_untied_nonnormalized_openings_gap_bound_from_root_query
        [OF root_bound query_bound])
  have openings_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_openings_gap s) s \<le>
      hash_err + (root_err + query_err)"
    by (rule
        wp_trace_fri_header_tied_low_candidate_untied_openings_gap_bound_from_hash_and_nonnormalized
        [OF hash_bound nonnormalized_bound])
  show ?thesis
    by (rule
        wp_trace_fri_header_tied_low_candidate_untied_gap_bound_from_openings
        [OF openings_bound])
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied_query_openings:
  fixes header_err merkle_err query_err opening_err :: prob
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
      header_err"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le>
      merkle_err"
    and query_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_query_gap s) s \<le>
        query_err"
    and openings_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_openings_gap s) s \<le>
        opening_err"
    and total_bound:
      "header_err + (merkle_err + (query_err + opening_err))
        \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have untied_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
      s \<le> query_err + opening_err"
    by (rule
        wp_trace_fri_header_tied_low_candidate_untied_gap_bound_from_query_and_openings
        [OF query_bound openings_bound])
  have reduction:
    "trace_fri_reachable_partial_candidate_reduction_assumption s"
    by (rule
        trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied
        [OF header_bound merkle_bound untied_bound])
      (rule total_bound)
  show ?thesis
    by (rule reduction)
qed

end

end
