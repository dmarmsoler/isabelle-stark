(*  Title:      Stark/Soundness_Alpha_Header_Cross_Candidate.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Alpha_Header_Cross_Candidate
  imports
    Soundness_Alpha_Header_Candidate_Blocker
    Soundness_Partial_Merkle_Cross
begin

text \<open>
  Witnessed alpha-header partial trace candidates.

  This layer keeps verifier outcomes and authenticated opening witnesses
  explicit.  It proves the trace-only analogue of the query-header
  cross-candidate decomposition: if witnessed candidates are not singleton,
  then either pairwise opening coverage fails or a Merkle/collision side
  condition occurs.
\<close>

context soundness
begin

definition alpha_header_supported_partial_trace_table_candidate_witness
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> bool"
where
  "alpha_header_supported_partial_trace_table_candidate_witness s fr
      f_fri_roots f_final trace_table final_state trace_openings \<longleftrightarrow>
    (\<exists>result query_idxs as dg composition_fri_roots final rest.
      Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
      accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest)"

definition alpha_header_supported_witnessed_partial_trace_table_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list set"
where
  "alpha_header_supported_witnessed_partial_trace_table_candidates s fr
      f_fri_roots f_final =
    {trace_table.
      \<exists>final_state trace_openings.
        alpha_header_supported_partial_trace_table_candidate_witness s fr
          f_fri_roots f_final trace_table final_state trace_openings}"

definition alpha_header_supported_witnessed_partial_union_bad_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list set"
where
  "alpha_header_supported_witnessed_partial_union_bad_sets s bad_sets fr
      f_fri_roots f_final =
    {as \<in> alpha_space.
      \<exists>trace_table \<in>
        alpha_header_supported_witnessed_partial_trace_table_candidates s fr
          f_fri_roots f_final.
        as \<in> bad_sets trace_table}"

lemma alpha_header_supported_partial_trace_table_candidate_witness_imp_candidate:
  assumes
    "alpha_header_supported_partial_trace_table_candidate_witness s fr
      f_fri_roots f_final trace_table final_state trace_openings"
  shows
    "trace_table \<in>
      alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
        f_final"
  using assms
  unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    alpha_header_supported_partial_trace_table_candidates_def
  by blast

lemma alpha_header_supported_witnessed_candidates_subset_candidates:
  "alpha_header_supported_witnessed_partial_trace_table_candidates s fr
    f_fri_roots f_final \<subseteq>
   alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
    f_final"
  unfolding alpha_header_supported_witnessed_partial_trace_table_candidates_def
  using alpha_header_supported_partial_trace_table_candidate_witness_imp_candidate
  by blast

lemma alpha_header_supported_partial_trace_table_candidates_subset_witnessed_candidates:
  "alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
    f_final \<subseteq>
   alpha_header_supported_witnessed_partial_trace_table_candidates s fr
    f_fri_roots f_final"
  unfolding alpha_header_supported_partial_trace_table_candidates_def
    alpha_header_supported_witnessed_partial_trace_table_candidates_def
    alpha_header_supported_partial_trace_table_candidate_witness_def
    accepted_with_partial_trace_openings_def
  by blast

lemma alpha_header_supported_witnessed_candidates_eq_candidates:
  "alpha_header_supported_witnessed_partial_trace_table_candidates s fr
    f_fri_roots f_final =
   alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
    f_final"
  using alpha_header_supported_witnessed_candidates_subset_candidates
    alpha_header_supported_partial_trace_table_candidates_subset_witnessed_candidates
  by blast

lemma alpha_header_supported_witnessed_union_bad_sets_subset_union_bad_sets:
  "alpha_header_supported_witnessed_partial_union_bad_sets s bad_sets fr
    f_fri_roots f_final \<subseteq>
   alpha_header_supported_partial_union_bad_sets s bad_sets fr f_fri_roots
    f_final"
  unfolding alpha_header_supported_witnessed_partial_union_bad_sets_def
    alpha_header_supported_partial_union_bad_sets_def
  using alpha_header_supported_witnessed_candidates_subset_candidates
  by blast

lemma alpha_header_supported_union_bad_sets_subset_witnessed_union_bad_sets:
  "alpha_header_supported_partial_union_bad_sets s bad_sets fr f_fri_roots
    f_final \<subseteq>
   alpha_header_supported_witnessed_partial_union_bad_sets s bad_sets fr
    f_fri_roots f_final"
  unfolding alpha_header_supported_witnessed_partial_union_bad_sets_def
    alpha_header_supported_partial_union_bad_sets_def
  using alpha_header_supported_partial_trace_table_candidates_subset_witnessed_candidates
  by blast

lemma alpha_header_supported_witnessed_union_bad_sets_eq_union_bad_sets:
  "alpha_header_supported_witnessed_partial_union_bad_sets s bad_sets fr
    f_fri_roots f_final =
   alpha_header_supported_partial_union_bad_sets s bad_sets fr f_fri_roots
    f_final"
  using alpha_header_supported_witnessed_union_bad_sets_subset_union_bad_sets
    alpha_header_supported_union_bad_sets_subset_witnessed_union_bad_sets
  by blast

lemma alpha_header_partial_candidate_not_prefix_bound_obtain_witness:
  assumes
    "alpha_header_partial_candidate_not_prefix_bound prefix_state s fr
      f_fri_roots f_final"
  obtains trace_table final_state trace_openings where
    "alpha_header_supported_partial_trace_table_candidate_witness s fr
      f_fri_roots f_final trace_table final_state trace_openings"
    "trace_table \<notin> alpha_prefix_trace_table_candidates prefix_state fr"
  using assms
  unfolding alpha_header_partial_candidate_not_prefix_bound_def
  using alpha_header_supported_partial_trace_table_candidates_subset_witnessed_candidates
  unfolding alpha_header_supported_witnessed_partial_trace_table_candidates_def
  by blast

lemma alpha_header_supported_witnessed_partial_trace_table_candidates_obtain_witness:
  assumes
    "trace_table \<in>
      alpha_header_supported_witnessed_partial_trace_table_candidates s fr
        f_fri_roots f_final"
  obtains final_state trace_openings where
    "alpha_header_supported_partial_trace_table_candidate_witness s fr
      f_fri_roots f_final trace_table final_state trace_openings"
  using assms
  unfolding alpha_header_supported_witnessed_partial_trace_table_candidates_def
  by blast

lemma alpha_header_supported_partial_trace_table_candidate_witness_shape:
  assumes
    "alpha_header_supported_partial_trace_table_candidate_witness s fr
      f_fri_roots f_final trace_table final_state trace_openings"
  shows "partial_trace_table_candidate trace_table trace_openings"
  using assms
  unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
  by blast

lemma alpha_header_supported_partial_trace_table_candidate_witness_eq_if_cross_cover_clean_merge:
  assumes witness:
    "alpha_header_supported_partial_trace_table_candidate_witness s fr
      f_fri_roots f_final trace_table final_state trace_openings"
    and witness':
    "alpha_header_supported_partial_trace_table_candidate_witness s fr
      f_fri_roots f_final trace_table' final_state' trace_openings'"
    and trace_cover:
      "partial_openings_cross_cover_all_indices trace_openings
        trace_openings'"
    and no_conflict:
      "\<not> merkle_hash_value_conflict final_state final_state'"
    and clean_merge:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
  shows "trace_table = trace_table'"
proof -
  from witness obtain result query_idxs as dg composition_fri_roots final rest
    where trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    by blast
  from witness' obtain result' query_idxs' as' dg' composition_fri_roots'
      final' rest' where trace_partial':
      "accepted_with_partial_trace_openings s
        (Some (result', final_state')) fr query_idxs' trace_openings'"
    and trace_cand':
      "partial_trace_table_candidate trace_table' trace_openings'"
    unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    by blast
  show ?thesis
    by (rule partial_trace_table_candidates_eq_if_cross_cover_clean_merge
        [OF trace_partial trace_partial' trace_cand trace_cand' trace_cover
          no_conflict clean_merge])
qed

lemma alpha_header_supported_witnessed_partial_trace_table_candidates_subset_singleton_if_pairwise_cross_cover_clean_merge:
  assumes pairwise:
      "\<And>trace_table final_state trace_openings trace_table' final_state'
          trace_openings'.
        alpha_header_supported_partial_trace_table_candidate_witness s fr
          f_fri_roots f_final trace_table final_state trace_openings
        \<Longrightarrow>
        alpha_header_supported_partial_trace_table_candidate_witness s fr
          f_fri_roots f_final trace_table' final_state' trace_openings'
        \<Longrightarrow>
        partial_openings_cross_cover_all_indices trace_openings
          trace_openings' \<and>
        \<not> merkle_hash_value_conflict final_state final_state' \<and>
        \<not> hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table.
      alpha_header_supported_witnessed_partial_trace_table_candidates s fr
        f_fri_roots f_final \<subseteq> {trace_table}"
proof (cases
    "alpha_header_supported_witnessed_partial_trace_table_candidates s fr
      f_fri_roots f_final = {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"]) simp
next
  case False
  then obtain trace_table0 where cand0:
    "trace_table0 \<in>
      alpha_header_supported_witnessed_partial_trace_table_candidates s fr
        f_fri_roots f_final"
    by blast
  from alpha_header_supported_witnessed_partial_trace_table_candidates_obtain_witness
      [OF cand0]
  obtain final_state0 trace_openings0 where witness0:
    "alpha_header_supported_partial_trace_table_candidate_witness s fr
      f_fri_roots f_final trace_table0 final_state0 trace_openings0"
    by blast
  have subset:
    "alpha_header_supported_witnessed_partial_trace_table_candidates s fr
      f_fri_roots f_final \<subseteq> {trace_table0}"
  proof
    fix trace_table
    assume cand:
      "trace_table \<in>
        alpha_header_supported_witnessed_partial_trace_table_candidates s fr
          f_fri_roots f_final"
    from alpha_header_supported_witnessed_partial_trace_table_candidates_obtain_witness
        [OF cand]
    obtain final_state trace_openings where witness:
      "alpha_header_supported_partial_trace_table_candidate_witness s fr
        f_fri_roots f_final trace_table final_state trace_openings"
      by blast
    have pairwise_facts:
      "partial_openings_cross_cover_all_indices trace_openings
        trace_openings0"
      "\<not> merkle_hash_value_conflict final_state final_state0"
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state0)"
      using pairwise[OF witness witness0] by simp_all
    have "trace_table = trace_table0"
      by (rule
          alpha_header_supported_partial_trace_table_candidate_witness_eq_if_cross_cover_clean_merge
          [OF witness witness0 pairwise_facts])
    then show "trace_table \<in> {trace_table0}"
      by simp
  qed
  then show ?thesis
    by blast
qed

lemma alpha_header_supported_witnessed_partial_trace_table_candidates_not_singleton_imp_cross_cover_or_merkle_bad:
  assumes not_unique:
      "\<not> (\<exists>trace_table.
        alpha_header_supported_witnessed_partial_trace_table_candidates s fr
          f_fri_roots f_final \<subseteq> {trace_table})"
  shows
    "\<exists>trace_table final_state trace_openings trace_table' final_state'
        trace_openings'.
      alpha_header_supported_partial_trace_table_candidate_witness s fr
        f_fri_roots f_final trace_table final_state trace_openings \<and>
      alpha_header_supported_partial_trace_table_candidate_witness s fr
        f_fri_roots f_final trace_table' final_state' trace_openings' \<and>
      trace_table \<noteq> trace_table' \<and>
      (\<not> partial_openings_cross_cover_all_indices trace_openings
          trace_openings' \<or>
       merkle_hash_value_conflict final_state final_state' \<or>
       hash_map_output_collision
        (merkle_hash_state_merge final_state final_state'))"
proof -
  let ?C =
    "alpha_header_supported_witnessed_partial_trace_table_candidates s fr
      f_fri_roots f_final"
  have nonempty: "?C \<noteq> {}"
    using not_unique by auto
  then obtain trace_table where cand: "trace_table \<in> ?C"
    by blast
  have not_subset: "\<not> ?C \<subseteq> {trace_table}"
    using not_unique by blast
  then obtain trace_table' where cand': "trace_table' \<in> ?C"
    and distinct: "trace_table \<noteq> trace_table'"
    by auto
  from alpha_header_supported_witnessed_partial_trace_table_candidates_obtain_witness
      [OF cand]
  obtain final_state trace_openings where witness:
    "alpha_header_supported_partial_trace_table_candidate_witness s fr
      f_fri_roots f_final trace_table final_state trace_openings"
    by blast
  from alpha_header_supported_witnessed_partial_trace_table_candidates_obtain_witness
      [OF cand']
  obtain final_state' trace_openings' where witness':
    "alpha_header_supported_partial_trace_table_candidate_witness s fr
      f_fri_roots f_final trace_table' final_state' trace_openings'"
    by blast
  have side:
    "\<not> partial_openings_cross_cover_all_indices trace_openings
        trace_openings' \<or>
     merkle_hash_value_conflict final_state final_state' \<or>
     hash_map_output_collision
      (merkle_hash_state_merge final_state final_state')"
  proof (rule ccontr)
    assume no_side:
      "\<not> (\<not> partial_openings_cross_cover_all_indices trace_openings
          trace_openings' \<or>
       merkle_hash_value_conflict final_state final_state' \<or>
       hash_map_output_collision
        (merkle_hash_state_merge final_state final_state'))"
    have "trace_table = trace_table'"
      by (rule
          alpha_header_supported_partial_trace_table_candidate_witness_eq_if_cross_cover_clean_merge
          [OF witness witness'])
        (use no_side in auto)
    then show False
      using distinct by simp
  qed
  show ?thesis
    using witness witness' distinct side by blast
qed

definition alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> bool"
where
  "alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
      s fr f_fri_roots f_final \<longleftrightarrow>
    (\<exists>trace_table final_state trace_openings trace_table' final_state'
        trace_openings'.
      alpha_header_supported_partial_trace_table_candidate_witness s fr
        f_fri_roots f_final trace_table final_state trace_openings \<and>
      alpha_header_supported_partial_trace_table_candidate_witness s fr
        f_fri_roots f_final trace_table' final_state' trace_openings' \<and>
      trace_table \<noteq> trace_table' \<and>
      (\<not> partial_openings_cross_cover_all_indices trace_openings
          trace_openings' \<or>
       merkle_hash_value_conflict final_state final_state' \<or>
       hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')))"

definition alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad s
    \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final.
      alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
        s fr f_fri_roots f_final)"

lemma alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad_if_not_singleton:
  assumes not_unique:
      "\<not> (\<exists>trace_table.
        alpha_header_supported_witnessed_partial_trace_table_candidates s fr
          f_fri_roots f_final \<subseteq> {trace_table})"
  shows
    "alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
      s fr f_fri_roots f_final"
  unfolding
    alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad_def
  using
    alpha_header_supported_witnessed_partial_trace_table_candidates_not_singleton_imp_cross_cover_or_merkle_bad
      [OF not_unique]
  by blast

lemma alpha_header_supported_witnessed_partial_trace_table_candidates_subset_singleton_if_no_cross_or_merkle_bad:
  assumes no_bad:
      "\<not> alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
        s fr f_fri_roots f_final"
  shows
    "\<exists>trace_table.
      alpha_header_supported_witnessed_partial_trace_table_candidates s fr
        f_fri_roots f_final \<subseteq> {trace_table}"
proof (rule ccontr)
  assume not_unique:
    "\<not> (\<exists>trace_table.
      alpha_header_supported_witnessed_partial_trace_table_candidates s fr
        f_fri_roots f_final \<subseteq> {trace_table})"
  then have
    "alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
      s fr f_fri_roots f_final"
    by (rule
        alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad_if_not_singleton)
  then show False
    using no_bad by contradiction
qed

lemma alpha_header_supported_partial_trace_table_candidates_subset_singleton_if_no_witnessed_cross_or_merkle_bad:
  assumes no_bad:
      "\<not> alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
        s fr f_fri_roots f_final"
  shows
    "\<exists>trace_table.
      alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
        f_final \<subseteq> {trace_table}"
proof -
  have
    "\<exists>trace_table.
      alpha_header_supported_witnessed_partial_trace_table_candidates s fr
        f_fri_roots f_final \<subseteq> {trace_table}"
    by (rule
        alpha_header_supported_witnessed_partial_trace_table_candidates_subset_singleton_if_no_cross_or_merkle_bad
        [OF no_bad])
  moreover have
    "alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
      f_final =
     alpha_header_supported_witnessed_partial_trace_table_candidates s fr
      f_fri_roots f_final"
    using alpha_header_supported_witnessed_candidates_eq_candidates
      [of s fr f_fri_roots f_final]
    by simp
  then show ?thesis
    using calculation by simp
qed

lemma alpha_header_supported_partial_trace_table_candidates_subset_singleton_if_no_global_witnessed_cross_or_merkle_bad:
  assumes no_bad:
      "\<not> alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
        s"
  shows
    "\<exists>trace_table.
      alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
        f_final \<subseteq> {trace_table}"
proof (rule
    alpha_header_supported_partial_trace_table_candidates_subset_singleton_if_no_witnessed_cross_or_merkle_bad)
  show
    "\<not> alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
      s fr f_fri_roots f_final"
    using no_bad
    unfolding
      alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad_def
    by blast
qed

lemma alpha_header_supported_witnessed_partial_union_bad_sets_fraction_bound_if_no_cross_or_merkle_bad:
  fixes C :: prob
  assumes no_bad:
      "\<not> alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
        s fr f_fri_roots f_final"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and bounded:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space) \<le>
        C"
  shows
    "nnreal
      (card
        (alpha_header_supported_witnessed_partial_union_bad_sets s bad_sets
          fr f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le> C"
proof -
  have unique:
    "\<exists>trace_table.
      alpha_header_supported_witnessed_partial_trace_table_candidates s fr
        f_fri_roots f_final \<subseteq> {trace_table}"
    by (rule
        alpha_header_supported_witnessed_partial_trace_table_candidates_subset_singleton_if_no_cross_or_merkle_bad
        [OF no_bad])
  from unique obtain trace_table where candidates:
    "alpha_header_supported_witnessed_partial_trace_table_candidates s fr
      f_fri_roots f_final \<subseteq> {trace_table}"
    by blast
  have union_subset:
    "alpha_header_supported_witnessed_partial_union_bad_sets s bad_sets fr
      f_fri_roots f_final \<subseteq> bad_sets trace_table"
    unfolding alpha_header_supported_witnessed_partial_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (bad_sets trace_table)"
    by (rule finite_subset[OF subset finite_alpha_space])
  have card_le:
    "card
      (alpha_header_supported_witnessed_partial_union_bad_sets s bad_sets fr
        f_fri_roots f_final) \<le> card (bad_sets trace_table)"
    by (rule card_mono[OF finite_bad union_subset])
  have "nnreal
        (card
          (alpha_header_supported_witnessed_partial_union_bad_sets s bad_sets
            fr f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le>
      nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> C"
    by (rule bounded)
  finally show ?thesis .
qed

lemma alpha_header_supported_partial_union_bad_sets_fraction_bound_if_no_witnessed_cross_or_merkle_bad:
  fixes C :: prob
  assumes no_bad:
      "\<not> alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
        s fr f_fri_roots f_final"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and bounded:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space) \<le>
        C"
  shows
    "nnreal
      (card
        (alpha_header_supported_partial_union_bad_sets s bad_sets fr
          f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le> C"
  using
    alpha_header_supported_witnessed_partial_union_bad_sets_fraction_bound_if_no_cross_or_merkle_bad
      [OF no_bad subset bounded]
  by (simp add: alpha_header_supported_witnessed_union_bad_sets_eq_union_bad_sets)

lemma alpha_header_supported_witnessed_partial_union_bad_sets_fraction_bound_if_no_global_cross_or_merkle_bad:
  fixes C :: prob
  assumes no_bad:
      "\<not> alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
        s"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and bounded:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space) \<le>
        C"
  shows
    "nnreal
      (card
        (alpha_header_supported_witnessed_partial_union_bad_sets s bad_sets
          fr f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le> C"
proof -
  have no_header_bad:
    "\<not> alpha_header_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
      s fr f_fri_roots f_final"
    using no_bad
    unfolding
      alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad_def
    by blast
  show ?thesis
    by (rule
        alpha_header_supported_witnessed_partial_union_bad_sets_fraction_bound_if_no_cross_or_merkle_bad
        [OF no_header_bad subset bounded])
qed

lemma alpha_header_supported_partial_union_bad_sets_fraction_bound_if_no_global_witnessed_cross_or_merkle_bad:
  fixes C :: prob
  assumes no_bad:
      "\<not> alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
        s"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and bounded:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space) \<le>
        C"
  shows
    "nnreal
      (card
        (alpha_header_supported_partial_union_bad_sets s bad_sets fr
          f_fri_roots f_final)) /
      nnreal (card alpha_space) \<le> C"
  using
    alpha_header_supported_witnessed_partial_union_bad_sets_fraction_bound_if_no_global_cross_or_merkle_bad
      [OF no_bad subset bounded]
  by (simp add: alpha_header_supported_witnessed_union_bad_sets_eq_union_bad_sets)

lemma wp_alpha_bad_set_hit_bound_if_no_global_witnessed_cross_or_merkle_bad:
  fixes C H :: prob
  assumes future: "alpha_future_fresh s"
    and no_bad:
      "\<not> alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
        s"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and bounded:
      "\<And>trace_table.
        nnreal (card (bad_sets trace_table)) / nnreal (card alpha_space) \<le>
        C"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows "wp_event verify_monad (alpha_bad_set_hit s bad_sets) s \<le> C + H"
proof -
  have unique:
    "\<And>fr f_fri_roots f_final.
      \<exists>trace_table.
        alpha_header_supported_partial_trace_table_candidates s fr
          f_fri_roots f_final \<subseteq> {trace_table}"
    by (rule
        alpha_header_supported_partial_trace_table_candidates_subset_singleton_if_no_global_witnessed_cross_or_merkle_bad
        [OF no_bad])
  show ?thesis
    by (rule
        wp_alpha_bad_set_hit_bound_if_supported_partial_header_candidate_unique_or_collision
        [OF future unique subset bounded collision_bound])
qed

lemma composition_randomization_bad_bound_if_no_global_witnessed_cross_or_merkle_bad:
  fixes H :: prob
  assumes future: "alpha_future_fresh s"
    and no_bad:
      "\<not> alpha_supported_witnessed_partial_trace_pairwise_cross_or_merkle_bad
        s"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (composition_randomization_bad s) s \<le>
      composition_error_bound + H"
proof -
  have unique:
    "\<And>fr f_fri_roots f_final.
      \<exists>trace_table.
        alpha_header_supported_partial_trace_table_candidates s fr
          f_fri_roots f_final \<subseteq> {trace_table}"
    by (rule
        alpha_header_supported_partial_trace_table_candidates_subset_singleton_if_no_global_witnessed_cross_or_merkle_bad
        [OF no_bad])
  show ?thesis
    by (rule
        composition_randomization_bad_bound_if_alpha_header_supported_partial_candidate_unique_or_collision
        [OF future unique collision_bound])
qed

lemma alpha_header_witness_candidate_in_prefix_if_pullback_clean_cover:
  assumes prefix_candidate:
      "prefix_trace_table \<in>
        alpha_prefix_trace_table_candidates prefix_state fr"
    and witness:
      "alpha_header_supported_partial_trace_table_candidate_witness s fr
        f_fri_roots f_final trace_table final_state trace_openings"
    and pullback:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) prefix_state"
    and cover:
      "\<And>j. j < scale * clength \<Longrightarrow>
        \<exists>i < rounds. \<exists>opn \<in> set (trace_openings ! i).
          opening_index opn = j"
    and clean_prefix: "\<not> hash_map_output_collision prefix_state"
  shows
    "trace_table \<in>
      alpha_prefix_trace_table_candidates prefix_state fr"
proof -
  have prefix_len:
    "length prefix_trace_table = clength * scale"
    using prefix_candidate
    unfolding alpha_prefix_trace_table_candidates_def by simp
  have prefix_bind:
    "merkle_root_binds_table fr prefix_trace_table prefix_state"
    using prefix_candidate
    unfolding alpha_prefix_trace_table_candidates_def by simp
  from witness obtain result query_idxs as dg composition_fri_roots final rest
    where trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    by blast
  have prefix_trace_cand:
    "partial_trace_table_candidate prefix_trace_table trace_openings"
  proof -
    obtain n where len_pow: "clength * scale = 2 ^ n"
      using eval_domain_length_power by blast
    have table_pow: "length prefix_trace_table = 2 ^ n"
      using prefix_len len_pow by (simp add: mult.commute)
    have rounds_len: "length trace_openings = rounds"
      using trace_cand unfolding partial_trace_table_candidate_def by simp
    have agrees:
      "\<And>i. i < rounds \<Longrightarrow>
        table_agrees_with_authenticated_openings prefix_trace_table
          (scale * clength) (trace_openings ! i)"
    proof -
      fix i
      assume i_bound: "i < rounds"
      have table_i:
        "partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) prefix_state"
        by (rule pullback[OF i_bound])
      have opening_agrees:
        "\<forall>opn \<in> set (trace_openings ! i).
          opening_index opn < scale * clength \<and>
          prefix_trace_table ! opening_index opn = opening_value opn"
      proof
        fix opn
        assume opn_in: "opn \<in> set (trace_openings ! i)"
        have root: "opening_root opn = fr"
          using table_i opn_in unfolding partial_authenticated_table_def
          by blast
        have len: "opening_length opn = length prefix_trace_table"
          using table_i opn_in prefix_len
          unfolding partial_authenticated_table_def by simp
        have auth: "authenticated_opening_in prefix_state opn"
          using table_i opn_in unfolding partial_authenticated_table_def
          by blast
        have agreement:
          "opening_index opn < length prefix_trace_table \<and>
            prefix_trace_table ! opening_index opn = opening_value opn"
          by (rule merkle_bound_table_agrees_with_authenticated_opening_if_clean
              [OF prefix_bind table_pow auth root len clean_prefix])
        then show
          "opening_index opn < scale * clength \<and>
            prefix_trace_table ! opening_index opn = opening_value opn"
          using prefix_len by (simp add: mult.commute)
      qed
      show
        "table_agrees_with_authenticated_openings prefix_trace_table
          (scale * clength) (trace_openings ! i)"
        unfolding table_agrees_with_authenticated_openings_def
        using prefix_len opening_agrees by simp
    qed
    show ?thesis
      unfolding partial_trace_table_candidate_def
      using prefix_len rounds_len agrees by simp
  qed
  have trace_eq: "trace_table = prefix_trace_table"
    by (rule partial_trace_table_candidate_eq_if_all_indices_opened
        [OF trace_cand prefix_trace_cand cover])
  show ?thesis
    using prefix_candidate unfolding trace_eq .
qed

lemma alpha_header_not_prefix_witness_imp_no_prefix_candidate_or_pullback_gap:
  assumes not_prefix:
      "trace_table \<notin> alpha_prefix_trace_table_candidates prefix_state fr"
    and witness:
      "alpha_header_supported_partial_trace_table_candidate_witness s fr
        f_fri_roots f_final trace_table final_state trace_openings"
    and clean_prefix: "\<not> hash_map_output_collision prefix_state"
    and pullback:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) prefix_state"
    and cover:
      "\<And>j. j < scale * clength \<Longrightarrow>
        \<exists>i < rounds. \<exists>opn \<in> set (trace_openings ! i).
          opening_index opn = j"
  shows
    "alpha_prefix_trace_table_candidates prefix_state fr = {}"
proof (rule ccontr)
  assume "alpha_prefix_trace_table_candidates prefix_state fr \<noteq> {}"
  then obtain prefix_trace_table where prefix_candidate:
    "prefix_trace_table \<in>
      alpha_prefix_trace_table_candidates prefix_state fr"
    by blast
  have
    "trace_table \<in>
      alpha_prefix_trace_table_candidates prefix_state fr"
    by (rule alpha_header_witness_candidate_in_prefix_if_pullback_clean_cover
        [OF prefix_candidate witness pullback cover clean_prefix])
  then show False
    using not_prefix by contradiction
qed

lemma alpha_header_witness_opening_pullback_or_new_output_hit:
  assumes ext: "prefix_state \<le> final_state"
    and witness:
      "alpha_header_supported_partial_trace_table_candidate_witness s fr
        f_fri_roots f_final trace_table final_state trace_openings"
    and i_bound: "i < rounds"
    and opn_in: "opn \<in> set (trace_openings ! i)"
  shows
    "authenticated_opening_in prefix_state opn \<or>
     hash_map_new_output_hit
      (merkle_path_target_roots final_state fr (scale * clength)
        (opening_index opn) (opening_value opn) (opening_path opn))
      prefix_state final_state"
proof -
  from witness obtain result query_idxs as dg composition_fri_roots final rest
    where partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
    by blast
  have table_i:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! i) final_state"
    using partial i_bound
    unfolding accepted_with_partial_trace_openings_def by blast
  show ?thesis
    by (rule partial_authenticated_table_opening_pullback_or_new_output_hit
        [OF ext table_i opn_in])
qed

lemma alpha_header_witness_openings_pullback_or_new_output_hit:
  assumes ext: "prefix_state \<le> final_state"
    and witness:
      "alpha_header_supported_partial_trace_table_candidate_witness s fr
        f_fri_roots f_final trace_table final_state trace_openings"
  shows
    "(\<forall>i < rounds.
        partial_authenticated_table fr (scale * clength)
          (trace_openings ! i) prefix_state) \<or>
     (\<exists>i < rounds. \<exists>opn \<in> set (trace_openings ! i).
        hash_map_new_output_hit
          (merkle_path_target_roots final_state fr (scale * clength)
            (opening_index opn) (opening_value opn) (opening_path opn))
          prefix_state final_state)"
proof (cases
    "\<exists>i < rounds. \<exists>opn \<in> set (trace_openings ! i).
      hash_map_new_output_hit
        (merkle_path_target_roots final_state fr (scale * clength)
          (opening_index opn) (opening_value opn) (opening_path opn))
        prefix_state final_state")
  case True
  then show ?thesis by simp
next
  case False
  have pullback_all:
    "\<forall>i < rounds.
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) prefix_state"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < rounds"
    from witness obtain result query_idxs as dg composition_fri_roots final rest
      where partial:
        "accepted_with_partial_trace_openings s
          (Some (result, final_state)) fr query_idxs trace_openings"
      unfolding alpha_header_supported_partial_trace_table_candidate_witness_def
      by blast
    have table_i:
      "partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
      using partial i_bound
      unfolding accepted_with_partial_trace_openings_def by blast
    show
      "partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) prefix_state"
      unfolding partial_authenticated_table_def
    proof
      fix opn
      assume opn_in: "opn \<in> set (trace_openings ! i)"
      have root_len:
        "opening_root opn = fr \<and> opening_length opn = scale * clength"
        using table_i opn_in unfolding partial_authenticated_table_def
        by blast
      have pullback:
        "authenticated_opening_in prefix_state opn \<or>
         hash_map_new_output_hit
          (merkle_path_target_roots final_state fr (scale * clength)
            (opening_index opn) (opening_value opn) (opening_path opn))
          prefix_state final_state"
        by (rule alpha_header_witness_opening_pullback_or_new_output_hit
            [OF ext witness i_bound opn_in])
      have auth_prefix: "authenticated_opening_in prefix_state opn"
        using pullback False i_bound opn_in by blast
      show
        "opening_root opn = fr \<and>
         opening_length opn = scale * clength \<and>
         authenticated_opening_in prefix_state opn"
        using root_len auth_prefix by simp
    qed
  qed
  then show ?thesis by simp
qed

end

end
