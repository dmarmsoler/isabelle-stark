(*  Title:      Stark/Soundness_Query_Header_Cross_Candidate.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Query_Header_Cross_Candidate
  imports
    Soundness_Reductions_Composition
    Soundness_Partial_Merkle_Cross
begin

text \<open>
  Witnessed query-header partial candidates.

  The public query-header candidate set hides the authenticated opening
  witnesses behind existentials.  This layer exposes those witnesses so that
  the cross-state partial-Merkle binding lemmas can be applied before reducing
  back to the old candidate-set interface.
\<close>

context soundness
begin

definition query_header_supported_partial_table_candidate_witness
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> bool"
where
  "query_header_supported_partial_table_candidate_witness s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state trace_openings composition_openings
    \<longleftrightarrow>
      composition_fri_roots \<noteq> [] \<and>
      (\<exists>result trace_query_idxs composition_query_idxs rest.
        Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
        accepted_with_partial_trace_openings s
          (Some (result, final_state)) fr trace_query_idxs
          trace_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        accepted_with_partial_composition_openings s
          (Some (result, final_state)) (hd composition_fri_roots)
          composition_query_idxs composition_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings \<and>
        verifier_header_transcript s fr f_fri_roots f_final as dg
          composition_fri_roots final rest)"

lemma query_header_supported_partial_table_candidate_witness_imp_state:
  assumes
    "query_header_supported_partial_table_candidate_witness s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state trace_openings composition_openings"
  shows
    "query_header_supported_partial_table_candidate_state s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state"
  using assms
  unfolding query_header_supported_partial_table_candidate_witness_def
    query_header_supported_partial_table_candidate_state_def
  by blast

lemma query_header_supported_partial_table_candidate_state_obtain_witness:
  assumes
    "query_header_supported_partial_table_candidate_state s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state"
  obtains trace_openings composition_openings where
    "query_header_supported_partial_table_candidate_witness s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state trace_openings composition_openings"
  using assms
  unfolding query_header_supported_partial_table_candidate_witness_def
    query_header_supported_partial_table_candidate_state_def
  by blast

lemma query_header_supported_partial_table_candidate_witness_imp_candidate:
  assumes
    "query_header_supported_partial_table_candidate_witness s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state trace_openings composition_openings"
  shows
    "(trace_table, composition_table) \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
  using query_header_supported_partial_table_candidate_witness_imp_state
      [OF assms]
    query_header_supported_partial_table_candidates_iff_state
  by blast

lemma query_header_supported_partial_table_candidates_obtain_witness:
  assumes
    "(trace_table, composition_table) \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
  obtains final_state trace_openings composition_openings where
    "query_header_supported_partial_table_candidate_witness s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state trace_openings composition_openings"
proof -
  from assms obtain final_state where state:
    "query_header_supported_partial_table_candidate_state s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state"
    using query_header_supported_partial_table_candidates_iff_state by blast
  from query_header_supported_partial_table_candidate_state_obtain_witness
      [OF state]
  obtain trace_openings composition_openings where witness:
    "query_header_supported_partial_table_candidate_witness s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state trace_openings composition_openings"
    by blast
  show ?thesis
    by (rule that[OF witness])
qed

lemma query_header_supported_partial_table_candidate_witness_shapes:
  assumes witness:
    "query_header_supported_partial_table_candidate_witness s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state trace_openings composition_openings"
  shows
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table composition_openings"
  using witness
  unfolding query_header_supported_partial_table_candidate_witness_def
  by blast+

lemma query_header_supported_partial_table_candidate_witness_eq_if_cross_cover_clean_merge:
  assumes witness:
    "query_header_supported_partial_table_candidate_witness s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table
      composition_table final_state trace_openings composition_openings"
    and witness':
    "query_header_supported_partial_table_candidate_witness s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table'
      composition_table' final_state' trace_openings' composition_openings'"
    and trace_cover:
      "partial_openings_cross_cover_all_indices trace_openings
        trace_openings'"
    and composition_cover:
      "partial_openings_cross_cover_all_indices composition_openings
        composition_openings'"
    and no_conflict:
      "\<not> merkle_hash_value_conflict final_state final_state'"
    and clean_merge:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
  shows "trace_table = trace_table' \<and> composition_table = composition_table'"
proof -
  from witness obtain result trace_query_idxs composition_query_idxs rest where
    trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    unfolding query_header_supported_partial_table_candidate_witness_def
    by blast
  from witness' obtain result' trace_query_idxs' composition_query_idxs' rest'
    where trace_partial':
      "accepted_with_partial_trace_openings s
        (Some (result', final_state')) fr trace_query_idxs'
        trace_openings'"
    and comp_partial':
      "accepted_with_partial_composition_openings s
        (Some (result', final_state')) (hd composition_fri_roots)
        composition_query_idxs' composition_openings'"
    and trace_cand':
      "partial_trace_table_candidate trace_table' trace_openings'"
    and comp_cand':
      "partial_composition_table_candidate composition_table'
        composition_openings'"
    unfolding query_header_supported_partial_table_candidate_witness_def
    by blast
  have trace_eq: "trace_table = trace_table'"
    by (rule partial_trace_table_candidates_eq_if_cross_cover_clean_merge
        [OF trace_partial trace_partial' trace_cand trace_cand' trace_cover
          no_conflict clean_merge])
  have comp_eq: "composition_table = composition_table'"
    by (rule partial_composition_table_candidates_eq_if_cross_cover_clean_merge
        [OF comp_partial comp_partial' comp_cand comp_cand'
          composition_cover no_conflict clean_merge])
  show ?thesis
    using trace_eq comp_eq by simp
qed

lemma query_header_supported_partial_table_candidates_subset_singleton_if_pairwise_cross_cover_clean_merge:
  assumes pairwise:
      "\<And>trace_table composition_table final_state trace_openings
          composition_openings trace_table' composition_table' final_state'
          trace_openings' composition_openings'.
        query_header_supported_partial_table_candidate_witness s fr
          f_fri_roots f_final as dg composition_fri_roots final trace_table
          composition_table final_state trace_openings composition_openings
        \<Longrightarrow>
        query_header_supported_partial_table_candidate_witness s fr
          f_fri_roots f_final as dg composition_fri_roots final trace_table'
          composition_table' final_state' trace_openings' composition_openings'
        \<Longrightarrow>
        partial_openings_cross_cover_all_indices trace_openings
          trace_openings' \<and>
        partial_openings_cross_cover_all_indices composition_openings
          composition_openings' \<and>
        \<not> merkle_hash_value_conflict final_state final_state' \<and>
        \<not> hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
  shows
    "\<exists>trace_table composition_table.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table, composition_table)}"
proof (cases
    "query_header_supported_partial_table_candidates s fr f_fri_roots
      f_final as dg composition_fri_roots final = {}")
  case True
  then show ?thesis
    by (intro exI[of _ "[]"] exI[of _ "[]"]) simp
next
  case False
  then obtain pair0 where pair0_in:
    "pair0 \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    by blast
  then obtain trace_table0 composition_table0 where pair0_eq:
    "pair0 = (trace_table0, composition_table0)"
    by (cases pair0)
  have cand0:
    "(trace_table0, composition_table0) \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    using pair0_in unfolding pair0_eq .
  from query_header_supported_partial_table_candidates_obtain_witness[OF cand0]
  obtain final_state0 trace_openings0 composition_openings0 where witness0:
    "query_header_supported_partial_table_candidate_witness s fr f_fri_roots
      f_final as dg composition_fri_roots final trace_table0
      composition_table0 final_state0 trace_openings0
      composition_openings0"
    by blast
  have subset:
    "query_header_supported_partial_table_candidates s fr f_fri_roots
      f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)}"
  proof
    fix pair
    assume pair_in:
      "pair \<in>
        query_header_supported_partial_table_candidates s fr f_fri_roots
          f_final as dg composition_fri_roots final"
    obtain trace_table composition_table where pair_eq:
      "pair = (trace_table, composition_table)"
      by (cases pair)
    from query_header_supported_partial_table_candidates_obtain_witness
        [OF pair_in[unfolded pair_eq]]
    obtain final_state trace_openings composition_openings where witness:
      "query_header_supported_partial_table_candidate_witness s fr
        f_fri_roots f_final as dg composition_fri_roots final trace_table
        composition_table final_state trace_openings composition_openings"
      by blast
    have pairwise_facts:
      "partial_openings_cross_cover_all_indices trace_openings
        trace_openings0"
      "partial_openings_cross_cover_all_indices composition_openings
        composition_openings0"
      "\<not> merkle_hash_value_conflict final_state final_state0"
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state0)"
      using pairwise[OF witness witness0] by simp_all
    have eq:
      "trace_table = trace_table0 \<and> composition_table = composition_table0"
      by (rule
          query_header_supported_partial_table_candidate_witness_eq_if_cross_cover_clean_merge
          [OF witness witness0 pairwise_facts])
    show "pair \<in> {(trace_table0, composition_table0)}"
      using pair_eq eq by simp
  qed
  then show ?thesis
    by blast
qed

lemma query_header_supported_partial_table_candidates_not_singleton_imp_cross_cover_or_merkle_bad:
  assumes not_unique:
      "\<not> (\<exists>trace_table composition_table.
        query_header_supported_partial_table_candidates s fr f_fri_roots
          f_final as dg composition_fri_roots final \<subseteq>
        {(trace_table, composition_table)})"
  shows
    "\<exists>trace_table composition_table final_state trace_openings
        composition_openings trace_table' composition_table' final_state'
        trace_openings' composition_openings'.
      query_header_supported_partial_table_candidate_witness s fr
        f_fri_roots f_final as dg composition_fri_roots final trace_table
        composition_table final_state trace_openings composition_openings \<and>
      query_header_supported_partial_table_candidate_witness s fr
        f_fri_roots f_final as dg composition_fri_roots final trace_table'
        composition_table' final_state' trace_openings'
        composition_openings' \<and>
      (trace_table \<noteq> trace_table' \<or>
       composition_table \<noteq> composition_table') \<and>
      (\<not> partial_openings_cross_cover_all_indices trace_openings
          trace_openings' \<or>
       \<not> partial_openings_cross_cover_all_indices composition_openings
          composition_openings' \<or>
       merkle_hash_value_conflict final_state final_state' \<or>
       hash_map_output_collision
        (merkle_hash_state_merge final_state final_state'))"
proof -
  let ?C =
    "query_header_supported_partial_table_candidates s fr f_fri_roots
      f_final as dg composition_fri_roots final"
  have nonempty: "?C \<noteq> {}"
    using not_unique by auto
  then obtain pair where pair_in: "pair \<in> ?C"
    by blast
  obtain trace_table composition_table where pair_eq:
    "pair = (trace_table, composition_table)"
    by (cases pair)
  have cand:
    "(trace_table, composition_table) \<in> ?C"
    using pair_in unfolding pair_eq .
  have not_subset: "\<not> ?C \<subseteq> {(trace_table, composition_table)}"
    using not_unique by blast
  then obtain pair' where pair'_in: "pair' \<in> ?C"
    and pair'_not: "pair' \<notin> {(trace_table, composition_table)}"
    by auto
  obtain trace_table' composition_table' where pair'_eq:
    "pair' = (trace_table', composition_table')"
    by (cases pair')
  have cand':
    "(trace_table', composition_table') \<in> ?C"
    using pair'_in unfolding pair'_eq .
  have distinct:
    "trace_table \<noteq> trace_table' \<or>
     composition_table \<noteq> composition_table'"
    using pair'_not unfolding pair'_eq by auto
  from query_header_supported_partial_table_candidates_obtain_witness[OF cand]
  obtain final_state trace_openings composition_openings where witness:
    "query_header_supported_partial_table_candidate_witness s fr
      f_fri_roots f_final as dg composition_fri_roots final trace_table
      composition_table final_state trace_openings composition_openings"
    by blast
  from query_header_supported_partial_table_candidates_obtain_witness[OF cand']
  obtain final_state' trace_openings' composition_openings' where witness':
    "query_header_supported_partial_table_candidate_witness s fr
      f_fri_roots f_final as dg composition_fri_roots final trace_table'
      composition_table' final_state' trace_openings'
      composition_openings'"
    by blast
  have side:
    "\<not> partial_openings_cross_cover_all_indices trace_openings
        trace_openings' \<or>
     \<not> partial_openings_cross_cover_all_indices composition_openings
        composition_openings' \<or>
     merkle_hash_value_conflict final_state final_state' \<or>
     hash_map_output_collision
      (merkle_hash_state_merge final_state final_state')"
  proof (rule ccontr)
    assume no_side:
      "\<not> (\<not> partial_openings_cross_cover_all_indices trace_openings
          trace_openings' \<or>
       \<not> partial_openings_cross_cover_all_indices composition_openings
          composition_openings' \<or>
       merkle_hash_value_conflict final_state final_state' \<or>
       hash_map_output_collision
        (merkle_hash_state_merge final_state final_state'))"
    have eq:
      "trace_table = trace_table' \<and>
       composition_table = composition_table'"
      by (rule
          query_header_supported_partial_table_candidate_witness_eq_if_cross_cover_clean_merge
          [OF witness witness'])
        (use no_side in auto)
    then show False
      using distinct by simp
  qed
  show ?thesis
    using witness witness' distinct side by blast
qed

definition query_header_supported_partial_pairwise_cross_or_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> bool"
where
  "query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
      f_fri_roots f_final as dg composition_fri_roots final \<longleftrightarrow>
    (\<exists>trace_table composition_table final_state trace_openings
        composition_openings trace_table' composition_table' final_state'
        trace_openings' composition_openings'.
      query_header_supported_partial_table_candidate_witness s fr
        f_fri_roots f_final as dg composition_fri_roots final trace_table
        composition_table final_state trace_openings composition_openings \<and>
      query_header_supported_partial_table_candidate_witness s fr
        f_fri_roots f_final as dg composition_fri_roots final trace_table'
        composition_table' final_state' trace_openings'
        composition_openings' \<and>
      (trace_table \<noteq> trace_table' \<or>
       composition_table \<noteq> composition_table') \<and>
      (\<not> partial_openings_cross_cover_all_indices trace_openings
          trace_openings' \<or>
       \<not> partial_openings_cross_cover_all_indices composition_openings
          composition_openings' \<or>
       merkle_hash_value_conflict final_state final_state' \<or>
       hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')))"

definition query_supported_partial_pairwise_cross_or_merkle_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "query_supported_partial_pairwise_cross_or_merkle_bad s \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final.
      query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
        f_fri_roots f_final as dg composition_fri_roots final)"

lemma query_header_supported_partial_pairwise_cross_or_merkle_bad_if_not_singleton:
  assumes not_unique:
      "\<not> (\<exists>trace_table composition_table.
        query_header_supported_partial_table_candidates s fr f_fri_roots
          f_final as dg composition_fri_roots final \<subseteq>
        {(trace_table, composition_table)})"
  shows
    "query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
      f_fri_roots f_final as dg composition_fri_roots final"
  unfolding query_header_supported_partial_pairwise_cross_or_merkle_bad_def
  using
    query_header_supported_partial_table_candidates_not_singleton_imp_cross_cover_or_merkle_bad
      [OF not_unique]
  by blast

lemma query_header_supported_partial_table_candidates_subset_singleton_if_no_cross_or_merkle_bad:
  assumes no_bad:
      "\<not> query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
        f_fri_roots f_final as dg composition_fri_roots final"
  shows
    "\<exists>trace_table composition_table.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table, composition_table)}"
proof (rule ccontr)
  assume not_unique:
    "\<not> (\<exists>trace_table composition_table.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table, composition_table)})"
  then have
    "query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
      f_fri_roots f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_pairwise_cross_or_merkle_bad_def
    using
      query_header_supported_partial_table_candidates_not_singleton_imp_cross_cover_or_merkle_bad
    by blast
  then show False
    using no_bad by contradiction
qed

lemma query_supported_partial_pairwise_cross_or_merkle_badD:
  assumes
    "query_supported_partial_pairwise_cross_or_merkle_bad s"
  obtains fr f_fri_roots f_final as dg composition_fri_roots final where
    "query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
      f_fri_roots f_final as dg composition_fri_roots final"
  using assms
  unfolding query_supported_partial_pairwise_cross_or_merkle_bad_def by blast

lemma query_header_supported_partial_table_candidates_subset_singleton_if_no_global_cross_or_merkle_bad:
  assumes no_bad:
      "\<not> query_supported_partial_pairwise_cross_or_merkle_bad s"
  shows
    "\<exists>trace_table composition_table.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table, composition_table)}"
proof (rule
    query_header_supported_partial_table_candidates_subset_singleton_if_no_cross_or_merkle_bad)
  show
    "\<not> query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
      f_fri_roots f_final as dg composition_fri_roots final"
    using no_bad
    unfolding query_supported_partial_pairwise_cross_or_merkle_bad_def by blast
qed

lemma query_header_supported_partial_union_good_sets_fraction_bound_if_no_cross_or_merkle_bad:
  assumes no_bad:
      "\<not> query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
        f_fri_roots f_final as dg composition_fri_roots final"
    and subset:
      "\<And>trace_table composition_table as.
        good_sets trace_table composition_table as \<subseteq> query_sample_space"
    and bounded:
      "\<And>trace_table composition_table as.
        nnreal (card (good_sets trace_table composition_table as)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
  shows
    "nnreal
      (card
        (query_header_supported_partial_union_good_sets s good_sets fr
          f_fri_roots f_final as dg composition_fri_roots final)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
proof -
  have unique:
    "\<exists>trace_table composition_table.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table, composition_table)}"
    by (rule
        query_header_supported_partial_table_candidates_subset_singleton_if_no_cross_or_merkle_bad
        [OF no_bad])
  show ?thesis
    by (rule
        query_header_supported_partial_union_good_sets_fraction_bound_if_unique_candidate
        [OF unique subset bounded])
qed

lemma query_header_supported_partial_union_good_sets_fraction_bound_if_no_global_cross_or_merkle_bad:
  assumes no_bad:
      "\<not> query_supported_partial_pairwise_cross_or_merkle_bad s"
    and subset:
      "\<And>trace_table composition_table as.
        good_sets trace_table composition_table as \<subseteq> query_sample_space"
    and bounded:
      "\<And>trace_table composition_table as.
        nnreal (card (good_sets trace_table composition_table as)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
  shows
    "nnreal
      (card
        (query_header_supported_partial_union_good_sets s good_sets fr
          f_fri_roots f_final as dg composition_fri_roots final)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
proof (rule
    query_header_supported_partial_union_good_sets_fraction_bound_if_no_cross_or_merkle_bad
    [OF _ subset bounded])
  show
    "\<not> query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
      f_fri_roots f_final as dg composition_fri_roots final"
    using no_bad
    unfolding query_supported_partial_pairwise_cross_or_merkle_bad_def by blast
qed

lemma wp_query_index_round_set_hit_bound_if_no_global_cross_or_merkle_bad:
  fixes H :: prob
  assumes future: "query_future_fresh s"
    and raw_bound: "query_index_raw_preimage_bound"
    and no_bad:
      "\<not> query_supported_partial_pairwise_cross_or_merkle_bad s"
    and subset:
      "\<And>trace_table composition_table as.
        good_sets trace_table composition_table as \<subseteq> query_sample_space"
    and bounded:
      "\<And>trace_table composition_table as.
        nnreal (card (good_sets trace_table composition_table as)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
    and collision_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> H"
  shows
    "wp_event verify_monad (query_index_round_set_hit s good_sets) s \<le>
      nnreal rounds * query_error_bound + H"
proof (rule
    wp_query_index_round_set_hit_bound_via_supported_partial_union_or_collision
    [OF future raw_bound _ collision_bound])
  fix fr f_fri_roots f_final as dg composition_fri_roots final
  show
    "nnreal
      (card
        (query_header_supported_partial_union_good_sets s good_sets fr
          f_fri_roots f_final as dg composition_fri_roots final)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
    by (rule
        query_header_supported_partial_union_good_sets_fraction_bound_if_no_global_cross_or_merkle_bad
        [OF no_bad subset bounded])
qed

end

end
