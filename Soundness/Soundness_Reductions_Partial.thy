(*  Title:      Stark/Soundness_Reductions_Partial.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Reductions_Partial
  imports Soundness_Reductions_Side
begin

text \<open>Partial-opening bad-event definitions and accepted-execution partitions.\<close>

context soundness
begin

text \<open>
  Reachable-state FRI interfaces for the partial-opening proof path.  These
  predicates express the verifier-local FRI low-degree reductions over
  authenticated partial openings and deliberately avoid complete-table
  witnesses in their statement.
\<close>

definition trace_fri_partial_opening_reduction_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "trace_fri_partial_opening_reduction_assumption s \<longleftrightarrow>
      wp_event verify_monad (trace_fri_bad_with_partial_openings s) s \<le>
        trace_fri_error"

definition composition_fri_partial_opening_reduction_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "composition_fri_partial_opening_reduction_assumption s \<longleftrightarrow>
      wp_event verify_monad
        (composition_fri_bad_with_partial_openings s) s \<le>
        composition_fri_error"

lemma trace_fri_bad_with_partial_openings_bound_from_partial_reduction:
  assumes "trace_fri_partial_opening_reduction_assumption s"
  shows "wp_event verify_monad (trace_fri_bad_with_partial_openings s) s \<le>
    trace_fri_error"
  using assms unfolding trace_fri_partial_opening_reduction_assumption_def
  by simp

lemma composition_fri_bad_with_partial_openings_bound_from_partial_reduction:
  assumes "composition_fri_partial_opening_reduction_assumption s"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_partial_openings s) s \<le>
      composition_fri_error"
  using assms
  unfolding composition_fri_partial_opening_reduction_assumption_def by simp

lemma trace_fri_bad_with_partial_openings_imp_trace_fri_bad:
  assumes "trace_fri_bad_with_partial_openings s out"
  shows "trace_fri_bad s out"
  using assms unfolding trace_fri_bad_with_partial_openings_def by simp

lemma composition_fri_bad_with_partial_openings_imp_composition_fri_bad:
  assumes "composition_fri_bad_with_partial_openings s out"
  shows "composition_fri_bad s out"
  using assms unfolding composition_fri_bad_with_partial_openings_def by simp

lemma wp_trace_fri_bad_with_partial_openings_le_trace_fri_bad:
  "wp_event verify_monad (trace_fri_bad_with_partial_openings s) s \<le>
    wp_event verify_monad (trace_fri_bad s) s"
  by (rule wp_event_mono)
    (rule trace_fri_bad_with_partial_openings_imp_trace_fri_bad)

lemma wp_composition_fri_bad_with_partial_openings_le_composition_fri_bad:
  "wp_event verify_monad (composition_fri_bad_with_partial_openings s) s \<le>
    wp_event verify_monad (composition_fri_bad s) s"
  by (rule wp_event_mono)
    (rule composition_fri_bad_with_partial_openings_imp_composition_fri_bad)

lemma trace_fri_bad_with_tables_imp_partial_openings_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and bad: "trace_fri_bad_with_tables s out"
  shows "trace_fri_bad_with_partial_openings s out"
proof -
  have tables: "accepted_with_fri_tables s out"
    using bad unfolding trace_fri_bad_with_tables_def by simp
  have accepted: "accepted out"
    by (rule accepted_with_fri_tables_imp_accepted[OF tables])
  then obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  from verify_monad_accepted_with_partial_trace_openings
      [OF support[unfolded out_eq]]
  obtain fr query_idxs trace_openings where partial:
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr query_idxs trace_openings"
    by blast
  have trace_bad: "trace_fri_bad s out"
    using bad unfolding trace_fri_bad_with_tables_def by simp
  show ?thesis
    unfolding trace_fri_bad_with_partial_openings_def out_eq
    using trace_bad[unfolded out_eq] partial by blast
qed

lemma composition_fri_bad_with_tables_imp_partial_openings_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and bad: "composition_fri_bad_with_tables s out"
  shows "composition_fri_bad_with_partial_openings s out"
proof -
  have tables: "accepted_with_fri_tables s out"
    using bad unfolding composition_fri_bad_with_tables_def by simp
  have accepted: "accepted out"
    by (rule accepted_with_fri_tables_imp_accepted[OF tables])
  then obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  from verify_monad_accepted_with_partial_trace_openings
      [OF support[unfolded out_eq]]
  obtain fr query_idxs trace_openings where partial:
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr query_idxs trace_openings"
    by blast
  have composition_bad: "composition_fri_bad s out"
    using bad unfolding composition_fri_bad_with_tables_def by simp
  show ?thesis
    unfolding composition_fri_bad_with_partial_openings_def out_eq
    using composition_bad[unfolded out_eq] partial by blast
qed

lemma wp_trace_fri_bad_with_tables_le_partial_openings:
  "wp_event verify_monad (trace_fri_bad_with_tables s) s \<le>
    wp_event verify_monad (trace_fri_bad_with_partial_openings s) s"
  by (rule wp_event_mono_on_support)
    (rule trace_fri_bad_with_tables_imp_partial_openings_on_support)

lemma wp_composition_fri_bad_with_tables_le_partial_openings:
  "wp_event verify_monad (composition_fri_bad_with_tables s) s \<le>
    wp_event verify_monad (composition_fri_bad_with_partial_openings s) s"
  by (rule wp_event_mono_on_support)
    (rule composition_fri_bad_with_tables_imp_partial_openings_on_support)

definition soundness_bad_event_table_aware
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "soundness_bad_event_table_aware s out \<longleftrightarrow>
      composition_bad s out \<or>
      trace_fri_bad_with_tables s out \<or>
      composition_fri_bad_with_tables s out \<or>
      query_bad s out"

definition soundness_bad_event_partial_opening
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "soundness_bad_event_partial_opening s out \<longleftrightarrow>
      composition_bad s out \<or>
      trace_fri_bad_with_partial_openings s out \<or>
      composition_fri_bad_with_partial_openings s out \<or>
      query_bad s out"

definition soundness_bad_event_table_aware_with_merkle
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "soundness_bad_event_table_aware_with_merkle s out \<longleftrightarrow>
      fri_merkle_binding_bad s out \<or>
      soundness_bad_event_table_aware s out"

definition soundness_bad_event_partial_opening_with_merkle
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "soundness_bad_event_partial_opening_with_merkle s out \<longleftrightarrow>
      fri_merkle_binding_bad s out \<or>
      soundness_bad_event_partial_opening s out"

definition soundness_bad_event_partial_opening_with_initial_merkle
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "soundness_bad_event_partial_opening_with_initial_merkle s out \<longleftrightarrow>
      initial_merkle_binding_bad s out \<or>
      soundness_bad_event_partial_opening s out"

definition soundness_bad_event_partial_opening_with_partial_merkle
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "soundness_bad_event_partial_opening_with_partial_merkle s out \<longleftrightarrow>
      partial_merkle_inconsistency_bad s out \<or>
      soundness_bad_event_partial_opening s out"

definition composition_bad_with_partial_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_bad_with_partial_candidates s out \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
          trace_query_idxs trace_openings composition_query_idxs
          composition_openings trace_table composition_table f.
        accepted_with_partial_initial_openings s out fr f_fri_roots f_final
          as dg composition_fri_roots final trace_query_idxs trace_openings
          composition_query_idxs composition_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings \<and>
        degree f < clength \<and>
        trace_table = map (poly f) eval_domain \<and>
        violated_constraints f \<noteq> {} \<and>
        composition_table_low_degree maxDegree composition_table \<and>
        all_queries_consistent trace_table composition_table as)"

definition composition_degree_bad_with_partial_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_degree_bad_with_partial_candidates s out \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
          trace_query_idxs trace_openings composition_query_idxs
          composition_openings trace_table composition_table f.
        accepted_with_partial_initial_openings s out fr f_fri_roots f_final
          as dg composition_fri_roots final trace_query_idxs trace_openings
          composition_query_idxs composition_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings \<and>
        degree f < clength \<and>
        trace_table = map (poly f) eval_domain \<and>
        violated_constraints f \<noteq> {} \<and>
        composition_table_low_degree maxDegree composition_table \<and>
        all_queries_consistent trace_table composition_table as \<and>
        \<not> common_denominator_degree_bounds f as)"

definition composition_randomization_bad_with_partial_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_randomization_bad_with_partial_candidates s out \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
          trace_query_idxs trace_openings composition_query_idxs
          composition_openings trace_table composition_table f.
        accepted_with_partial_initial_openings s out fr f_fri_roots f_final
          as dg composition_fri_roots final trace_query_idxs trace_openings
          composition_query_idxs composition_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings \<and>
        degree f < clength \<and>
        trace_table = map (poly f) eval_domain \<and>
        violated_constraints f \<noteq> {} \<and>
        composition_table_low_degree maxDegree composition_table \<and>
        all_queries_consistent trace_table composition_table as \<and>
        common_denominator_degree_bounds f as \<and>
        random_combination_common_denominator_hides_violations f as)"

definition trace_fri_bad_with_partial_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_bad_with_partial_candidates s out \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
          trace_query_idxs trace_openings composition_query_idxs
          composition_openings trace_table.
        accepted_with_partial_initial_openings s out fr f_fri_roots f_final
          as dg composition_fri_roots final trace_query_idxs trace_openings
          composition_query_idxs composition_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        \<not> trace_table_low_degree trace_table)"

definition composition_fri_bad_with_partial_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "composition_fri_bad_with_partial_candidates s out \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
          trace_query_idxs trace_openings composition_query_idxs
          composition_openings trace_table composition_table.
        accepted_with_partial_initial_openings s out fr f_fri_roots f_final
          as dg composition_fri_roots final trace_query_idxs trace_openings
          composition_query_idxs composition_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings \<and>
        trace_table_low_degree trace_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table)"

definition query_bad_with_partial_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "query_bad_with_partial_candidates s out \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
          trace_query_idxs trace_openings composition_query_idxs
          composition_openings trace_table composition_table.
        accepted_with_partial_initial_openings s out fr f_fri_roots f_final
          as dg composition_fri_roots final trace_query_idxs trace_openings
          composition_query_idxs composition_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings \<and>
        trace_table_low_degree trace_table \<and>
        composition_table_low_degree maxDegree composition_table \<and>
        \<not> all_queries_consistent trace_table composition_table as)"

definition soundness_bad_event_partial_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "soundness_bad_event_partial_candidate s out \<longleftrightarrow>
      composition_bad_with_partial_candidates s out \<or>
      trace_fri_bad_with_partial_candidates s out \<or>
      composition_fri_bad_with_partial_candidates s out \<or>
      query_bad_with_partial_candidates s out"

definition soundness_bad_event_partial_candidate_with_partial_merkle
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "soundness_bad_event_partial_candidate_with_partial_merkle s out \<longleftrightarrow>
      partial_merkle_inconsistency_bad s out \<or>
      soundness_bad_event_partial_candidate s out"

definition accepted_with_empty_composition_header_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      'f \<Rightarrow> nat list \<Rightarrow> 'f authenticated_opening list list \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> bool"
where
  "accepted_with_empty_composition_header_candidates s out fr f_fri_roots
      f_final as dg final trace_query_idxs trace_openings trace_table
      composition_table \<longleftrightarrow>
    accepted out \<and>
    (\<exists>rest.
      verifier_header_transcript s fr f_fri_roots f_final as dg []
        final rest) \<and>
    accepted_with_partial_trace_openings s out fr trace_query_idxs
      trace_openings \<and>
    partial_trace_table_candidate trace_table trace_openings \<and>
    composition_table = replicate (scale * clength) final"

definition composition_bad_with_empty_composition_header_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_bad_with_empty_composition_header_candidates s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table f.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      degree f < clength \<and>
      trace_table = map (poly f) eval_domain \<and>
      violated_constraints f \<noteq> {} \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as)"

definition composition_degree_bad_with_empty_composition_header_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_degree_bad_with_empty_composition_header_candidates s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table f.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      degree f < clength \<and>
      trace_table = map (poly f) eval_domain \<and>
      violated_constraints f \<noteq> {} \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as \<and>
      \<not> common_denominator_degree_bounds f as)"

definition composition_randomization_bad_with_empty_composition_header_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_randomization_bad_with_empty_composition_header_candidates s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table f.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      degree f < clength \<and>
      trace_table = map (poly f) eval_domain \<and>
      violated_constraints f \<noteq> {} \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as \<and>
      common_denominator_degree_bounds f as \<and>
      random_combination_common_denominator_hides_violations f as)"

definition composition_alpha_bad_set_hit_with_empty_composition_header_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_alpha_bad_set_hit_with_empty_composition_header_candidates s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      as \<in> composition_trace_bad_alpha_space trace_table)"

definition composition_alpha_bad_set_hit_with_partial_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_alpha_bad_set_hit_with_partial_candidates s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table.
      accepted_with_partial_initial_openings s out fr f_fri_roots f_final
        as dg composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      as \<in> composition_trace_bad_alpha_space trace_table)"

definition partial_trace_opening_alpha_union_bad_sets
  :: "'f authenticated_opening list list \<Rightarrow> 'f list set"
where
  "partial_trace_opening_alpha_union_bad_sets trace_openings =
    (\<Union>trace_table \<in> partial_trace_table_candidates trace_openings.
      composition_trace_bad_alpha_space trace_table)"

definition composition_alpha_partial_opening_union_hit_with_empty_header
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_alpha_partial_opening_union_hit_with_empty_header s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      as \<in> partial_trace_opening_alpha_union_bad_sets trace_openings)"

lemma partial_trace_opening_alpha_union_bad_sets_subset_alpha_space:
  "partial_trace_opening_alpha_union_bad_sets trace_openings \<subseteq>
    alpha_space"
  unfolding partial_trace_opening_alpha_union_bad_sets_def
  using composition_trace_bad_alpha_space_subset_alpha_space by auto

lemma partial_trace_opening_alpha_union_bad_sets_finite:
  "finite (partial_trace_opening_alpha_union_bad_sets trace_openings)"
  by (rule finite_subset
      [OF partial_trace_opening_alpha_union_bad_sets_subset_alpha_space
        finite_alpha_space])

lemma partial_trace_opening_alpha_union_bad_sets_fraction_bound_if_unique_candidate:
  assumes unique:
    "\<exists>trace_table.
      partial_trace_table_candidates trace_openings \<subseteq> {trace_table}"
  shows
    "nnreal
      (card (partial_trace_opening_alpha_union_bad_sets trace_openings)) /
      nnreal (card alpha_space) \<le> composition_error_bound"
proof -
  from unique obtain trace_table where candidates:
    "partial_trace_table_candidates trace_openings \<subseteq> {trace_table}"
    by blast
  have union_subset:
    "partial_trace_opening_alpha_union_bad_sets trace_openings \<subseteq>
      composition_trace_bad_alpha_space trace_table"
    unfolding partial_trace_opening_alpha_union_bad_sets_def
    using candidates by auto
  have finite_bad: "finite (composition_trace_bad_alpha_space trace_table)"
    by (rule finite_subset
        [OF composition_trace_bad_alpha_space_subset_alpha_space
          finite_alpha_space])
  have "card (partial_trace_opening_alpha_union_bad_sets trace_openings) \<le>
      card (composition_trace_bad_alpha_space trace_table)"
    by (rule card_mono[OF finite_bad union_subset])
  then have
    "nnreal
      (card (partial_trace_opening_alpha_union_bad_sets trace_openings)) /
      nnreal (card alpha_space) \<le>
      nnreal (card (composition_trace_bad_alpha_space trace_table)) /
      nnreal (card alpha_space)"
    by (rule nnreal_nat_divide_right_mono)
  also have "... \<le> composition_error_bound"
    by (rule composition_trace_bad_alpha_space_fraction_bound_alpha_space)
  finally show ?thesis .
qed

lemma composition_alpha_bad_set_hit_with_empty_header_imp_partial_opening_union_hit:
  assumes
    "composition_alpha_bad_set_hit_with_empty_composition_header_candidates
      s out"
  shows
    "composition_alpha_partial_opening_union_hit_with_empty_header s out"
proof -
  obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table where partial:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and as_bad: "as \<in> composition_trace_bad_alpha_space trace_table"
    using assms
    unfolding
      composition_alpha_bad_set_hit_with_empty_composition_header_candidates_def
    by blast
  have candidate:
    "trace_table \<in> partial_trace_table_candidates trace_openings"
    using partial
    unfolding accepted_with_empty_composition_header_candidates_def
      partial_trace_table_candidates_def
    by simp
  have
    "as \<in> partial_trace_opening_alpha_union_bad_sets trace_openings"
    unfolding partial_trace_opening_alpha_union_bad_sets_def
    using candidate as_bad by blast
  then show ?thesis
    unfolding composition_alpha_partial_opening_union_hit_with_empty_header_def
    using partial by blast
qed

lemma wp_composition_alpha_bad_set_hit_with_empty_header_le_partial_opening_union_hit:
  "wp_event verify_monad
      (composition_alpha_bad_set_hit_with_empty_composition_header_candidates s)
      s \<le>
    wp_event verify_monad
      (composition_alpha_partial_opening_union_hit_with_empty_header s) s"
  by (rule wp_event_mono)
    (rule
      composition_alpha_bad_set_hit_with_empty_header_imp_partial_opening_union_hit)

lemma composition_alpha_partial_opening_union_hit_with_empty_header_imp_alpha_header_partial_union_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and hit:
      "composition_alpha_partial_opening_union_hit_with_empty_header s out"
  shows
    "alpha_header_list_set_hit s
      (alpha_header_supported_partial_union_bad_sets s
        composition_trace_bad_alpha_space) out"
proof -
  obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table rest where partial:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg []
        final rest"
    and trace_partial:
      "accepted_with_partial_trace_openings s out fr trace_query_idxs
        trace_openings"
    and as_bad:
      "as \<in> partial_trace_opening_alpha_union_bad_sets trace_openings"
    using hit
    unfolding composition_alpha_partial_opening_union_hit_with_empty_header_def
      accepted_with_empty_composition_header_candidates_def
    by blast
  from trace_partial obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_with_partial_trace_openings_def by blast
  from verify_monad_accepted_transcript_shape[OF support[unfolded out_eq]]
  obtain as' query_idxs where shape':
    "accepted_transcript_shape s (Some (result, final_state)) as' query_idxs"
    by blast
  from shape' obtain result' final_state' fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where out_shape:
      "Some (result, final_state) = Some (result', final_state')"
    and header':
      "verifier_header_transcript s fr' f_fri_roots' f_final' as' dg'
        composition_fri_roots' final' rest'"
    by (elim accepted_transcript_shape_header_query_extraction)
  have as'_eq: "as' = as"
    using verifier_header_transcript_unique[OF header' header] by simp
  have shape:
    "accepted_transcript_shape s out as query_idxs"
    using shape' as'_eq out_eq by simp
  from as_bad obtain trace_table' where candidate':
      "trace_table' \<in> partial_trace_table_candidates trace_openings"
    and as_bad':
      "as \<in> composition_trace_bad_alpha_space trace_table'"
    unfolding partial_trace_opening_alpha_union_bad_sets_def by blast
  have candidate_header:
    "trace_table' \<in>
      alpha_header_supported_partial_trace_table_candidates s fr
        f_fri_roots f_final"
  proof -
    have partial_candidate':
      "partial_trace_table_candidate trace_table' trace_openings"
      using candidate'
      unfolding partial_trace_table_candidates_def by simp
    show ?thesis
      unfolding alpha_header_supported_partial_trace_table_candidates_def
      using support trace_partial partial_candidate' header by blast
  qed
  have as_union:
    "as \<in>
      alpha_header_supported_partial_union_bad_sets s
        composition_trace_bad_alpha_space fr f_fri_roots f_final"
    unfolding alpha_header_supported_partial_union_bad_sets_def
    using candidate_header as_bad'
      composition_trace_bad_alpha_space_subset_alpha_space[of trace_table']
    by auto
  show ?thesis
    unfolding alpha_header_list_set_hit_def
  proof (intro exI conjI)
    show "accepted_transcript_shape s out as query_idxs"
      by (rule shape)
  next
    show "out = Some (result, final_state)"
      by (rule out_eq)
  next
    show
      "verifier_header_transcript s fr f_fri_roots f_final as dg []
        final rest"
      by (rule header)
  next
    show
      "as \<in>
        alpha_header_supported_partial_union_bad_sets s
          composition_trace_bad_alpha_space fr f_fri_roots f_final"
      by (rule as_union)
  qed
qed

lemma wp_composition_alpha_partial_opening_union_hit_with_empty_header_le_alpha_header_partial_union:
  "wp_event verify_monad
      (composition_alpha_partial_opening_union_hit_with_empty_header s) s \<le>
    wp_event verify_monad
      (alpha_header_list_set_hit s
        (alpha_header_supported_partial_union_bad_sets s
          composition_trace_bad_alpha_space)) s"
  by (rule wp_event_mono_on_support)
    (rule
      composition_alpha_partial_opening_union_hit_with_empty_header_imp_alpha_header_partial_union_on_support)

definition trace_fri_bad_with_empty_composition_header_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_empty_composition_header_candidates s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      \<not> trace_table_low_degree trace_table)"

definition query_bad_with_empty_composition_header_candidates
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "query_bad_with_empty_composition_header_candidates s out \<longleftrightarrow>
    (\<exists>fr f_fri_roots f_final as dg final trace_query_idxs
        trace_openings trace_table composition_table.
      accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table \<and>
      trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      \<not> all_queries_consistent trace_table composition_table as)"

definition soundness_bad_event_partial_candidate_empty_header
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "soundness_bad_event_partial_candidate_empty_header s out \<longleftrightarrow>
    composition_bad_with_empty_composition_header_candidates s out \<or>
    trace_fri_bad_with_empty_composition_header_candidates s out \<or>
    query_bad_with_empty_composition_header_candidates s out"

definition soundness_bad_event_table_aware_with_pairwise_side
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "soundness_bad_event_table_aware_with_pairwise_side s out \<longleftrightarrow>
      supported_pairwise_side_bad s out \<or>
      soundness_bad_event_table_aware_with_merkle s out"

definition soundness_bad_event_table_aware_with_output_local_side
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "soundness_bad_event_table_aware_with_output_local_side s out \<longleftrightarrow>
      supported_output_local_side_bad s out \<or>
      soundness_bad_event_table_aware_with_merkle s out"

lemma soundness_bad_event_table_aware_imp_with_merkle:
  assumes "soundness_bad_event_table_aware s out"
  shows "soundness_bad_event_table_aware_with_merkle s out"
  using assms unfolding soundness_bad_event_table_aware_with_merkle_def by simp

lemma soundness_bad_event_partial_opening_imp_with_merkle:
  assumes "soundness_bad_event_partial_opening s out"
  shows "soundness_bad_event_partial_opening_with_merkle s out"
  using assms
  unfolding soundness_bad_event_partial_opening_with_merkle_def by simp

lemma initial_merkle_binding_bad_imp_partial_opening_with_initial_merkle:
  assumes "initial_merkle_binding_bad s out"
  shows "soundness_bad_event_partial_opening_with_initial_merkle s out"
  using assms
  unfolding soundness_bad_event_partial_opening_with_initial_merkle_def
  by simp

lemma soundness_bad_event_partial_opening_imp_with_initial_merkle:
  assumes "soundness_bad_event_partial_opening s out"
  shows "soundness_bad_event_partial_opening_with_initial_merkle s out"
  using assms
  unfolding soundness_bad_event_partial_opening_with_initial_merkle_def
  by simp

lemma partial_merkle_inconsistency_bad_imp_partial_opening_with_partial_merkle:
  assumes "partial_merkle_inconsistency_bad s out"
  shows "soundness_bad_event_partial_opening_with_partial_merkle s out"
  using assms
  unfolding soundness_bad_event_partial_opening_with_partial_merkle_def
  by simp

lemma soundness_bad_event_partial_opening_imp_with_partial_merkle:
  assumes "soundness_bad_event_partial_opening s out"
  shows "soundness_bad_event_partial_opening_with_partial_merkle s out"
  using assms
  unfolding soundness_bad_event_partial_opening_with_partial_merkle_def
  by simp

lemma soundness_bad_event_partial_candidate_imp_with_partial_merkle:
  assumes "soundness_bad_event_partial_candidate s out"
  shows "soundness_bad_event_partial_candidate_with_partial_merkle s out"
  using assms
  unfolding soundness_bad_event_partial_candidate_with_partial_merkle_def
  by simp

lemma partial_merkle_inconsistency_bad_imp_partial_candidate_with_partial_merkle:
  assumes "partial_merkle_inconsistency_bad s out"
  shows "soundness_bad_event_partial_candidate_with_partial_merkle s out"
  using assms
  unfolding soundness_bad_event_partial_candidate_with_partial_merkle_def
  by simp

lemma accepted_with_partial_initial_openings_alpha_length:
  assumes
    "accepted_with_partial_initial_openings s out fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings"
  shows "length as = length spec"
proof -
  obtain rest where
    "verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    using assms
    unfolding accepted_with_partial_initial_openings_def by blast
  then show ?thesis
    using verifier_header_transcript_shapes(3) by blast
qed

lemma composition_bad_with_partial_candidates_split:
  assumes false_statement: "\<not> exists_valid_trace"
    and bad: "composition_bad_with_partial_candidates s out"
  shows
    "composition_degree_bad_with_partial_candidates s out \<or>
      composition_randomization_bad_with_partial_candidates s out"
proof -
  obtain fr f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table f
    where partial:
      "accepted_with_partial_initial_openings s out fr f_fri_roots f_final
        as dg composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    and violated: "violated_constraints f \<noteq> {}"
    and composition_low:
      "composition_table_low_degree maxDegree composition_table"
    and all_queries:
      "all_queries_consistent trace_table composition_table as"
    using bad
    unfolding composition_bad_with_partial_candidates_def by blast
  show ?thesis
  proof (cases "common_denominator_degree_bounds f as")
    case False
    then have "composition_degree_bad_with_partial_candidates s out"
      unfolding composition_degree_bad_with_partial_candidates_def
      using partial trace_candidate composition_candidate deg_f trace_table
        violated composition_low all_queries
      by blast
    then show ?thesis by blast
  next
    case True
    note bounds = True
    have len_as: "length as = length spec"
      by (rule accepted_with_partial_initial_openings_alpha_length
          [OF partial])
    have hides:
      "random_combination_common_denominator_hides_violations f as"
      by (rule random_combination_common_denominator_hides_from_queries
          [OF len_as false_statement deg_f trace_table composition_low
            all_queries bounds])
    have "composition_randomization_bad_with_partial_candidates s out"
      unfolding composition_randomization_bad_with_partial_candidates_def
      using partial trace_candidate composition_candidate deg_f trace_table
        violated composition_low all_queries bounds hides
      by blast
    then show ?thesis by blast
  qed
qed

lemma composition_degree_bad_with_partial_candidates_false:
  "\<not> composition_degree_bad_with_partial_candidates s out"
  using common_denominator_degree_bounds_from_spec_degree_wellformed
    [OF spec_degree_wellformed_from_spec_query_margin]
  unfolding composition_degree_bad_with_partial_candidates_def by blast

lemma composition_randomization_bad_with_partial_candidates_imp_alpha_hit:
  assumes bad: "composition_randomization_bad_with_partial_candidates s out"
  shows "composition_alpha_bad_set_hit_with_partial_candidates s out"
proof -
  obtain fr f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table f
    where partial:
      "accepted_with_partial_initial_openings s out fr f_fri_roots f_final
        as dg composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    and violated: "violated_constraints f \<noteq> {}"
    and bounds: "common_denominator_degree_bounds f as"
    and hides:
      "random_combination_common_denominator_hides_violations f as"
    using bad
    unfolding composition_randomization_bad_with_partial_candidates_def
    by blast
  have as_in:
    "as \<in> common_denominator_hiding_alpha_space f"
    using accepted_with_partial_initial_openings_alpha_length[OF partial]
      hides
    unfolding common_denominator_hiding_alpha_space_def alpha_space_def
    by simp
  have witness_eq: "low_degree_trace_witness trace_table = f"
    by (rule low_degree_trace_witness_eq[OF deg_f trace_table])
  have "as \<in> composition_trace_bad_alpha_space trace_table"
    using deg_f trace_table violated bounds as_in
    unfolding composition_trace_bad_alpha_space_def witness_eq
    by simp
  then show ?thesis
    unfolding composition_alpha_bad_set_hit_with_partial_candidates_def
    using partial trace_candidate by blast
qed

lemma composition_alpha_bad_set_hit_with_partial_candidates_imp_alpha_header_partial_union_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and hit: "composition_alpha_bad_set_hit_with_partial_candidates s out"
  shows
    "alpha_header_list_set_hit s
      (alpha_header_supported_partial_union_bad_sets s
        composition_trace_bad_alpha_space) out"
proof -
  obtain fr f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table rest
    where partial:
      "accepted_with_partial_initial_openings s out fr f_fri_roots f_final
        as dg composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and trace_partial:
      "accepted_with_partial_trace_openings s out fr trace_query_idxs
        trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and as_bad:
      "as \<in> composition_trace_bad_alpha_space trace_table"
    using hit
    unfolding composition_alpha_bad_set_hit_with_partial_candidates_def
      accepted_with_partial_initial_openings_def
    by blast
  from trace_partial obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_with_partial_trace_openings_def by blast
  from verify_monad_accepted_transcript_shape[OF support[unfolded out_eq]]
  obtain as' query_idxs where shape':
    "accepted_transcript_shape s (Some (result, final_state)) as' query_idxs"
    by blast
  from shape' obtain result' final_state' fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where out_shape:
      "Some (result, final_state) = Some (result', final_state')"
    and header':
      "verifier_header_transcript s fr' f_fri_roots' f_final' as' dg'
        composition_fri_roots' final' rest'"
    by (elim accepted_transcript_shape_header_query_extraction)
  have as'_eq: "as' = as"
    using verifier_header_transcript_unique[OF header' header] by simp
  have shape:
    "accepted_transcript_shape s out as query_idxs"
    using shape' as'_eq out_eq by simp
  have candidate_header:
    "trace_table \<in>
      alpha_header_supported_partial_trace_table_candidates s fr
        f_fri_roots f_final"
    unfolding alpha_header_supported_partial_trace_table_candidates_def
    using support trace_partial trace_candidate header by blast
  have as_union:
    "as \<in>
      alpha_header_supported_partial_union_bad_sets s
        composition_trace_bad_alpha_space fr f_fri_roots f_final"
    unfolding alpha_header_supported_partial_union_bad_sets_def
    using candidate_header as_bad
      composition_trace_bad_alpha_space_subset_alpha_space[of trace_table]
    by auto
  show ?thesis
    unfolding alpha_header_list_set_hit_def
    using shape out_eq header as_union by blast
qed

lemma wp_composition_randomization_bad_with_partial_candidates_le_alpha_header_partial_union:
  "wp_event verify_monad
      (composition_randomization_bad_with_partial_candidates s) s \<le>
    wp_event verify_monad
      (alpha_header_list_set_hit s
        (alpha_header_supported_partial_union_bad_sets s
          composition_trace_bad_alpha_space)) s"
  by (rule wp_event_mono_on_support)
    (rule
      composition_alpha_bad_set_hit_with_partial_candidates_imp_alpha_header_partial_union_on_support
        [OF _ composition_randomization_bad_with_partial_candidates_imp_alpha_hit])

lemma accepted_partial_candidate_partition:
  assumes false_statement: "\<not> exists_valid_trace"
    and partial:
      "accepted_with_partial_initial_openings s out fr f_fri_roots f_final
        as dg composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
  shows "soundness_bad_event_partial_candidate s out"
proof (cases "trace_table_low_degree trace_table")
  case False
  have "trace_fri_bad_with_partial_candidates s out"
    unfolding trace_fri_bad_with_partial_candidates_def
    using partial trace_candidate False by blast
  then show ?thesis
    unfolding soundness_bad_event_partial_candidate_def by blast
next
  case True
  note trace_low = True
  show ?thesis
  proof (cases "composition_table_low_degree maxDegree composition_table")
    case False
    have "composition_fri_bad_with_partial_candidates s out"
      unfolding composition_fri_bad_with_partial_candidates_def
      using partial trace_candidate composition_candidate trace_low False
      by blast
    then show ?thesis
      unfolding soundness_bad_event_partial_candidate_def by blast
  next
    case True
    note composition_low = True
    show ?thesis
    proof (cases "all_queries_consistent trace_table composition_table as")
      case False
      have "query_bad_with_partial_candidates s out"
        unfolding query_bad_with_partial_candidates_def
        using partial trace_candidate composition_candidate trace_low
          composition_low False
        by blast
      then show ?thesis
        unfolding soundness_bad_event_partial_candidate_def by blast
    next
      case True
      note all_queries = True
      from trace_low obtain f where
        deg_f: "degree f < clength"
        and trace_table_eq: "trace_table = map (poly f) eval_domain"
        unfolding trace_table_low_degree_def by blast
      have violated: "violated_constraints f \<noteq> {}"
        by (rule false_statement_violated_constraints
            [OF false_statement deg_f])
      have "composition_bad_with_partial_candidates s out"
        unfolding composition_bad_with_partial_candidates_def
        using partial trace_candidate composition_candidate deg_f
          trace_table_eq violated composition_low all_queries
        by blast
      then show ?thesis
        unfolding soundness_bad_event_partial_candidate_def by blast
    qed
  qed
qed

lemma constant_composition_table_low_degree:
  "composition_table_low_degree maxDegree (replicate (scale * clength) final)"
proof -
  have "map (poly [:final:]) eval_domain =
      replicate (scale * clength) final"
  proof -
    have "map (poly [:final:]) eval_domain =
        replicate (length eval_domain) final"
    proof (rule nth_equalityI)
      show "length (map (poly [:final:]) eval_domain) =
          length (replicate (length eval_domain) final)"
        by simp
    next
      fix i
      assume "i < length (map (poly [:final:]) eval_domain)"
      then show "map (poly [:final:]) eval_domain ! i =
          replicate (length eval_domain) final ! i"
        by simp
    qed
    then show ?thesis
      using eval_domain_length by (simp add: mult.commute)
  qed
  then show ?thesis
    unfolding composition_table_low_degree_def
    by (intro exI[of _ "[:final:]"]) simp
qed

lemma accepted_with_empty_composition_header_candidates_alpha_length:
  assumes
    "accepted_with_empty_composition_header_candidates s out fr
      f_fri_roots f_final as dg final trace_query_idxs trace_openings
      trace_table composition_table"
  shows "length as = length spec"
proof -
  obtain rest where
    "verifier_header_transcript s fr f_fri_roots f_final as dg []
      final rest"
    using assms
    unfolding accepted_with_empty_composition_header_candidates_def by blast
  then show ?thesis
    using verifier_header_transcript_shapes(3) by blast
qed

lemma composition_bad_with_empty_composition_header_candidates_split:
  assumes false_statement: "\<not> exists_valid_trace"
    and bad: "composition_bad_with_empty_composition_header_candidates s out"
  shows
    "composition_degree_bad_with_empty_composition_header_candidates s out \<or>
      composition_randomization_bad_with_empty_composition_header_candidates s out"
proof -
  obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table f
    where partial:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    and violated: "violated_constraints f \<noteq> {}"
    and composition_low:
      "composition_table_low_degree maxDegree composition_table"
    and all_queries:
      "all_queries_consistent trace_table composition_table as"
    using bad
    unfolding composition_bad_with_empty_composition_header_candidates_def
    by blast
  show ?thesis
  proof (cases "common_denominator_degree_bounds f as")
    case False
    then have
      "composition_degree_bad_with_empty_composition_header_candidates s out"
      unfolding composition_degree_bad_with_empty_composition_header_candidates_def
      using partial deg_f trace_table violated composition_low all_queries
      by blast
    then show ?thesis by blast
  next
    case True
    note bounds = True
    have len_as: "length as = length spec"
      by (rule accepted_with_empty_composition_header_candidates_alpha_length
          [OF partial])
    have hides:
      "random_combination_common_denominator_hides_violations f as"
      by (rule random_combination_common_denominator_hides_from_queries
          [OF len_as false_statement deg_f trace_table composition_low
            all_queries bounds])
    have
      "composition_randomization_bad_with_empty_composition_header_candidates
        s out"
      unfolding
        composition_randomization_bad_with_empty_composition_header_candidates_def
      using partial deg_f trace_table violated composition_low all_queries
        bounds hides
      by blast
    then show ?thesis by blast
  qed
qed

lemma composition_degree_bad_with_empty_composition_header_candidates_false:
  "\<not> composition_degree_bad_with_empty_composition_header_candidates s out"
  using common_denominator_degree_bounds_from_spec_degree_wellformed
    [OF spec_degree_wellformed_from_spec_query_margin]
  unfolding composition_degree_bad_with_empty_composition_header_candidates_def
  by blast

lemma composition_degree_bad_with_empty_composition_header_candidates_bound:
  "wp_event verify_monad
    (composition_degree_bad_with_empty_composition_header_candidates s) s \<le>
    0"
proof -
  have "composition_degree_bad_with_empty_composition_header_candidates s =
      (\<lambda>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
        False)"
    by (rule ext)
      (simp add:
        composition_degree_bad_with_empty_composition_header_candidates_false)
  then show ?thesis
    unfolding wp_event_def wp_def dist_expect_def by simp
qed

lemma composition_randomization_bad_with_empty_composition_header_candidates_imp_alpha_hit:
  assumes bad:
      "composition_randomization_bad_with_empty_composition_header_candidates
        s out"
  shows
    "composition_alpha_bad_set_hit_with_empty_composition_header_candidates
      s out"
proof -
  obtain fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table f
    where partial:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
    and deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    and violated: "violated_constraints f \<noteq> {}"
    and bounds: "common_denominator_degree_bounds f as"
    and hides:
      "random_combination_common_denominator_hides_violations f as"
    using bad
    unfolding
      composition_randomization_bad_with_empty_composition_header_candidates_def
    by blast
  have as_in:
    "as \<in> common_denominator_hiding_alpha_space f"
    using accepted_with_empty_composition_header_candidates_alpha_length[OF partial]
      hides
    unfolding common_denominator_hiding_alpha_space_def alpha_space_def
    by simp
  have witness_eq: "low_degree_trace_witness trace_table = f"
    by (rule low_degree_trace_witness_eq[OF deg_f trace_table])
  have "as \<in> composition_trace_bad_alpha_space trace_table"
    using deg_f trace_table violated bounds as_in
    unfolding composition_trace_bad_alpha_space_def witness_eq
    by simp
  then show ?thesis
    unfolding
      composition_alpha_bad_set_hit_with_empty_composition_header_candidates_def
    using partial by blast
qed

lemma wp_composition_randomization_bad_with_empty_composition_header_candidates_le_alpha_hit:
  "wp_event verify_monad
      (composition_randomization_bad_with_empty_composition_header_candidates s)
      s \<le>
    wp_event verify_monad
      (composition_alpha_bad_set_hit_with_empty_composition_header_candidates s)
      s"
  by (rule wp_event_mono)
    (rule
      composition_randomization_bad_with_empty_composition_header_candidates_imp_alpha_hit)

lemma accepted_empty_composition_header_candidate_partition:
  assumes false_statement: "\<not> exists_valid_trace"
    and partial:
      "accepted_with_empty_composition_header_candidates s out fr
        f_fri_roots f_final as dg final trace_query_idxs trace_openings
        trace_table composition_table"
  shows "soundness_bad_event_partial_candidate_empty_header s out"
proof (cases "trace_table_low_degree trace_table")
  case False
  have "trace_fri_bad_with_empty_composition_header_candidates s out"
    unfolding trace_fri_bad_with_empty_composition_header_candidates_def
    using partial False by blast
  then show ?thesis
    unfolding soundness_bad_event_partial_candidate_empty_header_def by blast
next
  case True
  note trace_low = True
  have composition_low:
    "composition_table_low_degree maxDegree composition_table"
  proof -
    have "composition_table = replicate (scale * clength) final"
      using partial
      unfolding accepted_with_empty_composition_header_candidates_def by simp
    then show ?thesis
      using constant_composition_table_low_degree by simp
  qed
  show ?thesis
  proof (cases "all_queries_consistent trace_table composition_table as")
    case False
    have "query_bad_with_empty_composition_header_candidates s out"
      unfolding query_bad_with_empty_composition_header_candidates_def
      using partial trace_low composition_low False by blast
    then show ?thesis
      unfolding soundness_bad_event_partial_candidate_empty_header_def
      by blast
  next
    case True
    note all_queries = True
    from trace_low obtain f where
      deg_f: "degree f < clength"
      and trace_table_eq: "trace_table = map (poly f) eval_domain"
      unfolding trace_table_low_degree_def by blast
    have violated: "violated_constraints f \<noteq> {}"
      by (rule false_statement_violated_constraints
          [OF false_statement deg_f])
    have "composition_bad_with_empty_composition_header_candidates s out"
      unfolding composition_bad_with_empty_composition_header_candidates_def
      using partial deg_f trace_table_eq violated composition_low all_queries
      by blast
    then show ?thesis
      unfolding soundness_bad_event_partial_candidate_empty_header_def
      by blast
  qed
qed

lemma fri_merkle_binding_bad_imp_table_aware_with_merkle:
  assumes "fri_merkle_binding_bad s out"
  shows "soundness_bad_event_table_aware_with_merkle s out"
  using assms unfolding soundness_bad_event_table_aware_with_merkle_def by simp

lemma fri_merkle_binding_bad_imp_partial_opening_with_merkle:
  assumes "fri_merkle_binding_bad s out"
  shows "soundness_bad_event_partial_opening_with_merkle s out"
  using assms
  unfolding soundness_bad_event_partial_opening_with_merkle_def by simp

lemma soundness_bad_event_table_aware_imp_partial_opening_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and bad: "soundness_bad_event_table_aware s out"
  shows "soundness_bad_event_partial_opening s out"
  using bad
proof (unfold soundness_bad_event_table_aware_def, elim disjE)
  assume "composition_bad s out"
  then show ?thesis
    unfolding soundness_bad_event_partial_opening_def by blast
next
  assume trace_bad: "trace_fri_bad_with_tables s out"
  then have "trace_fri_bad_with_partial_openings s out"
    by (rule trace_fri_bad_with_tables_imp_partial_openings_on_support
        [OF support])
  then show ?thesis
    unfolding soundness_bad_event_partial_opening_def by blast
next
  assume composition_bad: "composition_fri_bad_with_tables s out"
  then have "composition_fri_bad_with_partial_openings s out"
    by (rule composition_fri_bad_with_tables_imp_partial_openings_on_support
        [OF support])
  then show ?thesis
    unfolding soundness_bad_event_partial_opening_def by blast
next
  assume "query_bad s out"
  then show ?thesis
    unfolding soundness_bad_event_partial_opening_def by blast
qed

lemma soundness_bad_event_table_aware_with_merkle_imp_partial_opening_with_merkle_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and bad: "soundness_bad_event_table_aware_with_merkle s out"
  shows "soundness_bad_event_partial_opening_with_merkle s out"
  using bad
proof (unfold soundness_bad_event_table_aware_with_merkle_def, elim disjE)
  assume "fri_merkle_binding_bad s out"
  then show ?thesis
    by (rule fri_merkle_binding_bad_imp_partial_opening_with_merkle)
next
  assume "soundness_bad_event_table_aware s out"
  then have "soundness_bad_event_partial_opening s out"
    by (rule soundness_bad_event_table_aware_imp_partial_opening_on_support
        [OF support])
  then show ?thesis
    by (rule soundness_bad_event_partial_opening_imp_with_merkle)
qed

lemma wp_soundness_bad_event_table_aware_le_partial_opening:
  "wp_event verify_monad (soundness_bad_event_table_aware s) s \<le>
    wp_event verify_monad (soundness_bad_event_partial_opening s) s"
  by (rule wp_event_mono_on_support)
    (rule soundness_bad_event_table_aware_imp_partial_opening_on_support)

lemma wp_soundness_bad_event_table_aware_with_merkle_le_partial_opening_with_merkle:
  "wp_event verify_monad (soundness_bad_event_table_aware_with_merkle s) s \<le>
    wp_event verify_monad
      (soundness_bad_event_partial_opening_with_merkle s) s"
  by (rule wp_event_mono_on_support)
    (rule
      soundness_bad_event_table_aware_with_merkle_imp_partial_opening_with_merkle_on_support)

lemma soundness_bad_event_table_aware_with_merkle_imp_with_pairwise_side:
  assumes "soundness_bad_event_table_aware_with_merkle s out"
  shows "soundness_bad_event_table_aware_with_pairwise_side s out"
  using assms
  unfolding soundness_bad_event_table_aware_with_pairwise_side_def by simp

lemma supported_pairwise_side_bad_imp_table_aware_with_pairwise_side:
  assumes "supported_pairwise_side_bad s out"
  shows "soundness_bad_event_table_aware_with_pairwise_side s out"
  using assms
  unfolding soundness_bad_event_table_aware_with_pairwise_side_def by simp

lemma soundness_bad_event_table_aware_with_merkle_imp_with_output_local_side:
  assumes "soundness_bad_event_table_aware_with_merkle s out"
  shows "soundness_bad_event_table_aware_with_output_local_side s out"
  using assms
  unfolding soundness_bad_event_table_aware_with_output_local_side_def
  by simp

lemma supported_output_local_side_bad_imp_table_aware_with_output_local_side:
  assumes "supported_output_local_side_bad s out"
  shows "soundness_bad_event_table_aware_with_output_local_side s out"
  using assms
  unfolding soundness_bad_event_table_aware_with_output_local_side_def
  by simp

lemma accepted_with_fri_tables_table_aware_partition:
  assumes false_statement: "\<not> exists_valid_trace"
    and tables: "accepted_with_fri_tables s out"
  shows "soundness_bad_event_table_aware s out"
proof -
  from accepted_with_fri_tables_obtain_bound_tables[OF tables]
  obtain trace_table composition_table as query_idxs where bound:
    "accepted_with_bound_tables s out trace_table composition_table as
      query_idxs"
    by blast
  have partition:
    "composition_bad s out \<or> trace_fri_bad s out \<or>
      composition_fri_bad s out \<or> query_bad s out"
    by (rule accepted_bound_table_partition[OF false_statement bound])
  then show ?thesis
  proof
    assume "composition_bad s out"
    then show ?thesis
      unfolding soundness_bad_event_table_aware_def by blast
  next
    assume rest: "trace_fri_bad s out \<or>
      composition_fri_bad s out \<or> query_bad s out"
    then show ?thesis
    proof
      assume trace_bad: "trace_fri_bad s out"
      then have "trace_fri_bad_with_tables s out"
        using tables unfolding trace_fri_bad_with_tables_def by simp
      then show ?thesis
        unfolding soundness_bad_event_table_aware_def by blast
    next
      assume rest': "composition_fri_bad s out \<or> query_bad s out"
      then show ?thesis
      proof
        assume composition_bad: "composition_fri_bad s out"
        then have "composition_fri_bad_with_tables s out"
          using tables unfolding composition_fri_bad_with_tables_def by simp
        then show ?thesis
          unfolding soundness_bad_event_table_aware_def by blast
      next
        assume "query_bad s out"
        then show ?thesis
          unfolding soundness_bad_event_table_aware_def by blast
      qed
    qed
  qed
qed

lemma accepted_partition_soundness_bad_event_table_aware_with_merkle:
  assumes false_statement: "\<not> exists_valid_trace"
    and acc: "accepted out"
  shows "soundness_bad_event_table_aware_with_merkle s out"
proof -
  from accepted_partition_fri_merkle_binding[OF acc]
  consider
      (merkle_bad) "fri_merkle_binding_bad s out"
    | (with_tables) "accepted_with_fri_tables s out"
    by blast
  then show ?thesis
  proof cases
    case merkle_bad
    then show ?thesis
      by (rule fri_merkle_binding_bad_imp_table_aware_with_merkle)
  next
    case with_tables
    have "soundness_bad_event_table_aware s out"
      by (rule accepted_with_fri_tables_table_aware_partition
          [OF false_statement with_tables])
    then show ?thesis
      by (rule soundness_bad_event_table_aware_imp_with_merkle)
  qed
qed

lemma accepted_partition_soundness_bad_event_table_aware_with_pairwise_side:
  assumes false_statement: "\<not> exists_valid_trace"
    and acc: "accepted out"
  shows "soundness_bad_event_table_aware_with_pairwise_side s out"
  by (rule soundness_bad_event_table_aware_with_merkle_imp_with_pairwise_side)
    (rule accepted_partition_soundness_bad_event_table_aware_with_merkle
      [OF false_statement acc])

lemma accepted_partition_soundness_bad_event_table_aware_with_output_local_side:
  assumes false_statement: "\<not> exists_valid_trace"
    and acc: "accepted out"
  shows "soundness_bad_event_table_aware_with_output_local_side s out"
  by (rule
      soundness_bad_event_table_aware_with_merkle_imp_with_output_local_side)
    (rule accepted_partition_soundness_bad_event_table_aware_with_merkle
      [OF false_statement acc])

lemma accepted_partition_soundness_bad_event_partial_opening_with_merkle:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
  shows "soundness_bad_event_partial_opening_with_merkle s out"
proof -
  have "soundness_bad_event_table_aware_with_merkle s out"
    by (rule accepted_partition_soundness_bad_event_table_aware_with_merkle
        [OF false_statement acc])
  then show ?thesis
    by (rule
        soundness_bad_event_table_aware_with_merkle_imp_partial_opening_with_merkle_on_support
        [OF supp])
qed

lemma accepted_partition_soundness_bad_event_partial_opening_with_initial_merkle:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
  shows "soundness_bad_event_partial_opening_with_initial_merkle s out"
proof -
  from acc obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  from verify_monad_accepted_transcript_shape[OF supp[unfolded out_eq]]
  obtain as query_idxs where shape:
    "accepted_transcript_shape s (Some (result, final_state)) as query_idxs"
    by blast
  show ?thesis
  proof (cases
      "\<exists>trace_table composition_table.
        accepted_with_bound_tables s (Some (result, final_state))
          trace_table composition_table as query_idxs")
    case False
    have "initial_merkle_binding_bad s out"
      unfolding initial_merkle_binding_bad_def out_eq
      using shape False by blast
    then show ?thesis
      by (rule initial_merkle_binding_bad_imp_partial_opening_with_initial_merkle)
  next
    case True
    then obtain trace_table composition_table where bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table as query_idxs"
      by blast
    have partial_bad:
      "soundness_bad_event_partial_opening s out"
    proof -
      have partition:
        "composition_bad s (Some (result, final_state)) \<or>
         trace_fri_bad s (Some (result, final_state)) \<or>
         composition_fri_bad s (Some (result, final_state)) \<or>
         query_bad s (Some (result, final_state))"
        by (rule accepted_bound_table_partition[OF false_statement bound])
      then show ?thesis
      proof
        assume "composition_bad s (Some (result, final_state))"
        then show ?thesis
          unfolding soundness_bad_event_partial_opening_def out_eq by blast
      next
        assume rest:
          "trace_fri_bad s (Some (result, final_state)) \<or>
           composition_fri_bad s (Some (result, final_state)) \<or>
           query_bad s (Some (result, final_state))"
        then show ?thesis
        proof
          assume trace_bad:
            "trace_fri_bad s (Some (result, final_state))"
          from verify_monad_accepted_with_partial_trace_openings
              [OF supp[unfolded out_eq]]
          obtain fr query_idxs' trace_openings where partial:
            "accepted_with_partial_trace_openings s
              (Some (result, final_state)) fr query_idxs' trace_openings"
            by blast
          have "trace_fri_bad_with_partial_openings s out"
            unfolding trace_fri_bad_with_partial_openings_def out_eq
            using trace_bad partial by blast
          then show ?thesis
            unfolding soundness_bad_event_partial_opening_def by blast
        next
          assume rest':
            "composition_fri_bad s (Some (result, final_state)) \<or>
             query_bad s (Some (result, final_state))"
          then show ?thesis
          proof
            assume composition_bad:
              "composition_fri_bad s (Some (result, final_state))"
            from verify_monad_accepted_with_partial_trace_openings
                [OF supp[unfolded out_eq]]
            obtain fr query_idxs' trace_openings where partial:
              "accepted_with_partial_trace_openings s
                (Some (result, final_state)) fr query_idxs' trace_openings"
              by blast
            have "composition_fri_bad_with_partial_openings s out"
              unfolding composition_fri_bad_with_partial_openings_def out_eq
              using composition_bad partial by blast
            then show ?thesis
              unfolding soundness_bad_event_partial_opening_def by blast
          next
            assume "query_bad s (Some (result, final_state))"
            then show ?thesis
              unfolding soundness_bad_event_partial_opening_def out_eq
              by blast
          qed
        qed
      qed
    qed
    then show ?thesis
      by (rule soundness_bad_event_partial_opening_imp_with_initial_merkle)
  qed
qed

lemma accepted_partition_soundness_bad_event_partial_candidate_with_partial_merkle_if_header_nonempty:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
  shows "soundness_bad_event_partial_candidate_with_partial_merkle s out"
proof -
  from acc obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  from verify_monad_partial_initial_candidates_or_partial_merkle_bad
      [OF supp[unfolded out_eq] header comp_nonempty]
  consider
      (partial_merkle)
        "partial_merkle_inconsistency_bad s (Some (result, final_state))"
    | (candidates) trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table where
        "accepted_with_partial_initial_openings s
          (Some (result, final_state)) fr f_fri_roots f_final as dg
          composition_fri_roots final trace_query_idxs trace_openings
          composition_query_idxs composition_openings"
        "partial_trace_table_candidate trace_table trace_openings"
        "partial_composition_table_candidate composition_table
          composition_openings"
    by blast
  then show ?thesis
  proof cases
    case partial_merkle
    then show ?thesis
      unfolding out_eq
      by (rule
          partial_merkle_inconsistency_bad_imp_partial_candidate_with_partial_merkle)
  next
    case (candidates trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table)
    have bad:
      "soundness_bad_event_partial_candidate s
        (Some (result, final_state))"
      by (rule accepted_partial_candidate_partition
          [OF false_statement candidates(1) candidates(2) candidates(3)])
    then show ?thesis
      unfolding out_eq
      by (rule soundness_bad_event_partial_candidate_imp_with_partial_merkle)
  qed
qed

lemma accepted_partition_soundness_bad_event_partial_candidate_with_partial_merkle_or_empty_header:
  assumes false_statement: "\<not> exists_valid_trace"
    and supp: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  shows
    "soundness_bad_event_partial_candidate_with_partial_merkle s out \<or>
     soundness_bad_event_partial_candidate_empty_header s out"
proof (cases "composition_fri_roots = []")
  case False
  then have comp_nonempty: "composition_fri_roots \<noteq> []"
    by simp
  have "soundness_bad_event_partial_candidate_with_partial_merkle s out"
    by (rule
        accepted_partition_soundness_bad_event_partial_candidate_with_partial_merkle_if_header_nonempty
        [OF false_statement supp acc header comp_nonempty])
  then show ?thesis by simp
next
  case True
  note comp_empty = True
  from acc obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  show ?thesis
  proof (cases
      "partial_merkle_inconsistency_bad s (Some (result, final_state))")
    case True
    then have "soundness_bad_event_partial_candidate_with_partial_merkle s out"
      unfolding out_eq
      by (rule
          partial_merkle_inconsistency_bad_imp_partial_candidate_with_partial_merkle)
    then show ?thesis by simp
  next
    case False
    from verify_monad_accepted_with_partial_trace_openings_for_header
        [OF supp[unfolded out_eq] header]
    obtain trace_query_idxs trace_openings where trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
      by blast
    obtain trace_table where trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
      using accepted_with_partial_trace_openings_candidate_if_no_partial_merkle_bad
        [OF trace_partial False]
      by blast
    have accepted_out: "accepted (Some (result, final_state))"
      by (rule accepted_with_partial_trace_openings_imp_accepted
          [OF trace_partial])
    let ?composition_table = "replicate (scale * clength) final"
    have empty_partial:
      "accepted_with_empty_composition_header_candidates s
        (Some (result, final_state)) fr f_fri_roots f_final as dg final
        trace_query_idxs trace_openings trace_table ?composition_table"
      unfolding accepted_with_empty_composition_header_candidates_def
      by (intro conjI exI[of _ rest])
        (use accepted_out header comp_empty trace_partial trace_candidate
          in simp_all)
    have "soundness_bad_event_partial_candidate_empty_header s
        (Some (result, final_state))"
      by (rule accepted_empty_composition_header_candidate_partition
          [OF false_statement empty_partial])
    then show ?thesis
      unfolding out_eq by simp
  qed
qed

definition trace_fri_with_tables_opening_algebraic_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow> bool"
  where
    "trace_fri_with_tables_opening_algebraic_cover s bad_sets \<longleftrightarrow>
      (\<forall>out trace_table composition_table as query_idxs opening_query_idxs
          trace_roots trace_bs trace_final dg composition_roots composition_bs
          composition_final trace_round_layers composition_round_layers.
        accepted_with_fri_tables s out \<longrightarrow>
        accepted_with_bound_tables s out trace_table composition_table as
          query_idxs \<longrightarrow>
        accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
          dg composition_roots composition_bs composition_final opening_query_idxs
          trace_round_layers composition_round_layers \<longrightarrow>
        \<not> trace_table_low_degree trace_table \<longrightarrow>
        trace_bs \<in> bad_sets trace_table)"

definition composition_fri_with_tables_opening_algebraic_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> 'f list set) \<Rightarrow> bool"
  where
    "composition_fri_with_tables_opening_algebraic_cover s bad_sets \<longleftrightarrow>
      (\<forall>out trace_table composition_table as query_idxs opening_query_idxs
          trace_roots trace_bs trace_final dg composition_roots composition_bs
          composition_final trace_round_layers composition_round_layers.
        accepted_with_fri_tables s out \<longrightarrow>
        accepted_with_bound_tables s out trace_table composition_table as
          query_idxs \<longrightarrow>
        accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
          dg composition_roots composition_bs composition_final opening_query_idxs
          trace_round_layers composition_round_layers \<longrightarrow>
        trace_table_low_degree trace_table \<longrightarrow>
        \<not> composition_table_low_degree maxDegree composition_table \<longrightarrow>
        composition_bs \<in> bad_sets dg composition_table)"

definition trace_fri_with_tables_bad_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list \<Rightarrow> 'f list set"
  where
    "trace_fri_with_tables_bad_sets s trace_table =
      {trace_bs.
        \<exists>out composition_table as query_idxs opening_query_idxs
            trace_roots trace_final dg composition_roots composition_bs
            composition_final trace_round_layers composition_round_layers.
          accepted_with_fri_tables s out \<and>
          accepted_with_bound_tables s out trace_table composition_table as
            query_idxs \<and>
          accepted_fri_opening_transcript s out trace_roots trace_bs
            trace_final dg composition_roots composition_bs
            composition_final opening_query_idxs trace_round_layers
            composition_round_layers \<and>
          \<not> trace_table_low_degree trace_table}"

definition composition_fri_with_tables_bad_sets
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f list set"
  where
    "composition_fri_with_tables_bad_sets s dg composition_table =
      {composition_bs.
        \<exists>out trace_table as query_idxs opening_query_idxs trace_roots
            trace_bs trace_final composition_roots composition_final
            trace_round_layers composition_round_layers.
          accepted_with_fri_tables s out \<and>
          accepted_with_bound_tables s out trace_table composition_table as
            query_idxs \<and>
          accepted_fri_opening_transcript s out trace_roots trace_bs
            trace_final dg composition_roots composition_bs composition_final
            opening_query_idxs trace_round_layers composition_round_layers \<and>
          trace_table_low_degree trace_table \<and>
          \<not> composition_table_low_degree maxDegree composition_table}"

lemma trace_fri_with_tables_bad_sets_cover:
  "trace_fri_with_tables_opening_algebraic_cover s
    (trace_fri_with_tables_bad_sets s)"
  unfolding trace_fri_with_tables_opening_algebraic_cover_def
    trace_fri_with_tables_bad_sets_def
  by blast

lemma composition_fri_with_tables_bad_sets_cover:
  "composition_fri_with_tables_opening_algebraic_cover s
    (composition_fri_with_tables_bad_sets s)"
  unfolding composition_fri_with_tables_opening_algebraic_cover_def
    composition_fri_with_tables_bad_sets_def
  by blast

lemma trace_fri_with_tables_bad_sets_subset:
  "trace_fri_with_tables_bad_sets s trace_table \<subseteq>
    fri_challenge_space (ceil_log clength)"
  unfolding trace_fri_with_tables_bad_sets_def
  using accepted_fri_opening_transcript_challenges
    accepted_fri_challenges_trace_space
  by blast

lemma composition_fri_with_tables_bad_sets_subset:
  "composition_fri_with_tables_bad_sets s dg composition_table \<subseteq>
    fri_challenge_space (ceil_log (to_nat dg + 1))"
  unfolding composition_fri_with_tables_bad_sets_def
  using accepted_fri_opening_transcript_challenges
    accepted_fri_challenges_composition_space
  by blast

lemma trace_fri_with_tables_bad_sets_card_bound:
  "card (trace_fri_with_tables_bad_sets s trace_table) \<le>
    CARD('f) ^ ceil_log clength"
proof -
  have "card (trace_fri_with_tables_bad_sets s trace_table) \<le>
      card (fri_challenge_space (ceil_log clength))"
    by (rule card_mono[OF finite_fri_challenge_space])
      (rule trace_fri_with_tables_bad_sets_subset)
  also have "... = CARD('f) ^ ceil_log clength"
    by (rule card_fri_challenge_space)
  finally show ?thesis .
qed

lemma composition_fri_with_tables_bad_sets_card_bound:
  "card (composition_fri_with_tables_bad_sets s dg composition_table) \<le>
    CARD('f) ^ ceil_log (to_nat dg + 1)"
proof -
  have "card (composition_fri_with_tables_bad_sets s dg composition_table) \<le>
      card (fri_challenge_space (ceil_log (to_nat dg + 1)))"
    by (rule card_mono[OF finite_fri_challenge_space])
      (rule composition_fri_with_tables_bad_sets_subset)
  also have "... = CARD('f) ^ ceil_log (to_nat dg + 1)"
    by (rule card_fri_challenge_space)
  finally show ?thesis .
qed

lemma trace_fri_with_tables_bad_sets_fraction_le_one:
  "nnreal (card (trace_fri_with_tables_bad_sets s trace_table)) /
    nnreal (CARD('f) ^ ceil_log clength) \<le> 1"
proof -
  have "nnreal (card (trace_fri_with_tables_bad_sets s trace_table)) /
      nnreal (CARD('f) ^ ceil_log clength) \<le>
      nnreal (CARD('f) ^ ceil_log clength) /
      nnreal (CARD('f) ^ ceil_log clength)"
    by (rule nnreal_nat_divide_right_mono)
      (rule trace_fri_with_tables_bad_sets_card_bound)
  also have "... = 1"
    by (rule nnreal_nat_divide_self) simp
  finally show ?thesis .
qed

lemma composition_fri_with_tables_bad_sets_fraction_le_one:
  "nnreal (card (composition_fri_with_tables_bad_sets s dg composition_table)) /
    nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> 1"
proof -
  have "nnreal
        (card (composition_fri_with_tables_bad_sets s dg composition_table)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))"
    by (rule nnreal_nat_divide_right_mono)
      (rule composition_fri_with_tables_bad_sets_card_bound)
  also have "... = 1"
    by (rule nnreal_nat_divide_self) simp
  finally show ?thesis .
qed

definition trace_fri_bad_with_tables_challenge_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow> bool"
  where
    "trace_fri_bad_with_tables_challenge_cover s bad_sets \<longleftrightarrow>
      (\<forall>out \<in> set_dist (execute verify_monad s).
        trace_fri_bad_with_tables s out \<longrightarrow>
          trace_fri_challenge_set_hit s bad_sets out)"

definition composition_fri_bad_with_tables_challenge_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> 'f list set) \<Rightarrow> bool"
  where
    "composition_fri_bad_with_tables_challenge_cover s bad_sets \<longleftrightarrow>
      (\<forall>out \<in> set_dist (execute verify_monad s).
        composition_fri_bad_with_tables s out \<longrightarrow>
          composition_fri_challenge_set_hit s bad_sets out)"

lemma trace_fri_with_tables_opening_algebraic_cover_imp_bad_challenge_cover:
  assumes cover:
    "trace_fri_with_tables_opening_algebraic_cover s bad_sets"
  shows "trace_fri_bad_with_tables_challenge_cover s bad_sets"
  unfolding trace_fri_bad_with_tables_challenge_cover_def
proof (intro ballI impI)
  fix out :: "(unit list \<times> ('f, 'a) protocol_channel_scheme) option"
  assume outcome: "out \<in> set_dist (execute verify_monad s)"
    and bad: "trace_fri_bad_with_tables s out"
  then have with_tables: "accepted_with_fri_tables s out"
    and trace_bad: "trace_fri_bad s out"
    unfolding trace_fri_bad_with_tables_def by simp_all
  from trace_bad obtain trace_table composition_table as query_idxs where bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and not_low: "\<not> trace_table_low_degree trace_table"
    unfolding trace_fri_bad_def by blast
  from accepted_with_bound_tables_imp_accepted[OF bound]
  obtain result final_state where out_eq: "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  have verify_out:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using outcome out_eq by simp
  from verify_monad_accepted_fri_opening_transcript[OF verify_out]
  obtain trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final query_idxs' trace_round_layers composition_round_layers
    where openings:
      "accepted_fri_opening_transcript s (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final query_idxs' trace_round_layers
        composition_round_layers"
    by blast
  have trace_bs_bad: "trace_bs \<in> bad_sets trace_table"
    using cover with_tables bound openings not_low out_eq
    unfolding trace_fri_with_tables_opening_algebraic_cover_def by blast
  have challenges:
    "accepted_fri_challenges s out trace_bs dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF openings] out_eq
    by simp
  show "trace_fri_challenge_set_hit s bad_sets out"
    unfolding trace_fri_challenge_set_hit_def
    using bound challenges not_low trace_bs_bad by blast
qed

lemma composition_fri_with_tables_opening_algebraic_cover_imp_bad_challenge_cover:
  assumes cover:
    "composition_fri_with_tables_opening_algebraic_cover s bad_sets"
  shows "composition_fri_bad_with_tables_challenge_cover s bad_sets"
  unfolding composition_fri_bad_with_tables_challenge_cover_def
proof (intro ballI impI)
  fix out :: "(unit list \<times> ('f, 'a) protocol_channel_scheme) option"
  assume outcome: "out \<in> set_dist (execute verify_monad s)"
    and bad: "composition_fri_bad_with_tables s out"
  then have with_tables: "accepted_with_fri_tables s out"
    and composition_bad: "composition_fri_bad s out"
    unfolding composition_fri_bad_with_tables_def by simp_all
  from composition_bad obtain trace_table composition_table as query_idxs
    where bound:
      "accepted_with_bound_tables s out trace_table composition_table as
        query_idxs"
    and trace_low: "trace_table_low_degree trace_table"
    and not_low: "\<not> composition_table_low_degree maxDegree composition_table"
    unfolding composition_fri_bad_def by blast
  from accepted_with_bound_tables_imp_accepted[OF bound]
  obtain result final_state where out_eq: "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  have verify_out:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using outcome out_eq by simp
  from verify_monad_accepted_fri_opening_transcript[OF verify_out]
  obtain trace_roots trace_bs trace_final dg composition_roots composition_bs
      composition_final query_idxs' trace_round_layers composition_round_layers
    where openings:
      "accepted_fri_opening_transcript s (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final query_idxs' trace_round_layers
        composition_round_layers"
    by blast
  have composition_bs_bad:
    "composition_bs \<in> bad_sets dg composition_table"
    using cover with_tables bound openings trace_low not_low out_eq
    unfolding composition_fri_with_tables_opening_algebraic_cover_def by blast
  have challenges:
    "accepted_fri_challenges s out trace_bs dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF openings] out_eq
    by simp
  show "composition_fri_challenge_set_hit s bad_sets out"
    unfolding composition_fri_challenge_set_hit_def
    using bound challenges trace_low not_low composition_bs_bad by blast
qed

lemma wp_trace_fri_challenge_set_hit_bound_if_root_candidate_unique:
  assumes future: "trace_fri_future_fresh s"
    and unique:
      "\<And>fr.
        \<exists>trace_table.
          trace_fri_root_trace_table_candidates s fr \<subseteq> {trace_table}"
    and bounded: "trace_fri_bad_challenge_sets_bounded bad_sets"
  shows "wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le>
    trace_fri_error"
proof -
  have union_bound:
    "\<And>fr. nnreal
        (card (trace_fri_root_union_bad_sets s bad_sets fr)) /
        nnreal (CARD('f) ^ ceil_log clength) \<le> trace_fri_error"
  proof -
    fix fr
    show "nnreal
        (card (trace_fri_root_union_bad_sets s bad_sets fr)) /
        nnreal (CARD('f) ^ ceil_log clength) \<le> trace_fri_error"
      by (rule trace_fri_root_union_bad_sets_fraction_bound_if_unique_candidate
          [OF unique])
        (use bounded in
          \<open>auto simp: trace_fri_bad_challenge_sets_bounded_def\<close>)
  qed
  show ?thesis
    by (rule wp_trace_fri_challenge_set_hit_bound_via_root_union
        [OF future union_bound])
qed

lemma wp_trace_fri_challenge_set_hit_bound_if_supported_root_candidate_unique:
  assumes future: "trace_fri_future_fresh s"
    and unique:
      "\<And>fr.
        \<exists>trace_table.
          trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
            {trace_table}"
    and bounded: "trace_fri_bad_challenge_sets_bounded bad_sets"
  shows "wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le>
    trace_fri_error"
proof -
  have union_bound:
    "\<And>fr. nnreal
        (card (trace_fri_supported_root_union_bad_sets s bad_sets fr)) /
        nnreal (CARD('f) ^ ceil_log clength) \<le> trace_fri_error"
  proof -
    fix fr
    show "nnreal
        (card (trace_fri_supported_root_union_bad_sets s bad_sets fr)) /
        nnreal (CARD('f) ^ ceil_log clength) \<le> trace_fri_error"
      by (rule
          trace_fri_supported_root_union_bad_sets_fraction_bound_if_unique_candidate
          [OF unique])
        (use bounded in
          \<open>auto simp: trace_fri_bad_challenge_sets_bounded_def\<close>)
  qed
  show ?thesis
    by (rule wp_trace_fri_challenge_set_hit_bound_via_supported_root_union
        [OF future union_bound])
qed

lemma wp_trace_fri_challenge_set_hit_bound_if_no_supported_pairwise_merkle_bad:
  assumes future: "trace_fri_future_fresh s"
    and no_bad: "\<not> trace_fri_supported_pairwise_merkle_bad s"
    and bounded: "trace_fri_bad_challenge_sets_bounded bad_sets"
  shows "wp_event verify_monad (trace_fri_challenge_set_hit s bad_sets) s \<le>
    trace_fri_error"
proof (rule wp_trace_fri_challenge_set_hit_bound_if_supported_root_candidate_unique
    [OF future _ bounded])
  fix fr
  show
    "\<exists>trace_table.
      trace_fri_supported_root_trace_table_candidates s fr \<subseteq>
        {trace_table}"
    by (rule
        trace_fri_supported_root_candidate_unique_if_no_global_pairwise_merkle_bad
        [OF no_bad])
qed

lemma wp_composition_fri_challenge_set_hit_bound_if_degree_candidate_unique:
  assumes future: "composition_fri_future_fresh s"
    and unique:
      "\<And>dg.
        \<exists>composition_table.
          composition_fri_degree_table_candidates s dg \<subseteq>
            {composition_table}"
    and bounded: "composition_fri_bad_challenge_sets_bounded bad_sets"
  shows
    "wp_event verify_monad (composition_fri_challenge_set_hit s bad_sets) s \<le>
      composition_fri_error"
proof -
  have union_bound:
    "\<And>dg. nnreal
        (card (composition_fri_degree_union_bad_sets s bad_sets dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
        composition_fri_error"
  proof -
    fix dg
    show "nnreal
        (card (composition_fri_degree_union_bad_sets s bad_sets dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
        composition_fri_error"
      by (rule
          composition_fri_degree_union_bad_sets_fraction_bound_if_unique_candidate
          [OF unique])
        (use bounded in
          \<open>auto simp: composition_fri_bad_challenge_sets_bounded_def\<close>)
  qed
  show ?thesis
    by (rule wp_composition_fri_challenge_set_hit_bound_via_degree_union
        [OF future union_bound])
qed

lemma wp_composition_fri_challenge_set_hit_bound_if_supported_root_candidate_unique:
  assumes future: "composition_fri_future_fresh s"
    and unique:
      "\<And>fr f_fri_roots f_final as dg composition_fri_roots.
        \<exists>composition_table.
          composition_fri_supported_root_composition_table_candidates s fr
            f_fri_roots f_final as dg composition_fri_roots \<subseteq>
            {composition_table}"
    and bounded: "composition_fri_bad_challenge_sets_bounded bad_sets"
  shows
    "wp_event verify_monad (composition_fri_challenge_set_hit s bad_sets) s \<le>
      composition_fri_error"
proof -
  have union_bound:
    "\<And>fr f_fri_roots f_final as dg composition_fri_roots.
      nnreal
        (card
          (composition_fri_supported_root_union_bad_sets s bad_sets fr
            f_fri_roots f_final as dg composition_fri_roots)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
      composition_fri_error"
  proof -
    fix fr f_fri_roots f_final as dg composition_fri_roots
    show "nnreal
        (card
          (composition_fri_supported_root_union_bad_sets s bad_sets fr
            f_fri_roots f_final as dg composition_fri_roots)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
      composition_fri_error"
      by (rule
          composition_fri_supported_root_union_bad_sets_fraction_bound_if_unique_candidate
          [OF unique])
        (use bounded in
          \<open>auto simp: composition_fri_bad_challenge_sets_bounded_def\<close>)
  qed
  show ?thesis
    by (rule
        wp_composition_fri_challenge_set_hit_bound_via_supported_root_union
        [OF future union_bound])
qed

lemma wp_composition_fri_challenge_set_hit_bound_if_no_supported_pairwise_merkle_bad:
  assumes future: "composition_fri_future_fresh s"
    and no_bad: "\<not> composition_fri_supported_pairwise_merkle_bad s"
    and bounded: "composition_fri_bad_challenge_sets_bounded bad_sets"
  shows
    "wp_event verify_monad (composition_fri_challenge_set_hit s bad_sets) s \<le>
      composition_fri_error"
proof (rule
    wp_composition_fri_challenge_set_hit_bound_if_supported_root_candidate_unique
    [OF future _ bounded])
  fix fr f_fri_roots f_final as dg composition_fri_roots
  show
    "\<exists>composition_table.
      composition_fri_supported_root_composition_table_candidates s fr
        f_fri_roots f_final as dg composition_fri_roots \<subseteq>
        {composition_table}"
    by (rule
        composition_fri_supported_root_candidate_unique_if_no_global_pairwise_merkle_bad
        [OF no_bad])
qed

definition trace_fri_opening_algebraic_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> 'f list set) \<Rightarrow> bool"
  where
    "trace_fri_opening_algebraic_cover s bad_sets \<longleftrightarrow>
      (\<forall>out trace_table composition_table as query_idxs opening_query_idxs
          trace_roots trace_bs trace_final dg composition_roots composition_bs
          composition_final trace_round_layers composition_round_layers.
        accepted_with_bound_tables s out trace_table composition_table as query_idxs \<longrightarrow>
        accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
          dg composition_roots composition_bs composition_final opening_query_idxs
          trace_round_layers composition_round_layers \<longrightarrow>
        \<not> trace_table_low_degree trace_table \<longrightarrow>
        trace_bs \<in> bad_sets trace_table)"

definition composition_fri_opening_algebraic_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> 'f list set) \<Rightarrow> bool"
  where
    "composition_fri_opening_algebraic_cover s bad_sets \<longleftrightarrow>
      (\<forall>out trace_table composition_table as query_idxs opening_query_idxs
          trace_roots trace_bs trace_final dg composition_roots composition_bs
          composition_final trace_round_layers composition_round_layers.
        accepted_with_bound_tables s out trace_table composition_table as query_idxs \<longrightarrow>
        accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
          dg composition_roots composition_bs composition_final opening_query_idxs
          trace_round_layers composition_round_layers \<longrightarrow>
        trace_table_low_degree trace_table \<longrightarrow>
        \<not> composition_table_low_degree maxDegree composition_table \<longrightarrow>
        composition_bs \<in> bad_sets dg composition_table)"

definition trace_fri_opening_reduction_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "trace_fri_opening_reduction_assumption s \<longleftrightarrow>
      (\<exists>bad_sets.
        trace_fri_opening_algebraic_cover s bad_sets \<and>
        trace_fri_bad_challenge_sets_bounded bad_sets)"

definition composition_fri_opening_reduction_assumption
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "composition_fri_opening_reduction_assumption s \<longleftrightarrow>
      (\<exists>bad_sets.
        composition_fri_opening_algebraic_cover s bad_sets \<and>
        composition_fri_bad_challenge_sets_bounded bad_sets)"

lemma trace_fri_opening_reductionI:
  assumes "trace_fri_opening_algebraic_cover s bad_sets"
    and "trace_fri_bad_challenge_sets_bounded bad_sets"
  shows "trace_fri_opening_reduction_assumption s"
  using assms unfolding trace_fri_opening_reduction_assumption_def by blast

lemma trace_fri_opening_reductionE:
  assumes "trace_fri_opening_reduction_assumption s"
  obtains bad_sets
  where "trace_fri_opening_algebraic_cover s bad_sets"
    and "trace_fri_bad_challenge_sets_bounded bad_sets"
  using assms unfolding trace_fri_opening_reduction_assumption_def by blast

lemma composition_fri_opening_reductionI:
  assumes "composition_fri_opening_algebraic_cover s bad_sets"
    and "composition_fri_bad_challenge_sets_bounded bad_sets"
  shows "composition_fri_opening_reduction_assumption s"
  using assms unfolding composition_fri_opening_reduction_assumption_def by blast

lemma composition_fri_opening_reductionE:
  assumes "composition_fri_opening_reduction_assumption s"
  obtains bad_sets
  where "composition_fri_opening_algebraic_cover s bad_sets"
    and "composition_fri_bad_challenge_sets_bounded bad_sets"
  using assms unfolding composition_fri_opening_reduction_assumption_def
  by blast

lemma trace_fri_multiround_bad_sets_bounded:
  assumes frac:
    "\<And>trace_table.
      nnreal (card (trace_fri_multiround_bad_sets bad trace_table)) /
        nnreal (CARD('f) ^ ceil_log clength) \<le> trace_fri_error"
  shows "trace_fri_bad_challenge_sets_bounded
    (trace_fri_multiround_bad_sets bad)"
  unfolding trace_fri_bad_challenge_sets_bounded_def
proof (intro allI conjI)
  fix trace_table
  show "trace_fri_multiround_bad_sets bad trace_table \<subseteq>
      fri_challenge_space (ceil_log clength)"
    by (rule trace_fri_multiround_bad_sets_subset)
  show "nnreal (card (trace_fri_multiround_bad_sets bad trace_table)) /
      nnreal (CARD('f) ^ ceil_log clength) \<le> trace_fri_error"
    by (rule frac)
qed

lemma composition_fri_multiround_bad_sets_bounded:
  assumes frac:
    "\<And>dg composition_table.
      nnreal (card
        (composition_fri_multiround_bad_sets bad dg composition_table)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
        composition_fri_error"
  shows "composition_fri_bad_challenge_sets_bounded
    (composition_fri_multiround_bad_sets bad)"
  unfolding composition_fri_bad_challenge_sets_bounded_def
proof (intro allI conjI)
  fix dg composition_table
  show "composition_fri_multiround_bad_sets bad dg composition_table \<subseteq>
      fri_challenge_space (ceil_log (to_nat dg + 1))"
    by (rule composition_fri_multiround_bad_sets_subset)
  show "nnreal (card
      (composition_fri_multiround_bad_sets bad dg composition_table)) /
      nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
      composition_fri_error"
    by (rule frac)
qed

lemma trace_fri_opening_reduction_from_multiround_bad_sets:
  assumes cover:
    "trace_fri_opening_algebraic_cover s
      (trace_fri_multiround_bad_sets bad)"
    and frac:
      "\<And>trace_table.
        nnreal (card (trace_fri_multiround_bad_sets bad trace_table)) /
          nnreal (CARD('f) ^ ceil_log clength) \<le> trace_fri_error"
  shows "trace_fri_opening_reduction_assumption s"
  by (rule trace_fri_opening_reductionI
      [OF cover trace_fri_multiround_bad_sets_bounded[OF frac]])

lemma composition_fri_opening_reduction_from_multiround_bad_sets:
  assumes cover:
    "composition_fri_opening_algebraic_cover s
      (composition_fri_multiround_bad_sets bad)"
    and frac:
      "\<And>dg composition_table.
        nnreal (card
          (composition_fri_multiround_bad_sets bad dg composition_table)) /
          nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le>
          composition_fri_error"
  shows "composition_fri_opening_reduction_assumption s"
  by (rule composition_fri_opening_reductionI
      [OF cover composition_fri_multiround_bad_sets_bounded[OF frac]])

end

end
