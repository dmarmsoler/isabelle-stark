(*  Title:      Stark/Soundness_Conceptual_Query_Current.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Conceptual_Query_Current
  imports
    Soundness_Conceptual_Query_Target
    Staged_Security_Experiment_Composition_Query_Current
begin

text \<open>
  Connect the existing prefix-authenticated query target to the conceptual
  prefix tables.  This is a deterministic bridge: it only uses openings that
  are already authenticated in the query-prefix state, so the resulting target
  remains fixed before the query-index challenge is sampled.
\<close>

context soundness
begin

definition staged_query_prefix_prefix_authenticated_empty_opening_target
  :: "'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "staged_query_prefix_prefix_authenticated_empty_opening_target
      prefix prefix_state =
    {idx \<in> query_sample_space.
      \<exists>(trace_openings :: 'f authenticated_opening list).
        partial_authenticated_table (sqp_trace_root prefix)
          (scale * clength) trace_openings prefix_state \<and>
        map opening_index trace_openings = powers_scaled idx \<and>
        cp_eval (sqp_alphas prefix) (map opening_value trace_openings)
          (h ^ idx * shift) = sqp_composition_final prefix}"

lemma staged_query_prefix_prefix_authenticated_empty_opening_target_subset:
  "staged_query_prefix_prefix_authenticated_empty_opening_target
      prefix prefix_state \<subseteq> query_sample_space"
  unfolding staged_query_prefix_prefix_authenticated_empty_opening_target_def
  by blast

definition checked_staged_security_with_query_prefix_prefix_authenticated_empty_opening_hit
where
  "checked_staged_security_with_query_prefix_prefix_authenticated_empty_opening_hit
      trace_openings i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        partial_authenticated_table (sqp_trace_root prefix)
          (scale * clength) trace_openings prefix_state \<and>
        map opening_index trace_openings = powers_scaled (index (to_nat raw)) \<and>
        cp_eval (sqp_alphas prefix) (map opening_value trace_openings)
          (h ^ index (to_nat raw) * shift) =
          sqp_composition_final prefix)"

definition checked_staged_security_with_query_prefix_empty_authenticated_opening_hit
where
  "checked_staged_security_with_query_prefix_empty_authenticated_opening_hit
      trace_openings i out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        partial_authenticated_table (sqp_trace_root prefix)
          (scale * clength) trace_openings final_state \<and>
        map opening_index trace_openings = powers_scaled (index (to_nat raw)) \<and>
        cp_eval (sqp_alphas prefix) (map opening_value trace_openings)
          (h ^ index (to_nat raw) * shift) =
          sqp_composition_final prefix)"

definition checked_staged_security_with_query_prefix_empty_trace_path_output_hit
where
  "checked_staged_security_with_query_prefix_empty_trace_path_output_hit
      trace_openings out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        (\<exists>opening \<in> set trace_openings.
          hash_map_new_output_hit
            (merkle_path_target_roots final_state
              (sqp_trace_root prefix)
              (scale * clength)
              (opening_index opening)
              (opening_value opening)
              (opening_path opening))
            prefix_state final_state))"

definition checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at
where
  "checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at
      i out \<longleftrightarrow>
    (\<exists>(trace_openings :: 'f authenticated_opening list).
      checked_staged_security_with_query_prefix_prefix_authenticated_empty_opening_hit
        trace_openings i out)"

definition checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at
where
  "checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at
      i out \<longleftrightarrow>
    (\<exists>(trace_openings :: 'f authenticated_opening list).
      checked_staged_security_with_query_prefix_empty_authenticated_opening_hit
        trace_openings i out)"

definition checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at
where
  "checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at
      i out \<longleftrightarrow>
    (\<exists>(trace_openings :: 'f authenticated_opening list).
      checked_staged_security_with_query_prefix_empty_trace_path_output_hit
        trace_openings out)"

definition checked_staged_security_with_query_prefix_conceptual_empty_context_residual_at
where
  "checked_staged_security_with_query_prefix_conceptual_empty_context_residual_at
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        hash_map_output_collision prefix_state \<or>
        \<not> trace_table_low_degree
          (query_prefix_trace_conceptual_table prefix prefix_state) \<or>
        all_queries_consistent
          (query_prefix_trace_conceptual_table prefix prefix_state)
          (replicate (scale * clength) (sqp_composition_final prefix))
          (sqp_alphas prefix))"

definition checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
where
  "checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
      (i :: nat) out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at
      i out \<and>
    checked_staged_security_with_query_prefix_conceptual_empty_context_residual_at
      out"

lemma checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at_imp_dynamic_target:
  assumes hit:
    "checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at
      i out"
  shows
    "checked_staged_security_with_query_prefix_dynamic_index_hit
      staged_query_prefix_prefix_authenticated_empty_opening_target out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at_def
      checked_staged_security_with_query_prefix_prefix_authenticated_empty_opening_hit_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state data attacker_state result
      final_state where out_eq:
    "out =
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)"
    by (cases packed) (auto split: prod.splits)
  from hit obtain trace_openings where prefix_hit:
    "checked_staged_security_with_query_prefix_prefix_authenticated_empty_opening_hit
      trace_openings i out"
    unfolding
      checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at_def
    by blast
  have idx_in:
    "index (to_nat raw) \<in>
      staged_query_prefix_prefix_authenticated_empty_opening_target
        prefix prefix_state"
    using prefix_hit index_less_query_sample_space
    unfolding out_eq
      checked_staged_security_with_query_prefix_prefix_authenticated_empty_opening_hit_def
      staged_query_prefix_prefix_authenticated_empty_opening_target_def
      query_sample_space_def
    by auto
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_query_prefix_dynamic_index_hit_def
      checked_staged_query_prefix_dynamic_index_hit_def
    using idx_in by simp
qed

lemma checked_staged_security_with_query_prefix_empty_authenticated_opening_hit_imp_prefix_or_path_output_hit:
  assumes ext: "prefix_state \<le> final_state"
    and hit:
      "checked_staged_security_with_query_prefix_empty_authenticated_opening_hit
        trace_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "checked_staged_security_with_query_prefix_prefix_authenticated_empty_opening_hit
        trace_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state)) \<or>
     checked_staged_security_with_query_prefix_empty_trace_path_output_hit
        trace_openings
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
proof -
  have trace_table:
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) trace_openings final_state"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled (index (to_nat raw))"
    and consistent:
      "cp_eval (sqp_alphas prefix) (map opening_value trace_openings)
        (h ^ index (to_nat raw) * shift) =
       sqp_composition_final prefix"
    using hit
    unfolding
      checked_staged_security_with_query_prefix_empty_authenticated_opening_hit_def
    by simp_all
  have trace_pullback:
    "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) trace_openings prefix_state \<or>
     (\<exists>opn \<in> set trace_openings.
      hash_map_new_output_hit
        (merkle_path_target_roots final_state (sqp_trace_root prefix)
          (scale * clength)
          (opening_index opn)
          (opening_value opn)
          (opening_path opn)) prefix_state final_state)"
    by (rule partial_authenticated_table_pullback_or_new_output_hit
        [OF ext trace_table])
  then show ?thesis
  proof
    assume trace_prefix:
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) trace_openings prefix_state"
    then have
      "checked_staged_security_with_query_prefix_prefix_authenticated_empty_opening_hit
        trace_openings i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      using trace_indices consistent
      unfolding
        checked_staged_security_with_query_prefix_prefix_authenticated_empty_opening_hit_def
      by simp
    then show ?thesis by simp
  next
    assume
      "\<exists>opn \<in> set trace_openings.
        hash_map_new_output_hit
          (merkle_path_target_roots final_state (sqp_trace_root prefix)
            (scale * clength)
            (opening_index opn)
            (opening_value opn)
            (opening_path opn)) prefix_state final_state"
    then have
      "checked_staged_security_with_query_prefix_empty_trace_path_output_hit
        trace_openings
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
      unfolding
        checked_staged_security_with_query_prefix_empty_trace_path_output_hit_def
      by simp
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_empty_authenticated_opening_hit_imp_prefix_or_path_output_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_empty_authenticated_opening_hit
        trace_openings i out"
  shows
    "checked_staged_security_with_query_prefix_prefix_authenticated_empty_opening_hit
        trace_openings i out \<or>
     checked_staged_security_with_query_prefix_empty_trace_path_output_hit
        trace_openings out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_query_prefix_empty_authenticated_opening_hit_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state data attacker_state result
      final_state where out_eq:
    "out =
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)"
    by (cases packed) (auto split: prod.splits)
  have ext: "prefix_state \<le> final_state"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_prefix_extends_final
          [OF wf controlled i_bound])
      (use support out_eq in simp)
  show ?thesis
    unfolding out_eq
    by (rule
        checked_staged_security_with_query_prefix_empty_authenticated_opening_hit_imp_prefix_or_path_output_hit
          [OF ext])
      (use hit out_eq in simp)
qed

lemma checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at_imp_prefix_or_path_output_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at
        i out"
  shows
    "checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at
        i out \<or>
     checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at
        i out"
proof -
  from hit obtain trace_openings where trace_hit:
    "checked_staged_security_with_query_prefix_empty_authenticated_opening_hit
      trace_openings i out"
    unfolding
      checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at_def
    by blast
  have split:
    "checked_staged_security_with_query_prefix_prefix_authenticated_empty_opening_hit
        trace_openings i out \<or>
     checked_staged_security_with_query_prefix_empty_trace_path_output_hit
        trace_openings out"
    by (rule
        checked_staged_security_with_query_prefix_empty_authenticated_opening_hit_imp_prefix_or_path_output_hit_on_support
        [OF wf controlled i_bound support trace_hit])
  then show ?thesis
    unfolding
      checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at_def
      checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at_def
    by blast
qed

lemma low_degree_all_queries_consistent_imp_composition_trace_bad_alpha_space:
  assumes false_statement: "\<not> exists_valid_trace"
    and len_as: "length as = length spec"
    and trace_low: "trace_table_low_degree trace_table"
    and composition_low:
      "composition_table_low_degree maxDegree composition_table"
    and all_queries:
      "all_queries_consistent trace_table composition_table as"
  shows "as \<in> composition_trace_bad_alpha_space trace_table"
proof -
  from trace_low obtain f where deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    unfolding trace_table_low_degree_def by blast
  have bounds: "common_denominator_degree_bounds f as"
    by (rule common_denominator_degree_bounds_from_spec_degree_wellformed
        [OF spec_degree_wellformed_from_spec_query_margin deg_f])
  have hides:
    "random_combination_common_denominator_hides_violations f as"
    by (rule random_combination_common_denominator_hides_from_queries
        [OF len_as false_statement deg_f trace_table composition_low
          all_queries bounds])
  have violated: "violated_constraints f \<noteq> {}"
    by (rule false_statement_violated_constraints
        [OF false_statement deg_f])
  have as_common: "as \<in> common_denominator_hiding_alpha_space f"
    using len_as hides
    unfolding common_denominator_hiding_alpha_space_def alpha_space_def
    by simp
  have witness_eq: "low_degree_trace_witness trace_table = f"
    by (rule low_degree_trace_witness_eq[OF deg_f trace_table])
  show ?thesis
    using deg_f trace_table violated bounds as_common
    unfolding composition_trace_bad_alpha_space_def witness_eq
    by simp
qed

lemma staged_query_prefix_prefix_authenticated_empty_opening_target_subset_conceptual_empty:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
    and trace_low:
      "trace_table_low_degree
        (query_prefix_trace_conceptual_table prefix prefix_state)"
    and not_all:
      "\<not> all_queries_consistent
        (query_prefix_trace_conceptual_table prefix prefix_state)
        (replicate (scale * clength) (sqp_composition_final prefix))
        (sqp_alphas prefix)"
  shows
    "staged_query_prefix_prefix_authenticated_empty_opening_target
        prefix prefix_state \<subseteq>
     staged_query_prefix_conceptual_empty_query_target prefix prefix_state"
proof
  fix idx
  assume idx_in:
    "idx \<in>
      staged_query_prefix_prefix_authenticated_empty_opening_target
        prefix prefix_state"
  then obtain trace_openings where
    idx_sample: "idx \<in> query_sample_space"
    and trace_table:
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) trace_openings prefix_state"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and final_eq:
      "cp_eval (sqp_alphas prefix) (map opening_value trace_openings)
        (h ^ idx * shift) = sqp_composition_final prefix"
    unfolding staged_query_prefix_prefix_authenticated_empty_opening_target_def
    by blast
  let ?trace_table =
    "query_prefix_trace_conceptual_table prefix prefix_state"
  let ?composition_table =
    "replicate (scale * clength) (sqp_composition_final prefix)"
  have idx_bound: "idx < clength * scale"
    by (rule query_sample_space_less_domain[OF idx_sample])
  have trace_values:
    "map ((!) ?trace_table) (powers_scaled idx) =
      map opening_value trace_openings"
  proof (rule nth_equalityI)
    show
      "length (map ((!) ?trace_table) (powers_scaled idx)) =
       length (map opening_value trace_openings)"
      using trace_indices by (metis length_map)
  next
    fix k
    assume k_bound:
      "k < length (map ((!) ?trace_table) (powers_scaled idx))"
    then have ps_bound: "k < length (powers_scaled idx)"
      by simp
    have opn_bound: "k < length trace_openings"
      using trace_indices ps_bound by (metis length_map)
    have opn_in: "trace_openings ! k \<in> set trace_openings"
      by (rule nth_mem[OF opn_bound])
    have idx_eq:
      "opening_index (trace_openings ! k) = powers_scaled idx ! k"
      using trace_indices ps_bound opn_bound
      by (metis nth_map)
    have conceptual:
      "?trace_table ! opening_index (trace_openings ! k) =
        opening_value (trace_openings ! k)"
      by (rule
          query_prefix_trace_conceptual_table_agrees_with_partial_authenticated_table
          [OF clean trace_table opn_in])
    show
      "map ((!) ?trace_table) (powers_scaled idx) ! k =
       map opening_value trace_openings ! k"
      using ps_bound opn_bound idx_eq conceptual by simp
  qed
  have query_consistent:
    "query_consistent_at ?trace_table ?composition_table
      (sqp_alphas prefix) idx"
  proof -
    have composition_value:
      "?composition_table ! idx = sqp_composition_final prefix"
      using idx_bound by (simp add: mult.commute)
    have cp_eq:
      "cp_eval (sqp_alphas prefix)
        (map ((!) ?trace_table) (powers_scaled idx))
        (h ^ idx * shift) =
       sqp_composition_final prefix"
      using trace_values final_eq by simp
    show ?thesis
      unfolding query_consistent_at_def
      using idx_bound query_sample_space_powers_scaled_bound[OF idx_sample]
        composition_value cp_eq by (simp add: mult.commute)
  qed
  show
    "idx \<in>
      staged_query_prefix_conceptual_empty_query_target prefix prefix_state"
    unfolding staged_query_prefix_conceptual_empty_query_target_def
      query_sampling_success_space_def query_agreement_indices_def
    using idx_sample trace_low constant_composition_table_low_degree not_all
      query_consistent by simp
qed

lemma checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_imp_conceptual_empty_or_residual:
  assumes hit:
    "checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at
      i out"
  shows
    "checked_staged_security_with_query_prefix_conceptual_empty_target_hit out \<or>
     checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
      i out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at_def
      checked_staged_security_with_query_prefix_prefix_authenticated_empty_opening_hit_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state data attacker_state result
      final_state where out_eq:
    "out =
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)"
    by (cases packed) (auto split: prod.splits)
  show ?thesis
  proof (cases
      "\<not> hash_map_output_collision prefix_state \<and>
       trace_table_low_degree
        (query_prefix_trace_conceptual_table prefix prefix_state) \<and>
       \<not> all_queries_consistent
        (query_prefix_trace_conceptual_table prefix prefix_state)
        (replicate (scale * clength) (sqp_composition_final prefix))
        (sqp_alphas prefix)")
    case False
    then have
      "checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
        i out"
      unfolding
        checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at_def
        checked_staged_security_with_query_prefix_conceptual_empty_context_residual_at_def
        out_eq
      using hit out_eq by simp
    then show ?thesis by simp
  next
    case True
    then have clean:
        "\<not> hash_map_output_collision prefix_state"
      and trace_low:
        "trace_table_low_degree
          (query_prefix_trace_conceptual_table prefix prefix_state)"
      and not_all:
        "\<not> all_queries_consistent
          (query_prefix_trace_conceptual_table prefix prefix_state)
          (replicate (scale * clength) (sqp_composition_final prefix))
          (sqp_alphas prefix)"
      by blast+
    have prefix_hit:
      "checked_staged_security_with_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_empty_opening_target out"
      by (rule
          checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at_imp_dynamic_target
          [OF hit])
    have subset:
      "staged_query_prefix_prefix_authenticated_empty_opening_target
          prefix prefix_state \<subseteq>
       staged_query_prefix_conceptual_empty_query_target prefix prefix_state"
      by (rule
          staged_query_prefix_prefix_authenticated_empty_opening_target_subset_conceptual_empty
          [OF clean trace_low not_all])
    have conceptual_hit:
      "checked_staged_security_with_query_prefix_conceptual_empty_target_hit
        out"
      using prefix_hit subset
      unfolding out_eq
        checked_staged_security_with_query_prefix_conceptual_empty_target_hit_def
        checked_staged_security_with_query_prefix_dynamic_index_hit_def
        checked_staged_query_prefix_dynamic_index_hit_def
      by auto
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at_bound_from_conceptual_empty_residual:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and residual_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
          i)
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at
        i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Conceptual =
    "checked_staged_security_with_query_prefix_conceptual_empty_target_hit"
  let ?Residual =
    "checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
      i"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at
        i)
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?Conceptual out \<or> ?Residual out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_imp_conceptual_empty_or_residual)
  have conceptual_bound:
    "wp_event ?M ?Conceptual adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_empty_target_hit_bound
        [OF wf controlled i_bound])
  have union_bound:
    "wp_event ?M (\<lambda>out. ?Conceptual out \<or> ?Residual out)
      adversary_initial_state \<le>
     wp_event ?M ?Conceptual adversary_initial_state +
     wp_event ?M ?Residual adversary_initial_state"
    by (rule wp_event_union_bound)
  have sum_bound:
    "wp_event ?M ?Conceptual adversary_initial_state +
     wp_event ?M ?Residual adversary_initial_state \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound) +
      R"
    by (intro add_mono conceptual_bound residual_bound)
  show ?thesis
    by (rule order_trans[OF event_le])
      (rule order_trans[OF union_bound sum_bound])
qed

lemma checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at_bound_from_prefix_and_path:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at
          i)
        adversary_initial_state \<le> P"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at
          i)
        adversary_initial_state \<le> T"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at
        i)
      adversary_initial_state \<le> P + T"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Prefix =
    "checked_staged_security_with_query_prefix_current_empty_prefix_authenticated_hit_at
      i"
  let ?Path =
    "checked_staged_security_with_query_prefix_current_empty_trace_path_output_hit_at
      i"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at
        i)
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?Prefix out \<or> ?Path out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_current_empty_authenticated_hit_at_imp_prefix_or_path_output_hit_on_support
        [OF wf controlled i_bound])
  have union_bound:
    "wp_event ?M (\<lambda>out. ?Prefix out \<or> ?Path out)
      adversary_initial_state \<le>
     wp_event ?M ?Prefix adversary_initial_state +
     wp_event ?M ?Path adversary_initial_state"
    by (rule wp_event_union_bound)
  have sum_bound:
    "wp_event ?M ?Prefix adversary_initial_state +
     wp_event ?M ?Path adversary_initial_state \<le> P + T"
    by (intro add_mono prefix_bound path_bound)
  show ?thesis
    by (rule order_trans[OF event_le])
      (rule order_trans[OF union_bound sum_bound])
qed

lemma staged_query_prefix_prefix_authenticated_opening_target_subset_conceptual:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
    and trace_low:
      "trace_table_low_degree
        (query_prefix_trace_conceptual_table prefix prefix_state)"
    and composition_low:
      "composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table prefix prefix_state)"
    and not_all:
      "\<not> all_queries_consistent
        (query_prefix_trace_conceptual_table prefix prefix_state)
        (query_prefix_composition_conceptual_table prefix prefix_state)
        (sqp_alphas prefix)"
  shows
    "staged_query_prefix_prefix_authenticated_opening_target prefix
      prefix_state \<subseteq>
     staged_query_prefix_conceptual_query_target prefix prefix_state"
proof
  fix idx
  assume idx_in:
    "idx \<in> staged_query_prefix_prefix_authenticated_opening_target prefix
      prefix_state"
  then obtain trace_openings composition_openings where
    trace_table:
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) trace_openings prefix_state"
    and composition_table:
      "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) composition_openings prefix_state"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (sqp_alphas prefix) idx"
    unfolding staged_query_prefix_prefix_authenticated_opening_target_def
    by blast
  let ?trace_openings =
    "(replicate rounds []) [0 := trace_openings]"
  let ?composition_openings =
    "(replicate rounds []) [0 := composition_openings]"
  have zero_bound: "0 < rounds"
    by (rule rounds_positive)
  have trace_len: "length ?trace_openings = rounds"
    by simp
  have composition_len: "length ?composition_openings = rounds"
    by simp
  have trace_tables:
    "\<And>j. j < rounds \<Longrightarrow>
      partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) (?trace_openings ! j) prefix_state"
  proof -
    fix j
    assume j_bound: "j < rounds"
    show
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) (?trace_openings ! j) prefix_state"
    proof (cases "j = 0")
      case True
      then show ?thesis
        using trace_table zero_bound by simp
    next
      case False
      then have "?trace_openings ! j = []"
        using j_bound by simp
      then show ?thesis
        unfolding partial_authenticated_table_def by simp
    qed
  qed
  have composition_tables:
    "\<And>j. j < rounds \<Longrightarrow>
      partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) (?composition_openings ! j) prefix_state"
  proof -
    fix j
    assume j_bound: "j < rounds"
    show
      "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) (?composition_openings ! j) prefix_state"
    proof (cases "j = 0")
      case True
      then show ?thesis
        using composition_table zero_bound by simp
    next
      case False
      then have "?composition_openings ! j = []"
        using j_bound by simp
      then show ?thesis
        unfolding partial_authenticated_table_def by simp
    qed
  qed
  have opening_target:
    "idx \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ?trace_openings ?composition_openings 0 prefix prefix_state"
    unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
    by (rule partial_query_success_indices_atI,
        rule partial_query_round_consistent_single_roundI
          [OF zero_bound consistent])
  have target_subset:
    "staged_query_prefix_candidate_opening_query_target_from_prefix
        ?trace_openings ?composition_openings 0 prefix prefix_state \<subseteq>
      staged_query_prefix_conceptual_query_target prefix prefix_state"
    by (rule
        staged_query_prefix_candidate_opening_query_target_from_prefix_subset_conceptual
        [OF clean trace_len composition_len trace_tables composition_tables
          trace_low composition_low not_all])
  show
    "idx \<in> staged_query_prefix_conceptual_query_target prefix prefix_state"
  using opening_target target_subset by blast
qed

lemma staged_query_prefix_prefix_authenticated_opening_target_fraction_bound_if_conceptual:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
    and trace_low:
      "trace_table_low_degree
        (query_prefix_trace_conceptual_table prefix prefix_state)"
    and composition_low:
      "composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table prefix prefix_state)"
    and not_all:
      "\<not> all_queries_consistent
        (query_prefix_trace_conceptual_table prefix prefix_state)
        (query_prefix_composition_conceptual_table prefix prefix_state)
        (sqp_alphas prefix)"
  shows
    "nnreal
      (card
        (staged_query_prefix_prefix_authenticated_opening_target prefix
          prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
proof -
  have subset:
    "staged_query_prefix_prefix_authenticated_opening_target prefix
      prefix_state \<subseteq>
     staged_query_prefix_conceptual_query_target prefix prefix_state"
    by (rule
        staged_query_prefix_prefix_authenticated_opening_target_subset_conceptual
        [OF clean trace_low composition_low not_all])
  have finite_conceptual:
    "finite (staged_query_prefix_conceptual_query_target prefix prefix_state)"
    by (rule finite_subset
        [OF staged_query_prefix_conceptual_query_target_subset
          finite_query_sample_space])
  have card_le:
    "card
      (staged_query_prefix_prefix_authenticated_opening_target prefix
        prefix_state) \<le>
     card (staged_query_prefix_conceptual_query_target prefix prefix_state)"
    by (rule card_mono[OF finite_conceptual subset])
  have frac_le:
    "nnreal
      (card
        (staged_query_prefix_prefix_authenticated_opening_target prefix
          prefix_state)) /
      nnreal (card query_sample_space) \<le>
     nnreal
      (card
        (staged_query_prefix_conceptual_query_target prefix prefix_state)) /
      nnreal (card query_sample_space)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  show ?thesis
    by (rule order_trans[OF frac_le
    staged_query_prefix_conceptual_query_target_fraction_bound])
qed

lemma staged_query_prefix_prefix_authenticated_opening_target_subset_conceptual_default:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
    and trace_low:
      "trace_table_low_degree
        (query_prefix_trace_conceptual_table_with_default prefix
          prefix_state trace_default)"
    and composition_low:
      "composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default)"
    and not_all:
      "\<not> all_queries_consistent
        (query_prefix_trace_conceptual_table_with_default prefix
          prefix_state trace_default)
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default)
        (sqp_alphas prefix)"
  shows
    "staged_query_prefix_prefix_authenticated_opening_target prefix
      prefix_state \<subseteq>
     staged_query_prefix_conceptual_default_query_target trace_default
      composition_default prefix prefix_state"
proof
  fix idx
  assume idx_in:
    "idx \<in> staged_query_prefix_prefix_authenticated_opening_target prefix
      prefix_state"
  then obtain trace_openings composition_openings where
    trace_table:
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) trace_openings prefix_state"
    and composition_table:
      "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) composition_openings prefix_state"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (sqp_alphas prefix) idx"
    unfolding staged_query_prefix_prefix_authenticated_opening_target_def
    by blast
  let ?trace_openings =
    "(replicate rounds []) [0 := trace_openings]"
  let ?composition_openings =
    "(replicate rounds []) [0 := composition_openings]"
  have zero_bound: "0 < rounds"
    by (rule rounds_positive)
  have trace_len: "length ?trace_openings = rounds"
    by simp
  have composition_len: "length ?composition_openings = rounds"
    by simp
  have trace_tables:
    "\<And>j. j < rounds \<Longrightarrow>
      partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) (?trace_openings ! j) prefix_state"
  proof -
    fix j
    assume j_bound: "j < rounds"
    show
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) (?trace_openings ! j) prefix_state"
    proof (cases "j = 0")
      case True
      then show ?thesis
        using trace_table zero_bound by simp
    next
      case False
      then have "?trace_openings ! j = []"
        using j_bound by simp
      then show ?thesis
        unfolding partial_authenticated_table_def by simp
    qed
  qed
  have composition_tables:
    "\<And>j. j < rounds \<Longrightarrow>
      partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) (?composition_openings ! j) prefix_state"
  proof -
    fix j
    assume j_bound: "j < rounds"
    show
      "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) (?composition_openings ! j) prefix_state"
    proof (cases "j = 0")
      case True
      then show ?thesis
        using composition_table zero_bound by simp
    next
      case False
      then have "?composition_openings ! j = []"
        using j_bound by simp
      then show ?thesis
        unfolding partial_authenticated_table_def by simp
    qed
  qed
  have opening_target:
    "idx \<in>
      staged_query_prefix_candidate_opening_query_target_from_prefix
        ?trace_openings ?composition_openings 0 prefix prefix_state"
    unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
    by (rule partial_query_success_indices_atI,
        rule partial_query_round_consistent_single_roundI
          [OF zero_bound consistent])
  have target_subset:
    "staged_query_prefix_candidate_opening_query_target_from_prefix
        ?trace_openings ?composition_openings 0 prefix prefix_state \<subseteq>
      staged_query_prefix_conceptual_default_query_target trace_default
        composition_default prefix prefix_state"
    by (rule
        staged_query_prefix_candidate_opening_query_target_from_prefix_subset_conceptual_default
        [OF clean trace_len composition_len trace_tables composition_tables
          trace_low composition_low not_all])
  show
    "idx \<in>
      staged_query_prefix_conceptual_default_query_target trace_default
        composition_default prefix prefix_state"
    using opening_target target_subset by blast
qed

definition checked_staged_security_with_query_prefix_conceptual_context_residual_at
where
  "checked_staged_security_with_query_prefix_conceptual_context_residual_at
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        hash_map_output_collision prefix_state \<or>
        \<not> trace_table_low_degree
          (query_prefix_trace_conceptual_table prefix prefix_state) \<or>
        \<not> composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table prefix prefix_state) \<or>
        all_queries_consistent
          (query_prefix_trace_conceptual_table prefix prefix_state)
          (query_prefix_composition_conceptual_table prefix prefix_state)
          (sqp_alphas prefix))"

definition checked_staged_security_with_query_prefix_conceptual_default_context_residual_at
where
  "checked_staged_security_with_query_prefix_conceptual_default_context_residual_at
      trace_default composition_default out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        hash_map_output_collision prefix_state \<or>
        \<not> trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default) \<or>
        \<not> composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default) \<or>
        all_queries_consistent
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default)
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default)
          (sqp_alphas prefix))"

lemma checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_imp_conceptual_or_residual_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i out"
  shows
    "checked_staged_security_with_query_prefix_conceptual_target_hit out \<or>
     checked_staged_security_with_query_prefix_conceptual_context_residual_at
        out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_def
      checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state data attacker_state result
      final_state where out_eq:
    "out =
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)"
    by (cases packed) (auto split: prod.splits)
  show ?thesis
  proof (cases
      "\<not> hash_map_output_collision prefix_state \<and>
       trace_table_low_degree
        (query_prefix_trace_conceptual_table prefix prefix_state) \<and>
       composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table prefix prefix_state) \<and>
       \<not> all_queries_consistent
        (query_prefix_trace_conceptual_table prefix prefix_state)
        (query_prefix_composition_conceptual_table prefix prefix_state)
        (sqp_alphas prefix)")
    case False
    then have
      "checked_staged_security_with_query_prefix_conceptual_context_residual_at
        out"
      unfolding out_eq
        checked_staged_security_with_query_prefix_conceptual_context_residual_at_def
      by simp
    then show ?thesis by simp
  next
    case True
    then have clean:
        "\<not> hash_map_output_collision prefix_state"
      and trace_low:
        "trace_table_low_degree
          (query_prefix_trace_conceptual_table prefix prefix_state)"
      and composition_low:
        "composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table prefix prefix_state)"
      and not_all:
        "\<not> all_queries_consistent
          (query_prefix_trace_conceptual_table prefix prefix_state)
          (query_prefix_composition_conceptual_table prefix prefix_state)
          (sqp_alphas prefix)"
      by blast+
    have prefix_hit:
      "checked_staged_security_with_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target out"
      by (rule
          checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_imp_dynamic_target
          [OF wf controlled i_bound support hit])
    have subset:
      "staged_query_prefix_prefix_authenticated_opening_target prefix
          prefix_state \<subseteq>
       staged_query_prefix_conceptual_query_target prefix prefix_state"
      by (rule
          staged_query_prefix_prefix_authenticated_opening_target_subset_conceptual
          [OF clean trace_low composition_low not_all])
    have conceptual_hit:
      "checked_staged_security_with_query_prefix_conceptual_target_hit out"
      using prefix_hit subset
      unfolding out_eq
        checked_staged_security_with_query_prefix_conceptual_target_hit_def
        checked_staged_security_with_query_prefix_dynamic_index_hit_def
        checked_staged_query_prefix_dynamic_index_hit_def
      by auto
    then show ?thesis by simp
  qed
qed

lemma checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_conceptual_residual:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and residual_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        checked_staged_security_with_query_prefix_conceptual_context_residual_at
        adversary_initial_state \<le> R"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + R"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Conceptual =
    "checked_staged_security_with_query_prefix_conceptual_target_hit"
  let ?Residual =
    "checked_staged_security_with_query_prefix_conceptual_context_residual_at"
  have event_le:
    "wp_event ?M
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i)
      adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?Conceptual out \<or> ?Residual out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_imp_conceptual_or_residual_on_support
        [OF wf controlled i_bound])
  have conceptual_bound:
    "wp_event ?M ?Conceptual adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_target_hit_bound
        [OF wf controlled i_bound])
  have union_bound:
    "wp_event ?M (\<lambda>out. ?Conceptual out \<or> ?Residual out)
      adversary_initial_state \<le>
     wp_event ?M ?Conceptual adversary_initial_state +
     wp_event ?M ?Residual adversary_initial_state"
    by (rule wp_event_union_bound)
  have sum_bound:
    "wp_event ?M ?Conceptual adversary_initial_state +
     wp_event ?M ?Residual adversary_initial_state \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound) +
      R"
    by (intro add_mono conceptual_bound residual_bound)
  show ?thesis
    by (rule order_trans[OF event_le])
      (rule order_trans[OF union_bound sum_bound])
qed

lemma checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_imp_conceptual_default_or_residual_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i out"
  shows
    "checked_staged_security_with_query_prefix_conceptual_default_target_hit
        trace_default composition_default out \<or>
     checked_staged_security_with_query_prefix_conceptual_default_context_residual_at
        trace_default composition_default out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_def
      checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state data attacker_state result
      final_state where out_eq:
    "out =
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)"
    by (cases packed) (auto split: prod.splits)
  show ?thesis
  proof (cases
      "\<not> hash_map_output_collision prefix_state \<and>
       trace_table_low_degree
        (query_prefix_trace_conceptual_table_with_default prefix
          prefix_state trace_default) \<and>
       composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default) \<and>
       \<not> all_queries_consistent
        (query_prefix_trace_conceptual_table_with_default prefix
          prefix_state trace_default)
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default)
        (sqp_alphas prefix)")
    case False
    then have
      "checked_staged_security_with_query_prefix_conceptual_default_context_residual_at
        trace_default composition_default out"
      unfolding out_eq
        checked_staged_security_with_query_prefix_conceptual_default_context_residual_at_def
      by simp
    then show ?thesis by simp
  next
    case True
    then have clean:
        "\<not> hash_map_output_collision prefix_state"
      and trace_low:
        "trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default)"
      and composition_low:
        "composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default)"
      and not_all:
        "\<not> all_queries_consistent
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default)
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default)
          (sqp_alphas prefix)"
      by blast+
    have prefix_hit:
      "checked_staged_security_with_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target out"
      by (rule
          checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_imp_dynamic_target
          [OF wf controlled i_bound support hit])
    have subset:
      "staged_query_prefix_prefix_authenticated_opening_target prefix
          prefix_state \<subseteq>
       staged_query_prefix_conceptual_default_query_target trace_default
        composition_default prefix prefix_state"
      by (rule
          staged_query_prefix_prefix_authenticated_opening_target_subset_conceptual_default
          [OF clean trace_low composition_low not_all])
    have conceptual_hit:
      "checked_staged_security_with_query_prefix_conceptual_default_target_hit
        trace_default composition_default out"
      using prefix_hit subset
      unfolding out_eq
        checked_staged_security_with_query_prefix_conceptual_default_target_hit_def
        checked_staged_security_with_query_prefix_dynamic_index_hit_def
        checked_staged_query_prefix_dynamic_index_hit_def
      by auto
    then show ?thesis by simp
  qed
qed

lemma checked_staged_query_prefix_prefix_authenticated_target_hit_bound_from_conceptual:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and conceptual_context:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        \<not> hash_map_output_collision prefix_state \<and>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table prefix prefix_state) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table prefix prefix_state) \<and>
        \<not> all_queries_consistent
          (query_prefix_trace_conceptual_table prefix prefix_state)
          (query_prefix_composition_conceptual_table prefix prefix_state)
          (sqp_alphas prefix)"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    have ctx:
      "\<not> hash_map_output_collision prefix_state \<and>
       trace_table_low_degree
        (query_prefix_trace_conceptual_table prefix prefix_state) \<and>
       composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table prefix prefix_state) \<and>
       \<not> all_queries_consistent
        (query_prefix_trace_conceptual_table prefix prefix_state)
        (query_prefix_composition_conceptual_table prefix prefix_state)
        (sqp_alphas prefix)"
      by (rule conceptual_context[OF support])
    have subset:
      "staged_query_prefix_prefix_authenticated_opening_target prefix
          prefix_state \<subseteq> query_sample_space"
      by (rule staged_query_prefix_prefix_authenticated_opening_target_subset)
    have frac:
      "nnreal
        (card
          (staged_query_prefix_prefix_authenticated_opening_target prefix
            prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      using ctx
      by (intro
          staged_query_prefix_prefix_authenticated_opening_target_fraction_bound_if_conceptual)
        blast+
    show
      "staged_query_prefix_prefix_authenticated_opening_target prefix
          prefix_state \<subseteq> query_sample_space \<and>
       nnreal
        (card
          (staged_query_prefix_prefix_authenticated_opening_target prefix
            prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      using subset frac by blast
  qed
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
  proof (rule
      checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
    show "HashMap adversary_initial_state = fmempty"
      by (simp add: adversary_initial_state_def)
    show "hash_relation_program
        (checked_staged_query_prefix_dynamic_index_prehit_relation A i
          adversary_initial_state
          staged_query_prefix_prefix_authenticated_opening_target)
        size (staged_query_search_queries budgets i + 1)
        (checked_staged_query_prefix_receive_with_state A i)"
      by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
          [OF wf controlled])
        (use i_bound in simp_all,
          rule checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
  qed
  show ?thesis
    by (rule order_trans[OF hit_bound])
      (intro add_mono prehit_bound order_refl)
qed

end

end
