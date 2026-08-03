(*  Title:      Stark/Soundness_Conceptual_Query_Current_Alpha_Clean.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Conceptual_Query_Current_Alpha_Clean
  imports Soundness_Staged_Aligned_Current_Query_Path
begin

text \<open>
  Alpha-clean wrappers for the default-backed conceptual current-query route.

  This layer derives the default-context non-consistency premise from the
  false statement, low degree of the fixed default tables, and the fact that
  the sampled alpha vector is not in the corresponding composition bad set.
\<close>

context soundness
begin

lemma checked_staged_security_with_query_prefix_conceptual_default_context_from_alpha_clean:
  assumes false_statement: "\<not> exists_valid_trace"
    and alphas_length: "length (sqp_alphas prefix) = length spec"
    and trace_low:
      "trace_table_low_degree
        (query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_default)"
    and composition_low:
      "composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default)"
    and alpha_clean:
      "sqp_alphas prefix \<notin> composition_trace_bad_alpha_space
        (query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_default)"
  shows
    "trace_table_low_degree
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default) \<and>
     composition_table_low_degree maxDegree
      (query_prefix_composition_conceptual_table_with_default prefix
        prefix_state composition_default) \<and>
     \<not> all_queries_consistent
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default)
      (query_prefix_composition_conceptual_table_with_default prefix
        prefix_state composition_default)
      (sqp_alphas prefix)"
proof (intro conjI trace_low composition_low notI)
  assume all_queries:
    "all_queries_consistent
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default)
      (query_prefix_composition_conceptual_table_with_default prefix
        prefix_state composition_default)
      (sqp_alphas prefix)"
  have alpha_bad:
    "sqp_alphas prefix \<in> composition_trace_bad_alpha_space
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default)"
    by (rule low_degree_all_queries_consistent_imp_composition_trace_bad_alpha_space
        [OF false_statement alphas_length trace_low composition_low all_queries])
  show False
    using alpha_clean alpha_bad by simp
qed

lemma checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_bound_from_alpha_clean:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and default_alpha_clean:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default) \<and>
        sqp_alphas prefix \<notin> composition_trace_bad_alpha_space
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_default composition_default i)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
proof (rule
    checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_bound_from_context
    [OF wf controlled i_bound])
  fix prefix prefix_state
  assume prefix_support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i)
          adversary_initial_state)"
  from default_alpha_clean[OF prefix_support] have trace_low:
      "trace_table_low_degree
        (query_prefix_trace_conceptual_table_with_default prefix
          prefix_state trace_default)"
    and composition_low:
      "composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default)"
    and alpha_clean:
      "sqp_alphas prefix \<notin> composition_trace_bad_alpha_space
        (query_prefix_trace_conceptual_table_with_default prefix
          prefix_state trace_default)"
    by blast+
  have alphas_length: "length (sqp_alphas prefix) = length spec"
    by (rule checked_staged_query_prefix_with_state_alphas_length
        [OF prefix_support])
  show
    "trace_table_low_degree
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default) \<and>
     composition_table_low_degree maxDegree
      (query_prefix_composition_conceptual_table_with_default prefix
        prefix_state composition_default) \<and>
     \<not> all_queries_consistent
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default)
      (query_prefix_composition_conceptual_table_with_default prefix
        prefix_state composition_default)
      (sqp_alphas prefix)"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_default_context_from_alpha_clean
        [OF false_statement alphas_length trace_low composition_low alpha_clean])
qed

lemma query_prefix_default_alpha_clean_from_alpha_prefix_union_clean:
  assumes trace_eq:
      "query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default = trace_default"
    and trace_candidate:
      "trace_default \<in>
        alpha_prefix_trace_table_candidates prefix_state (sqp_trace_root prefix)"
    and union_clean:
      "sqp_alphas prefix \<notin>
        alpha_prefix_union_bad_sets prefix_state composition_trace_bad_alpha_space
          (sqp_trace_root prefix)"
  shows
    "sqp_alphas prefix \<notin> composition_trace_bad_alpha_space
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default)"
proof
  assume alpha_bad:
    "sqp_alphas prefix \<in> composition_trace_bad_alpha_space
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default)"
  have alpha_space:
    "sqp_alphas prefix \<in> alpha_space"
    using alpha_bad composition_trace_bad_alpha_space_subset_alpha_space
    by blast
  have
    "sqp_alphas prefix \<in>
      alpha_prefix_union_bad_sets prefix_state composition_trace_bad_alpha_space
        (sqp_trace_root prefix)"
    unfolding alpha_prefix_union_bad_sets_def
    using trace_candidate alpha_bad trace_eq alpha_space by auto
  then show False
    using union_clean by simp
qed

lemma checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_bound_from_alpha_prefix_union_clean:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and default_prefix_clean:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_default = trace_default \<and>
        query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default = composition_default \<and>
        trace_table_low_degree trace_default \<and>
        composition_table_low_degree maxDegree composition_default \<and>
        trace_default \<in>
          alpha_prefix_trace_table_candidates prefix_state
            (sqp_trace_root prefix) \<and>
        sqp_alphas prefix \<notin>
          alpha_prefix_union_bad_sets prefix_state
            composition_trace_bad_alpha_space (sqp_trace_root prefix)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_default composition_default i)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
proof (rule
    checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_bound_from_alpha_clean
    [OF false_statement wf controlled i_bound])
  fix prefix prefix_state
  assume prefix_support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i)
          adversary_initial_state)"
  from default_prefix_clean[OF prefix_support] have trace_eq:
      "query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default = trace_default"
    and composition_eq:
      "query_prefix_composition_conceptual_table_with_default prefix
        prefix_state composition_default = composition_default"
    and trace_low: "trace_table_low_degree trace_default"
    and composition_low:
      "composition_table_low_degree maxDegree composition_default"
    and trace_candidate:
      "trace_default \<in>
        alpha_prefix_trace_table_candidates prefix_state
          (sqp_trace_root prefix)"
    and union_clean:
      "sqp_alphas prefix \<notin>
        alpha_prefix_union_bad_sets prefix_state
          composition_trace_bad_alpha_space (sqp_trace_root prefix)"
    by blast+
  have alpha_clean:
    "sqp_alphas prefix \<notin> composition_trace_bad_alpha_space
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default)"
    by (rule query_prefix_default_alpha_clean_from_alpha_prefix_union_clean
        [OF trace_eq trace_candidate union_clean])
  show
    "trace_table_low_degree
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default) \<and>
     composition_table_low_degree maxDegree
      (query_prefix_composition_conceptual_table_with_default prefix
        prefix_state composition_default) \<and>
     sqp_alphas prefix \<notin> composition_trace_bad_alpha_space
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default)"
    using trace_eq composition_eq trace_low composition_low alpha_clean by simp
qed

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_alpha_clean_and_structured_paths:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and default_alpha_clean:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default) \<and>
        sqp_alphas prefix \<notin> composition_trace_bad_alpha_space
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default)"
    and trace_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
        adversary_initial_state \<le> T"
    and composition_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
proof -
  have residual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_default composition_default i)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_bound_from_alpha_clean
        [OF false_statement wf controlled i_bound default_alpha_clean])
  have bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_residual_and_structured_paths
        [OF wf controlled i_bound residual_bound trace_path_bound
          composition_path_bound])
  show ?thesis
    using bound by simp
qed

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_alpha_prefix_union_clean_and_structured_paths:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and default_prefix_clean:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_default = trace_default \<and>
        query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default = composition_default \<and>
        trace_table_low_degree trace_default \<and>
        composition_table_low_degree maxDegree composition_default \<and>
        trace_default \<in>
          alpha_prefix_trace_table_candidates prefix_state
            (sqp_trace_root prefix) \<and>
        sqp_alphas prefix \<notin>
          alpha_prefix_union_bad_sets prefix_state
            composition_trace_bad_alpha_space (sqp_trace_root prefix)"
    and trace_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
        adversary_initial_state \<le> T"
    and composition_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
proof -
  have residual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_default composition_default i)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_bound_from_alpha_prefix_union_clean
        [OF false_statement wf controlled i_bound default_prefix_clean])
  have bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_residual_and_structured_paths
        [OF wf controlled i_bound residual_bound trace_path_bound
          composition_path_bound])
  show ?thesis
    using bound by simp
qed

lemma checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_bound_from_conceptual_default_alpha_clean_and_structured_paths:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and default_alpha_clean:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_table) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_table) \<and>
        sqp_alphas prefix \<notin> composition_trace_bad_alpha_space
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_table)"
    and trace_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
        adversary_initial_state \<le> T"
    and composition_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
proof -
  have residual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_default_context_residual_hit_at_bound_from_alpha_clean
        [OF false_statement wf controlled i_bound default_alpha_clean])
  have bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
    by (rule
        checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_bound_from_conceptual_default_residual_and_structured_paths
        [OF wf controlled i_bound residual_bound trace_path_bound
          composition_path_bound])
  show ?thesis
    using bound by simp
qed

lemma staged_security_with_data_state_current_query_partial_candidate_hit_at_bound_from_conceptual_default_alpha_clean:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and default_alpha_clean:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_table) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_table) \<and>
        sqp_alphas prefix \<notin> composition_trace_bad_alpha_space
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_table)"
    and trace_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
        adversary_initial_state \<le> T"
    and composition_path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
        adversary_initial_state \<le> C"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_query_partial_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
proof -
  have prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_authenticated_candidate_hit_at
        trace_table composition_table i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) + T + C"
    by (rule
        checked_staged_security_with_query_prefix_authenticated_candidate_hit_at_bound_from_conceptual_default_alpha_clean_and_structured_paths
        [OF false_statement wf controlled i_bound default_alpha_clean
          trace_path_bound composition_path_bound])
  show ?thesis
    by (rule order_trans
        [OF
          staged_security_with_data_state_current_query_partial_candidate_hit_at_le_query_prefix_authenticated_candidate
          prefix_bound])
      (use wf controlled i_bound in simp_all)
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_conceptual_default_alpha_clean_and_structured_paths:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and default_alpha_clean:
      "\<And>i prefix prefix_state. i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default) \<and>
        sqp_alphas prefix \<notin> composition_trace_bad_alpha_space
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default)"
    and trace_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
          adversary_initial_state \<le> T i"
    and composition_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
          adversary_initial_state \<le> C i"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound +
        hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1) +
        T i + C i)"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_prefix_current_rounds
    [OF wf controlled])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      T i + C i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_alpha_clean_and_structured_paths
        [OF false_statement wf controlled i_bound _ trace_path_bound[OF i_bound]
          composition_path_bound[OF i_bound]])
      (rule default_alpha_clean[OF i_bound])
qed

theorem stark_soundness_from_aligned_partial_query_prefix_conceptual_default_alpha_clean_structured_paths:
  fixes trace_fri_error' composition_fri_error' N :: prob
    and T C :: "nat \<Rightarrow> prob"
    and trace_default composition_default :: "'f list"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_fri_error'"
    and default_alpha_clean:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default) \<and>
        composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default) \<and>
        sqp_alphas prefix \<notin> composition_trace_bad_alpha_space
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default)"
    and trace_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
          adversary_initial_state \<le> T i"
    and composition_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
          adversary_initial_state \<le> C i"
    and not_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> N"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      T i + C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
proof (rule stark_soundness_from_aligned_partial_query_prefix_current_rounds
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound _ not_prefix_bound
      empty_trace_fri_bound empty_query_bound])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      T i + C i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_alpha_clean_and_structured_paths
        [OF false_statement wf controlled i_bound _ trace_path_bound[OF i_bound]
          composition_path_bound[OF i_bound]])
      (rule default_alpha_clean[OF i_bound])
qed

theorem stark_soundness_from_aligned_partial_query_prefix_conceptual_default_alpha_prefix_union_clean_structured_paths:
  fixes trace_fri_error' composition_fri_error' N :: prob
    and T C :: "nat \<Rightarrow> prob"
    and trace_default composition_default :: "'f list"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_fri_error'"
    and default_prefix_clean:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_default = trace_default \<and>
        query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default = composition_default \<and>
        trace_table_low_degree trace_default \<and>
        composition_table_low_degree maxDegree composition_default \<and>
        trace_default \<in>
          alpha_prefix_trace_table_candidates prefix_state
            (sqp_trace_root prefix) \<and>
        sqp_alphas prefix \<notin>
          alpha_prefix_union_bad_sets prefix_state
            composition_trace_bad_alpha_space (sqp_trace_root prefix)"
    and trace_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at i)
          adversary_initial_state \<le> T i"
    and composition_path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at i)
          adversary_initial_state \<le> C i"
    and not_prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_not_prefix_bound
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> N"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and empty_query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      T i + C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
proof (rule stark_soundness_from_aligned_partial_query_prefix_current_rounds
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound _ not_prefix_bound
      empty_trace_fri_bound empty_query_bound])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      T i + C i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_alpha_prefix_union_clean_and_structured_paths
        [OF false_statement wf controlled i_bound _ trace_path_bound[OF i_bound]
          composition_path_bound[OF i_bound]])
      (rule default_prefix_clean[OF i_bound])
qed

end

end
