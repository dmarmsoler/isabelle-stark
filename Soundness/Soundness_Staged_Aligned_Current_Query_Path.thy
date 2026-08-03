(*  Title:      Stark/Soundness_Staged_Aligned_Current_Query_Path.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Aligned_Current_Query_Path
  imports
    Soundness_Staged_Aligned_Current_Query
    Soundness_Conceptual_Query_Current_Candidate
begin

text \<open>
  Current-query wrappers that use structured Merkle path-output events.

  This layer keeps trace and composition authenticated-opening path outputs
  separate, which is the form needed for Merkle and candidate uniqueness
  arguments in the staged soundness proof.
\<close>

context soundness
begin

theorem stark_soundness_from_aligned_partial_query_prefix_current_prefix_structured_paths:
  fixes trace_fri_error' composition_fri_error' N :: prob
    and P T C :: "nat \<Rightarrow> prob"
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
    and prefix_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
          adversary_initial_state \<le> P i"
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
    (\<Sum>i<rounds. P i + T i + C i) +
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
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le> P i + T i + C i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_prefix_and_structured_paths
        [OF wf controlled i_bound prefix_bound[OF i_bound]
          trace_path_bound[OF i_bound] composition_path_bound[OF i_bound]])
qed (rule not_prefix_bound empty_trace_fri_bound empty_query_bound)+

theorem stark_soundness_from_aligned_partial_query_prefix_dynamic_target_structured_paths:
  fixes trace_fri_error' composition_fri_error' N :: prob
    and P T C :: "nat \<Rightarrow> prob"
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
    and prefix_target_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_query_prefix_receive_with_state A i)
          (checked_staged_query_prefix_dynamic_index_hit
            staged_query_prefix_prefix_authenticated_opening_target)
          adversary_initial_state \<le> P i"
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
    (\<Sum>i<rounds. P i + T i + C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
proof -
  have prefix_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
        adversary_initial_state \<le> P i"
    by (rule
        checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_dynamic_target
        [OF wf controlled _ prefix_target_bound])
  show ?thesis
    by (rule
        stark_soundness_from_aligned_partial_query_prefix_current_prefix_structured_paths
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          prefix_bound trace_path_bound composition_path_bound not_prefix_bound
          empty_trace_fri_bound empty_query_bound])
qed

theorem stark_soundness_from_aligned_partial_query_prefix_trace_index_structured_paths:
  fixes trace_fri_error' composition_fri_error' N :: prob
    and T C :: "nat \<Rightarrow> prob"
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
    and trace_frac:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        nnreal
          (card
            (staged_query_prefix_prefix_authenticated_trace_indices prefix
              prefix_state)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
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
      query_error_bound + T i + C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
proof (rule
    stark_soundness_from_aligned_partial_query_prefix_dynamic_target_structured_paths
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound _ trace_path_bound
      composition_path_bound not_prefix_bound empty_trace_fri_bound empty_query_bound])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_query_prefix_prefix_authenticated_target_hit_bound_from_trace_indices
        [OF wf controlled i_bound])
      (use trace_frac[OF i_bound] in blast)
qed

theorem stark_soundness_from_aligned_partial_query_prefix_conceptual_structured_paths:
  fixes trace_fri_error' composition_fri_error' N :: prob
    and T C :: "nat \<Rightarrow> prob"
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
    and conceptual_context:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
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
      query_error_bound + T i + C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
proof (rule
    stark_soundness_from_aligned_partial_query_prefix_dynamic_target_structured_paths
    [OF false_statement wf controlled trace_fri_bound comp_fri_bound _ trace_path_bound
      composition_path_bound not_prefix_bound empty_trace_fri_bound empty_query_bound])
  fix i
  assume i_bound: "i < rounds"
  show
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_query_prefix_prefix_authenticated_target_hit_bound_from_conceptual
        [OF wf controlled i_bound])
      (rule conceptual_context[OF i_bound])
qed

theorem stark_soundness_from_aligned_partial_query_prefix_conceptual_default_structured_paths:
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
    and default_context:
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
        \<not> all_queries_consistent
          (query_prefix_trace_conceptual_table_with_default prefix
            prefix_state trace_default)
          (query_prefix_composition_conceptual_table_with_default prefix
            prefix_state composition_default)
          (sqp_alphas prefix)"
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
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_conceptual_default_context_and_structured_paths
        [OF wf controlled i_bound _ trace_path_bound[OF i_bound]
          composition_path_bound[OF i_bound]])
      (rule default_context[OF i_bound])
qed

end

end
