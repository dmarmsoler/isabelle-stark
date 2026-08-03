(*  Title:      Stark/Soundness_Staged_Aligned_Current_Query.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Aligned_Current_Query
  imports Soundness_Staged_Aligned_Partial_Merkle
begin

text \<open>
  Thin wrappers that expose the actual-alpha current-query event in the aligned
  partial-candidate soundness path.  The underlying query reduction still lives
  in the partial-Merkle layer; this theory only uses the projection proved in
  the current-query alignment layer.
\<close>

context soundness
begin

lemma checked_staged_soundness_from_aligned_transcript_components_and_actual_alpha_current_partial_opening_hit_from_not_prefix:
  fixes trace_fri_error' composition_fri_error' query_error N :: prob
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
    and current_query_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
        adversary_initial_state \<le> query_error"
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
    query_error +
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
  have data_current_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> query_error"
    by (rule
        checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_actual_alpha_current_query
        [OF current_query_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_aligned_transcript_components_and_current_partial_opening_hit_from_not_prefix
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          data_current_query_bound not_prefix_bound empty_trace_fri_bound
          empty_query_bound])
qed

theorem stark_soundness_from_aligned_partial_actual_alpha_current_query:
  fixes trace_fri_error' composition_fri_error' query_error N :: prob
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
    and current_query_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
        adversary_initial_state \<le> query_error"
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
    query_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      N +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound)"
  by (rule
      checked_staged_soundness_from_aligned_transcript_components_and_actual_alpha_current_partial_opening_hit_from_not_prefix
      [OF false_statement wf controlled trace_fri_bound comp_fri_bound
        current_query_bound not_prefix_bound empty_trace_fri_bound
        empty_query_bound])

theorem stark_soundness_from_aligned_partial_query_prefix_current_rounds:
  fixes trace_fri_error' composition_fri_error' N :: prob
    and C :: "nat \<Rightarrow> prob"
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
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
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
    (\<Sum>i<rounds. C i) +
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
  have current_query_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_current_query_partial_opening_hit_bound_from_query_prefix_current_rounds
        [OF wf controlled round_bound])
  show ?thesis
    by (rule
        stark_soundness_from_aligned_partial_actual_alpha_current_query
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          current_query_bound not_prefix_bound empty_trace_fri_bound
          empty_query_bound])
qed

theorem stark_soundness_from_aligned_partial_query_prefix_current_prefix_path:
  fixes trace_fri_error' composition_fri_error' N :: prob
    and P Q :: "nat \<Rightarrow> prob"
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
    and path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_path_output_hit_at i)
          adversary_initial_state \<le> Q i"
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
    (\<Sum>i<rounds. P i + Q i) +
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
      adversary_initial_state \<le> P i + Q i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_prefix_and_path
        [OF wf controlled i_bound prefix_bound[OF i_bound]
      path_bound[OF i_bound]])
qed (rule not_prefix_bound empty_trace_fri_bound empty_query_bound)+

theorem stark_soundness_from_aligned_partial_query_prefix_dynamic_target_path:
  fixes trace_fri_error' composition_fri_error' N :: prob
    and P Q :: "nat \<Rightarrow> prob"
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
    and path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_path_output_hit_at i)
          adversary_initial_state \<le> Q i"
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
    (\<Sum>i<rounds. P i + Q i) +
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
    by (rule stark_soundness_from_aligned_partial_query_prefix_current_prefix_path
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          prefix_bound path_bound not_prefix_bound empty_trace_fri_bound
          empty_query_bound])
qed

end

end
