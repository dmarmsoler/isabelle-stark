(*  Title:      Stark/Soundness_Relevant_Drift_Public.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Relevant_Drift_Public
  imports
    Soundness
    Soundness_Staged_Empty_Relevant_Drift
begin

text \<open>
  Public migration wrappers for the refined relevant-drift route.

  These theorems sit downstream of \<open>Soundness\<close> so the main public
  compatibility layer does not keep growing.  The route below derives the
  aligned composition-randomization branch and aligned query branch from the
  same per-round current-query prefix bounds.  It exposes only the
  empty-header-specific relevant-drift event and keeps the partial-candidate
  FRI premises internal to this route.
\<close>

context soundness
begin

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query:
  fixes trace_fri_error' composition_fri_error' D empty_query_error :: prob
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
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
        adversary_initial_state \<le> D"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (\<Sum>i<rounds. C i) +
      trace_fri_error' + composition_fri_error' +
      (\<Sum>i<rounds. C i) +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        D + trace_fri_error + empty_query_error)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_current_query_prefix_rounds_from_empty_relevant_drift_current_empty
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          round_bound drift_bound empty_trace_fri_bound current_empty_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

theorem stark_soundness_from_aligned_partial_components_current_query_prefix_and_current_empty_query_single_query_charge:
  fixes trace_fri_error' composition_fri_error' D empty_query_error :: prob
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
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        checked_staged_security_with_actual_alpha_prefix_empty_header_relevant_drift
        adversary_initial_state \<le> D"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (\<Sum>i<rounds. C i) +
    trace_fri_error' + composition_fri_error' +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error)"
proof -
  have bound:
    "checked_staged_adversary_acceptance_probability A \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      (\<Sum>i<rounds. C i) +
      trace_fri_error' + composition_fri_error' +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        D + trace_fri_error + empty_query_error)"
    by (rule
        checked_staged_soundness_from_aligned_transcript_aligned_randomization_components_and_current_query_prefix_rounds_from_empty_relevant_drift_current_empty_single_query_charge
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          round_bound drift_bound empty_trace_fri_bound current_empty_bound])
  then show ?thesis
    by (simp add: algebra_simps)
qed

end

end
