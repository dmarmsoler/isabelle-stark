(*  Title:      Stark/Soundness_Public_Route_Single_Query.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Public_Route_Single_Query
  imports
    Soundness_FRI_Verifier_Tied
    Soundness_Not_Prefix_Partial_Opening
begin

text \<open>
  Narrow downstream wrappers for the public route that use the
  transcript-indexed single-current-query charge.  This theory depends directly
  on the partial-opening route needed by the final endpoint.
\<close>

context soundness
begin

theorem stark_soundness_from_transcript_indexed_partial_opening_route_from_sampled_transcript_relevant_drift_only_single_query_charge_from_active_fri_bounds:
  fixes P trace_fri_error' composition_fri_error'
    empty_trace_fri_error' empty_query_error :: prob
    and C :: "nat \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
    and data_pre_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_transcript_pre_hit
        adversary_initial_state \<le> P"
    and current_empty_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
        adversary_initial_state \<le> empty_query_error"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_partial_candidate)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_verifier_tied_partial_candidate)
        adversary_initial_state \<le> composition_fri_error'"
    and empty_trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> empty_trace_fri_error'"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    hash_collision_budget_value 0
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (P + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error' + composition_fri_error' +
    (\<Sum>i<rounds. C i) +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (P + staged_concrete_transcript_target_error_bound) +
      empty_trace_fri_error' + empty_query_error)"
proof -
  have current_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_query_prefix_rounds
        [OF round_bound wf controlled])
  have query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_current_partial_opening_hit
          current_query_bound])
      (use wf controlled in simp_all)
  have transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift
      adversary_initial_state \<le>
      P + staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_relevant_partial_header_candidate_drift_bound_from_sampled_transcript
        [OF wf controlled data_pre_bound transcript_new_bound])
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_bad_with_partial_candidates)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (P + staged_concrete_transcript_target_error_bound)"
    by (rule
        checked_staged_security_with_data_state_partial_candidate_composition_bad_bound_from_relevant_drift_and_budgets
        [OF false_statement wf controlled drift_bound])
  have merkle_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
  have empty_query_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> empty_query_error"
    by (rule order_trans[
        OF checked_staged_security_with_data_state_empty_query_bad_le_current_empty_opening_hit_at_zero[
          OF wf controlled] current_empty_bound])
  have empty_header_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (P + staged_concrete_transcript_target_error_bound) +
      empty_trace_fri_error' + empty_query_error"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_bound_from_relevant_drift_trace_fri_and_query
        [OF false_statement wf controlled drift_bound empty_trace_fri_bound
          empty_query_bound])
  show ?thesis
    by (rule
        checked_staged_soundness_from_verifier_tied_aligned_transcript_partial_candidate_components_and_empty_header_bound
        [OF false_statement merkle_bound comp_bound trace_fri_bound
          comp_fri_bound query_bound empty_header_bound])
qed

end

text \<open>
  These single-query-charge wrappers are downstream plumbing for the public
  same-run route.  The visible theorem remains in
  \<open>Soundness_Public_Route_Same_Run\<close>.
\<close>

hide_fact
  soundness.stark_soundness_from_transcript_indexed_partial_opening_route_from_sampled_transcript_relevant_drift_only_single_query_charge_from_active_fri_bounds

end
