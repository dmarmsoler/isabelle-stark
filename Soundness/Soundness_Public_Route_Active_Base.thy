(*  Title:      Stark/Soundness_Public_Route_Active_Base.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Public_Route_Active_Base
  imports
    Soundness_Public_Route_Single_Query
    Soundness_FRI_Query_Exact_Bounds
    Soundness_FRI_Query_Index_Staged_Bounds
begin

text \<open>
  Base active-FRI public-route endpoint.

  This theory is deliberately upstream of the downstream FRI route adapters.
  It exposes the common route theorem from staged active FRI event bounds,
  without importing the final same-run endpoint theory.  This avoids an import
  cycle when later route layers are consumed by the final public endpoint.
\<close>

context soundness
begin

definition active_route_transcript_pre_error_for
where
  "active_route_transcript_pre_error_for A =
    wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_pre_hit
      adversary_initial_state"

definition active_route_current_empty_query_error_for
where
  "active_route_current_empty_query_error_for A =
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
      adversary_initial_state"

definition active_route_current_prefix_authenticated_error_for
where
  "active_route_current_prefix_authenticated_error_for A i =
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i)
      adversary_initial_state"

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_bounds:
  fixes trace_fri_error' composition_fri_error'
    empty_trace_fri_error' :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        active_route_current_prefix_authenticated_error_for A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
    trace_fri_error' + composition_fri_error' +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound) +
      empty_trace_fri_error' + active_route_current_empty_query_error_for A)"
proof -
  have transcript_new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  have data_pre_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_pre_hit
      adversary_initial_state \<le> active_route_transcript_pre_error_for A"
    by (simp add: active_route_transcript_pre_error_for_def)
  have current_empty_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_empty_query_opening_hit_at 0)
      adversary_initial_state \<le> active_route_current_empty_query_error_for A"
    by (simp add: active_route_current_empty_query_error_for_def)
  have prefix_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
          i)
        adversary_initial_state \<le>
        active_route_current_prefix_authenticated_error_for A i"
    by (simp add: active_route_current_prefix_authenticated_error_for_def)
  have trace_path_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_trace_path_output_hit_at
          i)
        adversary_initial_state \<le>
      active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_current_trace_path_output_hit_at_bound_from_transcript
        [OF _ data_pre_bound transcript_new_bound])
  have composition_path_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_composition_path_output_hit_at
          i)
        adversary_initial_state \<le>
      active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_current_composition_path_output_hit_at_bound_from_transcript
        [OF _ data_pre_bound transcript_new_bound])
  define C :: "nat \<Rightarrow> prob" where
    "C =
      (\<lambda>i. active_route_current_prefix_authenticated_error_for A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound))"
  have round_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
          i)
        adversary_initial_state \<le> C i"
  proof -
    fix i
    assume i_bound: "i < rounds"
    show
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
          i)
        adversary_initial_state \<le> C i"
      unfolding C_def
      by (rule
          checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_prefix_and_structured_paths
          [OF wf controlled i_bound prefix_bound[OF i_bound]
            trace_path_bound[OF i_bound] composition_path_bound[OF i_bound]])
  qed
  have route:
    "checked_staged_adversary_acceptance_probability A \<le>
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
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
      trace_fri_error' + composition_fri_error' +
      (\<Sum>i<rounds. C i) +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        empty_trace_fri_error' +
        active_route_current_empty_query_error_for A)"
    by (rule
        stark_soundness_from_transcript_indexed_partial_opening_route_from_sampled_transcript_relevant_drift_only_single_query_charge_from_active_fri_bounds
        [OF false_statement wf controlled round_bound data_pre_bound
          current_empty_bound trace_fri_bound comp_fri_bound
          empty_trace_fri_bound])
  then show ?thesis
    unfolding C_def by (simp add: algebra_simps)
qed

end

end
