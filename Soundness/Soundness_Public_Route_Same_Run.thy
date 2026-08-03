(*  Title:      Stark/Soundness_Public_Route_Same_Run.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Public_Route_Same_Run
  imports
    Soundness_Public_Route_Active_Base
    Soundness_FRI_Sampled_Interface_Conflict_Zero
begin

text \<open>
  Public-route infrastructure for the staged soundness theorem.  This layer
  assembles the checked current-empty and transcript-empty reductions and
  states them in the plain locale \<^locale>\<open>soundness\<close>.  FRI losses are expressed
  as concrete staged verifier-event probabilities that are bounded in later FRI
  layers.
\<close>

context soundness
begin

lemma current_query_route_bound_from_active_fri_bounds_internal:
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error' + composition_fri_error' +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      empty_trace_fri_error' + 1)"
proof -
  let ?exact =
    "hash_collision_budget_value 0
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
  have route:
    "checked_staged_adversary_acceptance_probability A \<le> ?exact"
    by (rule
        stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_bounds
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          empty_trace_fri_bound])
  have exact_le_route:
    "?exact \<le>
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
        (1 + staged_concrete_transcript_target_error_bound)) +
        (\<Sum>i<rounds.
          1 +
          (1 + staged_concrete_transcript_target_error_bound) +
          (1 + staged_concrete_transcript_target_error_bound)) +
      trace_fri_error' + composition_fri_error' +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        (1 + staged_concrete_transcript_target_error_bound) +
        empty_trace_fri_error' + 1)"
    unfolding active_route_transcript_pre_error_for_def
      active_route_current_prefix_authenticated_error_for_def
      active_route_current_empty_query_error_for_def
    by (intro add_mono sum_mono order_refl wp_event_le_1)
  show ?thesis
    by (rule order_trans[OF route exact_le_route])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_staged_active_fri_bounds:
  fixes trace_bad ::
    "'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
    and composition_bad ::
      "'f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
    and trace_B :: "'f list set"
    and composition_B :: "'f \<Rightarrow> 'f list set"
    and trace_fresh trace_merkle trace_missing empty_fresh
      empty_assignment composition_fresh composition_merkle :: prob
    and trace_fri_error' composition_fri_error'
      empty_trace_fri_error' :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_finite: "finite trace_B"
    and trace_cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) trace_bad"
    and trace_envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets trace_bad trace_table \<subseteq> trace_B"
    and trace_fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s trace_B))
      adversary_initial_state \<le> trace_fresh"
    and trace_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_merkle"
    and trace_missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_missing"
    and trace_total:
    "(trace_fresh +
        hash_relation_budget_value (card trace_B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      ((trace_missing +
        ((((trace_merkle + trace_merkle) + (trace_merkle + 0) +
          (trace_merkle + 0) + (trace_merkle + 0 + 0)) +
          trace_merkle) + 0)) +
        (1 + trace_merkle)) +
      (trace_missing + trace_merkle)
      \<le> trace_fri_error'"
    and empty_fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s trace_B))
      adversary_initial_state \<le> empty_fresh"
    and empty_assignment_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_layer_assignment_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> empty_assignment"
    and empty_total:
    "(empty_fresh +
        hash_relation_budget_value (card trace_B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) + empty_assignment
      \<le> empty_trace_fri_error'"
    and composition_finite: "\<And>dg. finite (composition_B dg)"
    and composition_cover:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_sampled_layer_chain_cover
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) composition_bad"
    and composition_envelope:
    "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets composition_bad dg composition_table
        \<subseteq> composition_B dg"
    and composition_fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s composition_B))
      adversary_initial_state \<le> composition_fresh"
    and composition_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_merkle"
    and composition_total:
    "(composition_fresh +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (composition_B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (((composition_merkle + 0) +
        (composition_merkle + 0) + (composition_merkle + 0) +
        (composition_merkle + 0 + 0) + composition_merkle) + 0 + 0)
      \<le> composition_fri_error'"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error' + composition_fri_error' +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      empty_trace_fri_error' + 1)"
proof -
  have trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> trace_fri_error'"
  proof (rule order_trans)
    show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      ((trace_fresh +
        hash_relation_budget_value (card trace_B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      ((trace_missing +
        ((((trace_merkle + trace_merkle) + (trace_merkle + 0) +
          (trace_merkle + 0) + (trace_merkle + 0 + 0)) +
          trace_merkle) + 0)) +
        (1 + trace_merkle))) +
      (trace_missing + trace_merkle)"
      by (rule
          checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_augmented_route_and_unaugmented_split
          [OF wf controlled trace_finite trace_cover trace_envelope
            trace_fresh_bound trace_merkle_bound trace_missing_bound
            wp_event_le_1])
    show "... \<le> trace_fri_error'"
      by (rule trace_total)
  qed
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> empty_trace_fri_error'"
  proof (rule order_trans)
    show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      (empty_fresh +
        hash_relation_budget_value (card trace_B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) + empty_assignment"
      by (rule
          checked_staged_security_trace_fri_empty_header_bound_from_fresh_prequery_and_assignment_obstruction
          [OF wf controlled trace_finite trace_cover trace_envelope
            empty_fresh_bound empty_assignment_bound])
    show "... \<le> empty_trace_fri_error'"
      by (rule empty_total)
  qed
  have comp_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> composition_fri_error'"
  proof (rule order_trans)
    show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      (composition_fresh +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (composition_B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (((composition_merkle + 0) +
        (composition_merkle + 0) + (composition_merkle + 0) +
        (composition_merkle + 0 + 0) + composition_merkle) + 0 + 0)"
      by (rule
          checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_fresh_prequery_zero_slot_missing_selected_final_and_replay_gaps
          [OF wf controlled composition_finite composition_cover
            composition_envelope composition_fresh_bound composition_merkle_bound])
    show "... \<le> composition_fri_error'"
      by (rule composition_total)
  qed
  show ?thesis
    by (rule
        current_query_route_bound_from_active_fri_bounds_internal
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          empty_trace_fri_bound])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_residual_obligations:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and residuals:
      "active_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
        Rc Ac Pc Nc Sc Gc"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      trace_fri_error + 1)"
proof -
  have trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> trace_fri_error"
    by (rule active_fri_residual_obligations_staged_trace_bound[OF residuals])
  have comp_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> composition_fri_error"
    by (rule
        active_fri_residual_obligations_staged_composition_bound[OF residuals])
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule
        active_fri_residual_obligations_staged_empty_header_bound[OF residuals])
  show ?thesis
    by (rule
        current_query_route_bound_from_active_fri_bounds_internal
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          empty_trace_fri_bound])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_residual_components:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_residuals:
      "active_trace_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft"
    and composition_residuals:
      "active_composition_fri_residual_obligations_for A Rc Ac Pc Nc Sc Gc"
    and empty_trace: "active_empty_trace_fri_reduction_for A"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      trace_fri_error + 1)"
proof -
  have residuals:
    "active_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
      Rc Ac Pc Nc Sc Gc"
    by (rule active_fri_residual_obligations_from_components
        [OF trace_residuals composition_residuals empty_trace])
  show ?thesis
    by (rule
        stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_residual_obligations
        [OF false_statement wf controlled residuals])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_reductions:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and active_fri: "active_fri_reductions_for A"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      trace_fri_error + 1)"
proof -
  have trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> trace_fri_error"
    by (rule active_fri_reductions_staged_trace_bound[OF active_fri])
  have comp_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> composition_fri_error"
    by (rule active_fri_reductions_staged_composition_bound[OF active_fri])
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
    by (rule active_fri_reductions_staged_empty_header_bound[OF active_fri])
  show ?thesis
    by (rule
        current_query_route_bound_from_active_fri_bounds_internal
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          empty_trace_fri_bound])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_derived_active_fri_components:
  fixes TraceAug TraceMissing TraceMerkle CompSampled CompMerkle EmptySampled EmptyMissing ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_augmented_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_augmented_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceAug data attacker_state"
    and trace_missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      TraceMissing data attacker_state"
    and trace_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceMerkle data attacker_state"
    and trace_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      TraceAug data attacker_state +
        (TraceMissing data attacker_state + TraceMerkle data attacker_state)
      \<le> trace_fri_error"
    and composition_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_bad_with_verifier_tied_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      CompSampled data attacker_state"
    and composition_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> CompMerkle data attacker_state"
    and composition_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      CompSampled data attacker_state +
        (((CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0 + 0) +
          CompMerkle data attacker_state) + 0)
      \<le> composition_fri_error"
    and empty_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptySampled data attacker_state"
    and empty_missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_reachable_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyMissing data attacker_state"
    and empty_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      EmptySampled data attacker_state + EmptyMissing data attacker_state
      \<le> trace_fri_error"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      trace_fri_error + 1)"
proof -
  have active_fri: "active_fri_reductions_for A"
    by (rule
        active_fri_reductions_for_from_trace_augmented_composition_sampled_and_empty_sampled
        [OF trace_augmented_bound trace_missing_bound trace_merkle_bound
          trace_total composition_sampled_bound composition_merkle_bound
          composition_total empty_sampled_bound empty_missing_bound
          empty_total])
  show ?thesis
    by (rule
        stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_reductions
        [OF false_statement wf controlled active_fri])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_derived_active_fri_conflict_zero_components:
  fixes TraceAug TraceMissing TraceMerkle CompSampled CompMerkle EmptySampled EmptyConflict EmptyZero ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_augmented_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_augmented_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceAug data attacker_state"
    and trace_missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      TraceMissing data attacker_state"
    and trace_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceMerkle data attacker_state"
    and trace_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      TraceAug data attacker_state +
        (TraceMissing data attacker_state + TraceMerkle data attacker_state)
      \<le> trace_fri_error"
    and composition_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_bad_with_verifier_tied_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      CompSampled data attacker_state"
    and composition_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> CompMerkle data attacker_state"
    and composition_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      CompSampled data attacker_state +
        (((CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0 + 0) +
          CompMerkle data attacker_state) + 0)
      \<le> composition_fri_error"
    and empty_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptySampled data attacker_state"
    and empty_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyConflict data attacker_state"
    and empty_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyZero data attacker_state"
    and empty_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      EmptySampled data attacker_state +
        (EmptyConflict data attacker_state + EmptyZero data attacker_state)
      \<le> trace_fri_error"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      trace_fri_error + 1)"
proof -
  have active_fri: "active_fri_reductions_for A"
    by (rule
        active_fri_reductions_for_from_trace_augmented_composition_sampled_and_empty_conflict_zero
        [OF trace_augmented_bound trace_missing_bound trace_merkle_bound
          trace_total composition_sampled_bound composition_merkle_bound
          composition_total empty_sampled_bound empty_conflict_bound
          empty_zero_bound empty_total])
  show ?thesis
    by (rule
        stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_reductions
        [OF false_statement wf controlled active_fri])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_derived_active_fri_canonical_components:
  fixes TraceAug TraceMissing TraceMerkle CompCanonical CompMerkle EmptyCanonical EmptyConflict EmptyZero ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_augmented_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_augmented_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceAug data attacker_state"
    and trace_missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      TraceMissing data attacker_state"
    and trace_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceMerkle data attacker_state"
    and trace_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      TraceAug data attacker_state +
        (TraceMissing data attacker_state + TraceMerkle data attacker_state)
      \<le> trace_fri_error"
    and composition_canonical_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_bad_with_canonical_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      CompCanonical data attacker_state"
    and composition_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> CompMerkle data attacker_state"
    and composition_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      CompCanonical data attacker_state +
        (((CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0 + 0) +
          CompMerkle data attacker_state) + 0)
      \<le> composition_fri_error"
    and empty_canonical_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_canonical_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyCanonical data attacker_state"
    and empty_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyConflict data attacker_state"
    and empty_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyZero data attacker_state"
    and empty_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      EmptyCanonical data attacker_state +
        (EmptyConflict data attacker_state + EmptyZero data attacker_state)
      \<le> trace_fri_error"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      trace_fri_error + 1)"
proof -
  have active_fri: "active_fri_reductions_for A"
    by (rule
        active_fri_reductions_for_from_trace_augmented_composition_canonical_and_empty_conflict_zero
        [OF trace_augmented_bound trace_missing_bound trace_merkle_bound
          trace_total composition_canonical_bound composition_merkle_bound
          composition_total empty_canonical_bound empty_conflict_bound
          empty_zero_bound empty_total])
  show ?thesis
    by (rule
        stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_reductions
        [OF false_statement wf controlled active_fri])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_sampled_query_fri_components:
  fixes TraceAug TraceConflict TraceZero TraceMerkle CompSampled CompMerkle EmptySampled EmptyConflict EmptyZero ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_augmented_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_augmented_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceAug data attacker_state"
    and trace_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceConflict data attacker_state"
    and trace_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceZero data attacker_state"
    and trace_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceMerkle data attacker_state"
    and trace_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      TraceAug data attacker_state +
        ((TraceConflict data attacker_state + TraceZero data attacker_state) +
          TraceMerkle data attacker_state)
      \<le> trace_fri_error"
    and composition_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_query_bad_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      CompSampled data attacker_state"
    and composition_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> CompMerkle data attacker_state"
    and composition_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      CompSampled data attacker_state +
        (((CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0 + 0) +
          CompMerkle data attacker_state) + 0)
      \<le> composition_fri_error"
    and empty_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_query_bad_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptySampled data attacker_state"
    and empty_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyConflict data attacker_state"
    and empty_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyZero data attacker_state"
    and empty_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      EmptySampled data attacker_state +
        (EmptyConflict data attacker_state + EmptyZero data attacker_state)
      \<le> trace_fri_error"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      trace_fri_error + 1)"
proof -
  have active_fri: "active_fri_reductions_for A"
    by (rule
        active_fri_reductions_for_from_trace_augmented_conflict_zero_composition_sampled_query_and_empty_conflict_zero
        [OF trace_augmented_bound trace_conflict_bound trace_zero_bound
          trace_merkle_bound trace_total composition_sampled_bound composition_merkle_bound
          composition_total empty_sampled_bound empty_conflict_bound
          empty_zero_bound empty_total])
  show ?thesis
    by (rule
        stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_reductions
        [OF false_statement wf controlled active_fri])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_sampled_query_projection_fraction_components:
  fixes TraceAug TraceConflict TraceZero TraceMerkle CompSampled CompMerkle EmptySampled EmptyConflict EmptyZero ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_augmented_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_augmented_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceAug data attacker_state"
    and trace_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceConflict data attacker_state"
    and trace_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceZero data attacker_state"
    and trace_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> TraceMerkle data attacker_state"
    and trace_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      TraceAug data attacker_state +
        ((TraceConflict data attacker_state + TraceZero data attacker_state) +
          TraceMerkle data attacker_state)
      \<le> trace_fri_error"
    and composition_sampled_future:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_future_fresh
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
    and composition_sampled_generic:
    "\<And>data attacker_state dg.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      generic_fri_sampled_query_projection_fraction_bound
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg)
        (CompSampled data attacker_state)"
    and composition_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> CompMerkle data attacker_state"
    and composition_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      CompSampled data attacker_state +
        (((CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0) +
          (CompMerkle data attacker_state + 0 + 0) +
          CompMerkle data attacker_state) + 0)
      \<le> composition_fri_error"
    and empty_sampled_future:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_future_fresh
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
    and empty_sampled_generic:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      generic_fri_sampled_query_projection_fraction_bound
        trace_table_low_degree (Not \<circ> trace_table_low_degree)
        (clength - 1) (EmptySampled data attacker_state)"
    and empty_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyConflict data attacker_state"
    and empty_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyZero data attacker_state"
    and empty_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      EmptySampled data attacker_state +
        (EmptyConflict data attacker_state + EmptyZero data attacker_state)
      \<le> trace_fri_error"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      trace_fri_error + 1)"
  proof (rule
    stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_sampled_query_fri_components
    [OF false_statement wf controlled trace_augmented_bound
      trace_conflict_bound trace_zero_bound trace_merkle_bound trace_total _
      composition_merkle_bound composition_total _ empty_conflict_bound
      empty_zero_bound empty_total])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show
    "wp_event verify_monad (composition_fri_sampled_query_bad_candidate ?s)
      ?s \<le> CompSampled data attacker_state"
    by (rule
        wp_composition_fri_sampled_query_bad_candidate_bound_from_generic_projection_fraction
        [OF composition_sampled_future[OF support]])
      (rule composition_sampled_generic[OF support])
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate ?s)
      ?s \<le> EmptySampled data attacker_state"
    by (rule
        wp_trace_fri_sampled_query_bad_candidate_bound_from_generic_projection_fraction
        [OF empty_sampled_future[OF support]])
      (rule empty_sampled_generic[OF support])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_trace_active_and_staged_sampled_query_projection_components:
  fixes composition_B :: "'f \<Rightarrow> 'f list set"
    and composition_Q empty_Q :: "nat list set"
    and CompSampled CompMerkle EmptySampled EmptyConflict EmptyZero
      composition_fresh empty_fresh :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_partial_candidate)
        adversary_initial_state \<le> trace_fri_error"
    and composition_finite: "\<And>dg. finite (composition_B dg)"
    and composition_fresh_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_challenge_list_fresh_hit s composition_B))
        adversary_initial_state \<le> composition_fresh"
    and composition_projection:
      "\<And>dg. fst `
        ((composition_fri_sampled_query_bad_pair_union dg \<inter>
          (fri_query_index_list_space \<times> UNIV)) \<inter>
          (UNIV \<times> (- composition_B dg))) \<subseteq> composition_Q"
    and composition_sampled_total:
      "composition_fresh +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (composition_B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget) +
        staged_phase_target_error
          (query_index_raw_preimage
            (query_index_list_entries composition_Q))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)
      \<le> CompSampled"
    and composition_merkle_bound:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        wp_event verify_monad
          (partial_merkle_inconsistency_bad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) \<le> CompMerkle"
    and composition_total:
      "CompSampled +
        (((CompMerkle + 0) + (CompMerkle + 0) + (CompMerkle + 0) +
          (CompMerkle + 0 + 0) + CompMerkle) + 0 + 0)
      \<le> composition_fri_error"
    and empty_finite: "finite empty_B"
    and empty_fresh_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_challenge_list_fresh_hit s empty_B))
        adversary_initial_state \<le> empty_fresh"
    and empty_projection:
      "fst `
        ((trace_fri_sampled_query_bad_pair_union \<inter>
          (fri_query_index_list_space \<times> UNIV)) \<inter>
          (UNIV \<times> (- empty_B))) \<subseteq> empty_Q"
    and empty_sampled_total:
      "empty_fresh +
        hash_relation_budget_value (card empty_B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget) +
        staged_phase_target_error
          (query_index_raw_preimage (query_index_list_entries empty_Q))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)
      \<le> EmptySampled"
    and empty_conflict_bound:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        wp_event verify_monad
          (trace_fri_sampled_assignment_conflict
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) \<le> EmptyConflict"
    and empty_zero_bound:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist (execute (checked_staged_transcript_program A)
            adversary_initial_state) \<Longrightarrow>
        wp_event verify_monad
          (trace_fri_zero_round_final_obstruction
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) \<le> EmptyZero"
    and empty_total:
      "EmptySampled + (EmptyConflict + EmptyZero) \<le> trace_fri_error"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      trace_fri_error + 1)"
proof -
  have composition_sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> CompSampled"
    by (rule order_trans
        [OF checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_challenge_cover_and_query_projection
          [OF wf controlled composition_finite composition_fresh_bound
            composition_projection]
          composition_sampled_total])
  have comp_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> composition_fri_error"
  proof -
    have "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_verifier_tied_partial_candidate)
        adversary_initial_state \<le>
        CompSampled +
          (((CompMerkle + 0) + (CompMerkle + 0) + (CompMerkle + 0) +
            (CompMerkle + 0 + 0) + CompMerkle) + 0 + 0)"
      apply (rule
          checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_sampled_query_and_residual_gaps
          [OF composition_sampled])
      apply (rule wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
      apply (rule composition_merkle_bound)
      apply assumption
      apply (rule wp_composition_fri_verifier_tied_recorded_base_chunk_auth_missing_zero)
      apply (rule wp_composition_fri_verifier_tied_next_value_replay_gap_bound_from_merkle_and_slot)
      apply (rule composition_merkle_bound)
      apply assumption
      apply (rule wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
      apply (rule wp_composition_fri_verifier_tied_successor_replay_gap_bound_from_merkle_and_slot)
      apply (rule composition_merkle_bound)
      apply assumption
      apply (rule wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
      apply (rule wp_composition_fri_verifier_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
      apply (rule composition_merkle_bound)
      apply assumption
      apply (rule wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
      apply (rule wp_composition_fri_verifier_tied_final_value_selected_step_missing_gap_zero)
      apply (subst wp_composition_fri_verifier_tied_zero_round_final_obstruction_zero)
      apply simp
      done
    then show ?thesis
      by (rule order_trans[OF _ composition_total])
  qed
  have empty_sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> EmptySampled"
    by (rule order_trans
        [OF checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_challenge_cover_and_query_projection
          [OF wf controlled empty_finite empty_fresh_bound empty_projection]
          empty_sampled_total])
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
  proof -
    have "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> EmptySampled + (EmptyConflict + EmptyZero)"
      by (rule
          checked_staged_security_trace_fri_empty_header_bound_from_sampled_query_conflict_and_zero
          [OF empty_sampled empty_conflict_bound empty_zero_bound])
    then show ?thesis
      by (rule order_trans[OF _ empty_total])
  qed
  show ?thesis
    by (rule
        current_query_route_bound_from_active_fri_bounds_internal
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          empty_trace_fri_bound])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_full_cover_domain_conflict_zero_components:
  fixes trace_bad ::
    "'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
    and composition_bad ::
      "'f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
    and trace_B :: "'f list set"
    and composition_B :: "'f \<Rightarrow> 'f list set"
    and trace_fresh trace_proximity trace_index trace_domain_length
      trace_sampled_domain trace_conflict trace_zero
      composition_fresh composition_proximity composition_index
      composition_domain_length composition_sampled_domain
      composition_conflict composition_zero
      empty_conflict empty_zero :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_finite: "finite trace_B"
    and trace_envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets trace_bad trace_table \<subseteq> trace_B"
    and trace_fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s trace_B))
      adversary_initial_state \<le> trace_fresh"
    and trace_proximity_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) trace_bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_proximity"
    and trace_index_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_index"
    and trace_domain_length_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_domain_length"
    and trace_sampled_domain_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_sampled_domain"
    and trace_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_conflict"
    and trace_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_zero"
    and trace_total:
    "((trace_fresh +
        hash_relation_budget_value (card trace_B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
        (trace_proximity + trace_index +
          (trace_index + trace_domain_length) +
          (trace_index + trace_sampled_domain))) +
        (trace_conflict + trace_zero)
      \<le> trace_fri_error"
    and composition_finite: "\<And>dg. finite (composition_B dg)"
    and composition_envelope:
    "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets composition_bad dg composition_table
        \<subseteq> composition_B dg"
    and composition_fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s composition_B))
      adversary_initial_state \<le> composition_fresh"
    and composition_proximity_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) composition_bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_proximity"
    and composition_index_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_index"
    and composition_domain_length_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_domain_length"
    and composition_sampled_domain_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_sampled_domain"
    and composition_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_conflict"
    and composition_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_zero"
    and composition_total:
    "((composition_fresh +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (composition_B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
        (composition_proximity + composition_index +
          (composition_index + composition_domain_length) +
          (composition_index + composition_sampled_domain))) +
        (composition_conflict + composition_zero)
      \<le> composition_fri_error"
    and empty_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> empty_conflict"
    and empty_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> empty_zero"
    and empty_total:
    "((trace_fresh +
        hash_relation_budget_value (card trace_B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
        (trace_proximity + trace_index +
          (trace_index + trace_domain_length) +
          (trace_index + trace_sampled_domain))) +
        (empty_conflict + empty_zero)
      \<le> trace_fri_error"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      trace_fri_error + 1)"
proof -
  have trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> trace_fri_error"
  proof -
    have "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_partial_candidate)
        adversary_initial_state \<le>
        ((trace_fresh +
          hash_relation_budget_value (card trace_B * ceil_log clength)
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget)) +
          (trace_proximity + trace_index +
            (trace_index + trace_domain_length) +
            (trace_index + trace_sampled_domain))) +
          (trace_conflict + trace_zero)"
      by (rule
          checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_full_cover_domain_conflict_and_zero
          [where bad = trace_bad];
        (rule wf | rule controlled | rule trace_finite |
         rule trace_envelope | rule trace_fresh_bound |
         rule trace_proximity_bound | rule trace_index_bound |
         rule trace_domain_length_bound | rule trace_sampled_domain_bound |
         rule trace_conflict_bound | rule trace_zero_bound))
    then show ?thesis
      by (rule order_trans[OF _ trace_total])
  qed
  have comp_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> composition_fri_error"
  proof -
    have "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_verifier_tied_partial_candidate)
        adversary_initial_state \<le>
        ((composition_fresh +
          hash_relation_budget_value
            (\<Sum>dg \<in> (UNIV :: 'f set).
              card (composition_B dg) * ceil_log (maxDegree + 1))
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget)) +
          (composition_proximity + composition_index +
            (composition_index + composition_domain_length) +
            (composition_index + composition_sampled_domain))) +
          (composition_conflict + composition_zero)"
      by (rule
          checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_full_cover_domain_conflict_and_zero
          [where bad = composition_bad];
        (rule wf | rule controlled | rule composition_finite |
         rule composition_envelope | rule composition_fresh_bound |
         rule composition_proximity_bound | rule composition_index_bound |
         rule composition_domain_length_bound |
         rule composition_sampled_domain_bound |
         rule composition_conflict_bound | rule composition_zero_bound))
    then show ?thesis
      by (rule order_trans[OF _ composition_total])
  qed
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
  proof -
    have "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le>
        ((trace_fresh +
          hash_relation_budget_value (card trace_B * ceil_log clength)
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget)) +
          (trace_proximity + trace_index +
            (trace_index + trace_domain_length) +
            (trace_index + trace_sampled_domain))) +
          (empty_conflict + empty_zero)"
      by (rule
          checked_staged_security_trace_fri_empty_header_bound_from_full_cover_domain_conflict_and_zero
          [where bad = trace_bad];
        (rule wf | rule controlled | rule trace_finite |
         rule trace_envelope | rule trace_fresh_bound |
         rule trace_proximity_bound | rule trace_index_bound |
         rule trace_domain_length_bound | rule trace_sampled_domain_bound |
         rule empty_conflict_bound | rule empty_zero_bound))
    then show ?thesis
      by (rule order_trans[OF _ empty_total])
  qed
  show ?thesis
    by (rule
        current_query_route_bound_from_active_fri_bounds_internal
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          empty_trace_fri_bound])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_full_cover_domain_conflict_zero_standard_envelopes:
  fixes trace_bad ::
    "'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
    and composition_bad ::
      "'f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
    and trace_fresh trace_proximity trace_index trace_domain_length
      trace_sampled_domain trace_conflict trace_zero
      composition_fresh composition_proximity composition_index
      composition_domain_length composition_sampled_domain
      composition_conflict composition_zero
      empty_conflict empty_zero :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          trace_fri_challenge_list_fresh_hit s
            (fri_challenge_space (ceil_log clength))))
      adversary_initial_state \<le> trace_fresh"
    and trace_proximity_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) trace_bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_proximity"
    and trace_index_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_index"
    and trace_domain_length_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_domain_length"
    and trace_sampled_domain_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_sampled_domain"
    and trace_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_conflict"
    and trace_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_zero"
    and trace_total:
    "((trace_fresh +
        hash_relation_budget_value
          (card (fri_challenge_space (ceil_log clength)) * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
        (trace_proximity + trace_index +
          (trace_index + trace_domain_length) +
          (trace_index + trace_sampled_domain))) +
        (trace_conflict + trace_zero)
      \<le> trace_fri_error"
    and composition_fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          composition_fri_challenge_list_fresh_hit s
            (\<lambda>dg. fri_challenge_space (ceil_log (to_nat dg + 1)))))
      adversary_initial_state \<le> composition_fresh"
    and composition_proximity_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) composition_bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_proximity"
    and composition_index_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_index"
    and composition_domain_length_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_domain_length"
    and composition_sampled_domain_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_sampled_domain"
    and composition_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_conflict"
    and composition_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_zero"
    and composition_total:
    "((composition_fresh +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (fri_challenge_space (ceil_log (to_nat dg + 1))) *
              ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
        (composition_proximity + composition_index +
          (composition_index + composition_domain_length) +
          (composition_index + composition_sampled_domain))) +
        (composition_conflict + composition_zero)
      \<le> composition_fri_error"
    and empty_conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> empty_conflict"
    and empty_zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> empty_zero"
    and empty_total:
    "((trace_fresh +
        hash_relation_budget_value
          (card (fri_challenge_space (ceil_log clength)) * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
        (trace_proximity + trace_index +
          (trace_index + trace_domain_length) +
          (trace_index + trace_sampled_domain))) +
        (empty_conflict + empty_zero)
      \<le> trace_fri_error"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    trace_fri_error + composition_fri_error +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      trace_fri_error + 1)"
proof (rule
    stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_full_cover_domain_conflict_zero_components
    [where trace_B = "fri_challenge_space (ceil_log clength)"
      and composition_B =
        "\<lambda>dg. fri_challenge_space (ceil_log (to_nat dg + 1))"
      and trace_bad = trace_bad
      and composition_bad = composition_bad])
  show "\<not> exists_valid_trace"
    by (rule false_statement)
  show "staged_budget_wellformed budgets"
    by (rule wf)
  show "staged_adversary_controlled budgets A"
    by (rule controlled)
  show "finite (fri_challenge_space (ceil_log clength))"
    by simp
  show "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets trace_bad trace_table
      \<subseteq> fri_challenge_space (ceil_log clength)"
    by (rule trace_fri_multiround_bad_sets_subset)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          trace_fri_challenge_list_fresh_hit s
            (fri_challenge_space (ceil_log clength))))
      adversary_initial_state \<le> trace_fresh"
    by (rule trace_fresh_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) trace_bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_proximity"
    by (rule trace_proximity_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_index"
    by (rule trace_index_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_domain_length"
    by (rule trace_domain_length_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_sampled_domain"
    by (rule trace_sampled_domain_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_conflict"
    by (rule trace_conflict_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> trace_zero"
    by (rule trace_zero_bound)
  show "((trace_fresh +
      hash_relation_budget_value
        (card (fri_challenge_space (ceil_log clength)) * ceil_log clength)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)) +
      (trace_proximity + trace_index +
        (trace_index + trace_domain_length) +
        (trace_index + trace_sampled_domain))) +
      (trace_conflict + trace_zero)
      \<le> trace_fri_error"
    by (rule trace_total)
  show "\<And>dg. finite (fri_challenge_space (ceil_log (to_nat dg + 1)))"
    by simp
  show "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets composition_bad dg
        composition_table
      \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    by (rule composition_fri_multiround_bad_sets_subset)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          composition_fri_challenge_list_fresh_hit s
            (\<lambda>dg. fri_challenge_space (ceil_log (to_nat dg + 1)))))
      adversary_initial_state \<le> composition_fresh"
    by (rule composition_fresh_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) composition_bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_proximity"
    by (rule composition_proximity_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_index"
    by (rule composition_index_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_domain_length"
    by (rule composition_domain_length_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_sampled_domain"
    by (rule composition_sampled_domain_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_conflict"
    by (rule composition_conflict_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> composition_zero"
    by (rule composition_zero_bound)
  show "((composition_fresh +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (fri_challenge_space (ceil_log (to_nat dg + 1))) *
            ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)) +
      (composition_proximity + composition_index +
        (composition_index + composition_domain_length) +
        (composition_index + composition_sampled_domain))) +
      (composition_conflict + composition_zero)
      \<le> composition_fri_error"
    by (rule composition_total)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> empty_conflict"
    by (rule empty_conflict_bound)
  show "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> empty_zero"
    by (rule empty_zero_bound)
  show "((trace_fresh +
      hash_relation_budget_value
        (card (fri_challenge_space (ceil_log clength)) * ceil_log clength)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)) +
      (trace_proximity + trace_index +
        (trace_index + trace_domain_length) +
        (trace_index + trace_sampled_domain))) +
      (empty_conflict + empty_zero)
      \<le> trace_fri_error"
    by (rule empty_total)
qed

definition concrete_trace_fri_header_error_for
where
  "concrete_trace_fri_header_error_for A =
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state"

definition concrete_composition_fri_error_for
where
  "concrete_composition_fri_error_for A =
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state"

definition concrete_trace_fri_empty_error_for
where
  "concrete_trace_fri_empty_error_for A =
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state"

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    concrete_trace_fri_header_error_for A +
      concrete_composition_fri_error_for A +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      concrete_trace_fri_empty_error_for A + 1)"
proof -
  have trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> concrete_trace_fri_header_error_for A"
    by (simp add: concrete_trace_fri_header_error_for_def)
  have comp_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> concrete_composition_fri_error_for A"
    by (simp add: concrete_composition_fri_error_for_def)
  have empty_trace_fri_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> concrete_trace_fri_empty_error_for A"
    by (simp add: concrete_trace_fri_empty_error_for_def)
  show ?thesis
    by (rule
        current_query_route_bound_from_active_fri_bounds_internal
        [OF false_statement wf controlled trace_fri_bound comp_fri_bound
          empty_trace_fri_bound])
qed

theorem stark_soundness_same_run_endpoint:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
      (1 + staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        1 +
        (1 + staged_concrete_transcript_target_error_bound) +
        (1 + staged_concrete_transcript_target_error_bound)) +
    concrete_trace_fri_header_error_for A +
      concrete_composition_fri_error_for A +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      concrete_trace_fri_empty_error_for A + 1)"
  by (rule
      stark_soundness_from_current_public_prefix_current_query_relevant_drift_route
      [OF false_statement wf controlled])

end

hide_fact
  soundness.stark_soundness_same_run_endpoint
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_staged_active_fri_bounds
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_bounds
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_reductions
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_derived_active_fri_components
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_derived_active_fri_conflict_zero_components
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_derived_active_fri_canonical_components
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_sampled_query_fri_components
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_sampled_query_projection_fraction_components
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_trace_active_and_staged_sampled_query_projection_components
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_full_cover_domain_conflict_zero_components
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_full_cover_domain_conflict_zero_standard_envelopes
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_residual_obligations
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_residual_components

end
