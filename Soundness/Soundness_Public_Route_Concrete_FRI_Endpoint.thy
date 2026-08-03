(*  Title:      Stark/Soundness_Public_Route_Concrete_FRI_Endpoint.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Public_Route_Concrete_FRI_Endpoint
  imports Soundness_Public_Route_Same_Run
begin

text \<open>
  Public-route endpoint with concrete FRI losses expanded one step below
  the top-level bad-event probabilities.

  This theory is retained as infrastructure for the current sharpened endpoint:
  downstream theories reuse the reachable verifier-event envelope definitions
  and one-step concrete FRI bounds.  The active public theorem is exported by
  \<^file>\<open>Soundness_FRI_Trace_Restricted_Query_Endpoint.thy\<close>.
\<close>

context soundness
begin

definition reachable_verifier_event_bound_for
where
  "reachable_verifier_event_bound_for A E =
    Max (insert 0
      ((\<lambda>out. case out of
          None \<Rightarrow> 0
        | Some y \<Rightarrow>
            let s =
              verifier_state_from_adversary (snd y)
                (staged_proof_transcript (fst y))
            in wp_event verify_monad (E s) s) `
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)))"

lemma reachable_verifier_event_bound_for_ge:
  assumes support:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  shows
    "wp_event verify_monad
      (E
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
    \<le> reachable_verifier_event_bound_for A E"
proof -
  let ?F =
    "(\<lambda>out. case out of
        None \<Rightarrow> 0
      | Some y \<Rightarrow>
          let s =
            verifier_state_from_adversary (snd y)
              (staged_proof_transcript (fst y))
          in wp_event verify_monad (E s) s)"
  let ?S =
    "insert 0
      (?F `
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state))"
  have finite_S: "finite ?S"
    by simp
  have mem: "?F (Some (data, attacker_state)) \<in> ?S"
    using support by blast
  have le: "?F (Some (data, attacker_state)) \<le> Max ?S"
    by (rule Max_ge[OF finite_S mem])
  have F_eq:
    "?F (Some (data, attacker_state)) =
      wp_event verify_monad
        (E
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
    by (simp add: Let_def)
  show ?thesis
    unfolding reachable_verifier_event_bound_for_def
    using le F_eq by simp
qed

definition trace_fri_full_challenge_bad
where
  "trace_fri_full_challenge_bad _ _ _ = UNIV"

definition composition_fri_full_challenge_bad
where
  "composition_fri_full_challenge_bad _ _ _ _ = UNIV"

definition concrete_trace_fri_full_cover_domain_error_for
where
  "concrete_trace_fri_full_cover_domain_error_for budgets A =
    ((wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s.
            trace_fri_challenge_list_fresh_hit s
              (fri_challenge_space (ceil_log clength))))
        adversary_initial_state +
      hash_relation_budget_value
        (card (fri_challenge_space (ceil_log clength)) * ceil_log clength)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)) +
      (reachable_verifier_event_bound_for A
        (\<lambda>s.
          trace_fri_sampled_full_cover_proximity_failure s
            trace_fri_full_challenge_bad) +
       reachable_verifier_event_bound_for A
        trace_fri_sampled_full_cover_index_failure +
       (reachable_verifier_event_bound_for A
          trace_fri_sampled_full_cover_index_failure +
        reachable_verifier_event_bound_for A
          trace_fri_sampled_full_cover_domain_length_failure) +
       (reachable_verifier_event_bound_for A
          trace_fri_sampled_full_cover_index_failure +
        reachable_verifier_event_bound_for A
          trace_fri_sampled_full_cover_sampled_domain_failure)))"

definition concrete_trace_fri_header_error_for'
where
  "concrete_trace_fri_header_error_for' budgets A =
    concrete_trace_fri_full_cover_domain_error_for budgets A +
      (reachable_verifier_event_bound_for A
        trace_fri_header_tied_sampled_assignment_conflict +
       reachable_verifier_event_bound_for A
        trace_fri_header_tied_zero_round_final_obstruction)"

definition concrete_trace_fri_empty_error_for'
where
  "concrete_trace_fri_empty_error_for' budgets A =
    concrete_trace_fri_full_cover_domain_error_for budgets A +
      (reachable_verifier_event_bound_for A
        trace_fri_sampled_assignment_conflict +
       reachable_verifier_event_bound_for A
        trace_fri_zero_round_final_obstruction)"

definition concrete_composition_fri_full_cover_domain_error_for
where
  "concrete_composition_fri_full_cover_domain_error_for budgets A =
    ((wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          (\<lambda>s.
            composition_fri_challenge_list_fresh_hit s
              (\<lambda>dg. fri_challenge_space (ceil_log (to_nat dg + 1)))))
        adversary_initial_state +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (fri_challenge_space (ceil_log (to_nat dg + 1))) *
            ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)) +
      (reachable_verifier_event_bound_for A
        (\<lambda>s.
          composition_fri_sampled_full_cover_proximity_failure s
            composition_fri_full_challenge_bad) +
       reachable_verifier_event_bound_for A
        composition_fri_sampled_full_cover_index_failure +
       (reachable_verifier_event_bound_for A
          composition_fri_sampled_full_cover_index_failure +
        reachable_verifier_event_bound_for A
          composition_fri_sampled_full_cover_domain_length_failure) +
       (reachable_verifier_event_bound_for A
          composition_fri_sampled_full_cover_index_failure +
        reachable_verifier_event_bound_for A
          composition_fri_sampled_full_cover_sampled_domain_failure)))"

definition concrete_composition_fri_error_for'
where
  "concrete_composition_fri_error_for' budgets A =
    concrete_composition_fri_full_cover_domain_error_for budgets A +
      (reachable_verifier_event_bound_for A
        composition_fri_verifier_tied_sampled_assignment_conflict +
       reachable_verifier_event_bound_for A
        composition_fri_verifier_tied_zero_round_final_obstruction)"

lemma concrete_trace_fri_header_error_for'_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> concrete_trace_fri_header_error_for' budgets A"
  unfolding concrete_trace_fri_header_error_for'_def
    concrete_trace_fri_full_cover_domain_error_for_def
  by (rule
      checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_full_cover_domain_conflict_and_zero
      [where bad = trace_fri_full_challenge_bad
        and B = "fri_challenge_space (ceil_log clength)",
       OF wf controlled])
    (auto intro!: reachable_verifier_event_bound_for_ge
      dest: trace_fri_multiround_bad_sets_subset[THEN subsetD])

lemma concrete_trace_fri_empty_error_for'_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> concrete_trace_fri_empty_error_for' budgets A"
  unfolding concrete_trace_fri_empty_error_for'_def
    concrete_trace_fri_full_cover_domain_error_for_def
  by (rule
      checked_staged_security_trace_fri_empty_header_bound_from_full_cover_domain_conflict_and_zero
      [where bad = trace_fri_full_challenge_bad
        and B = "fri_challenge_space (ceil_log clength)",
       OF wf controlled])
    (auto intro!: reachable_verifier_event_bound_for_ge
      dest: trace_fri_multiround_bad_sets_subset[THEN subsetD])

lemma concrete_composition_fri_error_for'_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> concrete_composition_fri_error_for' budgets A"
  unfolding concrete_composition_fri_error_for'_def
    concrete_composition_fri_full_cover_domain_error_for_def
  by (rule
      checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_full_cover_domain_conflict_and_zero
      [where bad = composition_fri_full_challenge_bad
        and B = "\<lambda>dg. fri_challenge_space (ceil_log (to_nat dg + 1))",
       OF wf controlled])
    (auto intro!: reachable_verifier_event_bound_for_ge
      dest: composition_fri_multiround_bad_sets_subset[THEN subsetD])

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
    concrete_trace_fri_header_error_for' budgets A +
      concrete_composition_fri_error_for' budgets A +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      concrete_trace_fri_empty_error_for' budgets A + 1)"
  by (rule
      current_query_route_bound_from_active_fri_bounds_internal
      [OF false_statement wf controlled
        concrete_trace_fri_header_error_for'_bound[OF wf controlled]
        concrete_composition_fri_error_for'_bound[OF wf controlled]
        concrete_trace_fri_empty_error_for'_bound[OF wf controlled]])

theorem stark_soundness_concrete_fri_endpoint:
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
    concrete_trace_fri_header_error_for' budgets A +
      concrete_composition_fri_error_for' budgets A +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (1 + staged_concrete_transcript_target_error_bound) +
      concrete_trace_fri_empty_error_for' budgets A + 1)"
  by (rule
      stark_soundness_from_current_public_prefix_current_query_relevant_drift_route
      [OF false_statement wf controlled])

end

hide_fact
  soundness.stark_soundness_concrete_fri_endpoint
  soundness.stark_soundness_from_current_public_prefix_current_query_relevant_drift_route

end
