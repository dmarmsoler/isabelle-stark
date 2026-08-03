(*  Title:      Stark/Soundness_FRI_Trace_Restricted_Query_Endpoint.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Trace_Restricted_Query_Endpoint
  imports Soundness_FRI_Trace_Empty_Sampled_Assignment_Split
begin

text \<open>
  Public entry point for the staged STARK soundness theorem.  The theorem in
  this theory combines the staged adversary experiment, Merkle authentication
  reductions, query bounds, composition randomization bounds, and the FRI
  query/challenge accounting into one explicit probability bound.

  The bound uses restricted trace and composition product-accounting terms and
  the proved zero-round trace empty-header estimates from the preceding FRI
  theories.
\<close>

context soundness
begin

definition trace_header_restricted_one_step_error_for
where
  "trace_header_restricted_one_step_error_for budgets A trace_bad =
    trace_restricted_sampled_query_error_for budgets A trace_bad +
      trace_fri_header_replay_conflict_zero_error_for budgets A"

definition concrete_trace_header_restricted_one_step_error_for
where
  "concrete_trace_header_restricted_one_step_error_for budgets A =
    trace_header_restricted_one_step_error_for budgets A
      (\<lambda>_. trace_one_step_split_bad)"

lemma trace_fri_header_tied_sampled_assignment_conflict_replay_bound:
  "wp_event (checked_staged_security_experiment_with_data_state A)
    (staged_security_with_data_state_verifier_event
      trace_fri_header_tied_sampled_assignment_conflict)
    adversary_initial_state
  \<le> trace_fri_header_replay_conflict_error_for A"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  let ?M =
    "reachable_verifier_event_bound_for A partial_merkle_inconsistency_bad"
  let ?H =
    "reachable_verifier_event_bound_for A
      trace_fri_header_tied_recorded_sibling_candidate_missing"
  have merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
      \<le> ?M"
    by (rule reachable_verifier_event_bound_for_ge[OF support])
  have recorded_missing_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_recorded_sibling_candidate_missing ?s) ?s
      \<le> ?H"
    by (rule reachable_verifier_event_bound_for_ge[OF support])
  have head_neq:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap ?s) ?s \<le> ?M"
    by (rule
        wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle)
      (rule merkle_bound)
  have head_mismatch:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_mismatch_gap ?s) ?s
      \<le> ?M"
    by (rule
        wp_trace_fri_header_tied_base_head_value_mismatch_gap_bound_from_neq_gap
        [OF head_neq])
  have alignment:
    "wp_event verify_monad
      (trace_fri_header_tied_base_value_alignment_gap ?s) ?s \<le> ?M"
    by (rule
        wp_trace_fri_header_tied_base_value_alignment_gap_bound_from_head_value_mismatch_gap
        [OF head_mismatch])
  have next_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap ?s) ?s \<le> ?M + 0"
    by (rule
        wp_trace_fri_header_tied_next_value_replay_gap_bound_from_merkle_and_slot)
      (rule merkle_bound,
       rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
  have successor:
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap ?s) ?s \<le> ?M + 0"
    by (rule
        wp_trace_fri_header_tied_successor_replay_gap_bound_from_merkle_and_slot)
      (rule merkle_bound,
       rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
  have final:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_replay_gap ?s) ?s \<le> ?M + 0 + 0"
    by (rule
        wp_trace_fri_header_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
      (rule merkle_bound,
       rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero,
       rule wp_trace_fri_header_tied_final_value_selected_step_missing_gap_zero)
  have slot:
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap ?s) ?s
      \<le> 0"
    by (rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero)
  have authenticated_recorded_auth:
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap ?s)
      ?s \<le> 0"
    by (rule
        wp_trace_fri_header_tied_same_layer_authenticated_recorded_auth_gap_bound_from_slot_recorded_chunk_gap
        [OF slot])
  have recorded_auth:
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_recorded_auth_gap ?s) ?s \<le> 0"
    by (rule
        wp_trace_fri_header_tied_same_layer_recorded_auth_gap_bound_from_authenticated_recorded_auth_gap
        [OF authenticated_recorded_auth])
  have same_auth:
    "wp_event verify_monad
      (trace_fri_header_tied_same_layer_auth_gap ?s) ?s \<le> 0"
    by (rule
        wp_trace_fri_header_tied_same_layer_auth_gap_bound_from_recorded_auth_gap
        [OF recorded_auth])
  have auth_gap:
    "wp_event verify_monad
      (trace_fri_header_tied_assignment_auth_gap ?s) ?s \<le> 0"
    by (rule
        wp_trace_fri_header_tied_assignment_auth_gap_bound_from_same_layer_auth_gap
        [OF same_auth])
  have complement:
    "wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_sampled_assignment_conflict ?s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing ?s out)
      ?s \<le>
      ((((?M + ?M) + (?M + 0) + (?M + 0) + (?M + 0 + 0)) + ?M) + 0)"
    by (rule
        wp_trace_fri_header_tied_sampled_assignment_conflict_without_recorded_missing_bound_from_auth_gap_and_replay_gaps)
      (rule auth_gap, rule merkle_bound, rule alignment,
       rule next_bound, rule successor, rule final)
  show "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict ?s) ?s
    \<le> trace_fri_header_replay_conflict_error_for A"
    unfolding trace_fri_header_replay_conflict_error_for_def Let_def
    by (rule
        wp_trace_fri_header_tied_sampled_assignment_conflict_bound_from_recorded_missing_and_complement)
      (rule recorded_missing_bound, rule complement)
next
  fix s
  show "\<not> trace_fri_header_tied_sampled_assignment_conflict s None"
    unfolding trace_fri_header_tied_sampled_assignment_conflict_def
      accepted_fri_opening_transcript_def
    by simp
qed

lemma trace_fri_header_tied_zero_round_final_obstruction_agreement_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state
    \<le> trace_fri_zero_round_agreement_set_target_error_for budgets +
      trace_fri_controlled_merkle_error_for budgets"
proof -
  have checked:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_checked_final_obstruction)
      adversary_initial_state
    \<le> trace_fri_zero_round_agreement_set_target_error_for budgets"
    by (rule
        checked_staged_security_trace_fri_zero_round_checked_final_obstruction_bound_from_agreement_sets
        [OF wf controlled])
  have merkle:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state
    \<le> trace_fri_controlled_merkle_error_for budgets"
    unfolding trace_fri_controlled_merkle_error_for_def
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
  have split:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state
    \<le> wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_with_data_state_verifier_event
          trace_fri_zero_round_checked_final_obstruction out \<or>
        staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad out)
      adversary_initial_state"
    unfolding staged_security_with_data_state_verifier_event_def
    by (rule wp_event_mono_on_support)
      (auto dest:
        trace_fri_header_tied_zero_round_final_obstruction_imp_checked_or_merkle
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_zero_round_checked_final_obstruction)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets +
      trace_fri_controlled_merkle_error_for budgets"
    by (rule add_mono[OF checked merkle])
  finally show ?thesis .
qed

lemma trace_header_restricted_one_step_error_for_bound:
  fixes trace_bad :: "'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state
    \<le> trace_header_restricted_one_step_error_for budgets A trace_bad"
proof -
  have sampled_query:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> trace_restricted_sampled_query_error_for budgets A trace_bad"
    by (rule trace_restricted_sampled_query_error_for_bound[OF wf controlled])
  have sampled_plain:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state
    \<le> trace_restricted_sampled_query_error_for budgets A trace_bad"
    by (rule
        checked_staged_security_trace_fri_sampled_layer_chain_bound_from_sampled_query
        [OF sampled_query])
  have sampled_header:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state
    \<le> trace_restricted_sampled_query_error_for budgets A trace_bad"
  proof (rule order_trans[OF _ sampled_plain])
    show "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_header_tied_sampled_layer_chain)
        adversary_initial_state
      \<le> wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_sampled_layer_chain)
        adversary_initial_state"
      by (rule wp_event_mono)
        (auto simp: staged_security_with_data_state_verifier_event_def
          dest: trace_fri_header_tied_sampled_layer_chain_imp_sampled_layer_chain
          split: option.splits prod.splits)
  qed
  have conflict_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_sampled_assignment_conflict)
      adversary_initial_state
    \<le> trace_fri_header_replay_conflict_error_for A"
    by (rule trace_fri_header_tied_sampled_assignment_conflict_replay_bound)
  have zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state
    \<le> trace_fri_zero_round_agreement_set_target_error_for budgets +
      trace_fri_controlled_merkle_error_for budgets"
    by (rule
        trace_fri_header_tied_zero_round_final_obstruction_agreement_bound
        [OF wf controlled])
  have branch:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state
      \<le> trace_restricted_sampled_query_error_for budgets A trace_bad +
        (trace_fri_header_replay_conflict_error_for A +
         (trace_fri_zero_round_agreement_set_target_error_for budgets +
          trace_fri_controlled_merkle_error_for budgets))"
    by (rule
        checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_sampled_conflict_and_staged_zero
        [OF sampled_header conflict_bound zero_bound])
  show ?thesis
    using branch
    by (simp add: trace_header_restricted_one_step_error_for_def
      trace_fri_header_replay_conflict_zero_error_for_def)
qed

definition trace_empty_header_restricted_openings_zero_error_for
where
  "trace_empty_header_restricted_openings_zero_error_for budgets A empty_bad =
    (trace_fri_zero_round_agreement_set_target_error_for budgets +
     trace_fri_controlled_merkle_error_for budgets +
     (trace_header_restricted_one_step_error_for budgets A (\<lambda>_. empty_bad) +
      reachable_verifier_event_bound_for A
        trace_fri_header_tied_low_candidate_untied_openings_gap) +
     trace_header_restricted_one_step_error_for budgets A (\<lambda>_. empty_bad))"

definition trace_empty_header_restricted_nonnormalized_zero_error_for
where
  "trace_empty_header_restricted_nonnormalized_zero_error_for budgets A empty_bad =
    (trace_fri_zero_round_agreement_set_target_error_for budgets +
     trace_fri_controlled_merkle_error_for budgets +
     (trace_fri_controlled_merkle_error_for budgets +
      ((reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_nonconsumed_query_gap +
        reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_nonconsumed_irrelevant_root_gap) +
       reachable_verifier_event_bound_for A
          trace_fri_header_tied_low_candidate_nonconsumed_query_gap)) +
     trace_header_restricted_one_step_error_for budgets A (\<lambda>_. empty_bad))"

definition trace_empty_header_restricted_sampled_split_one_step_error_for
where
  "trace_empty_header_restricted_sampled_split_one_step_error_for budgets A empty_bad =
    trace_restricted_sampled_query_error_for budgets A (\<lambda>_. empty_bad) +
      (trace_fri_empty_sampled_assignment_structural_error_for budgets A +
       min (trace_empty_header_restricted_openings_zero_error_for budgets A empty_bad)
         (trace_empty_header_restricted_nonnormalized_zero_error_for budgets A empty_bad))"

definition concrete_trace_empty_header_restricted_sampled_split_one_step_error_for
where
  "concrete_trace_empty_header_restricted_sampled_split_one_step_error_for budgets A =
    trace_empty_header_restricted_sampled_split_one_step_error_for budgets A
      trace_one_step_split_bad"

lemma trace_empty_header_restricted_sampled_split_one_step_error_for_bound:
  fixes empty_bad :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state
    \<le> trace_empty_header_restricted_sampled_split_one_step_error_for
        budgets A empty_bad"
proof -
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> trace_restricted_sampled_query_error_for budgets A (\<lambda>_. empty_bad)"
    by (rule trace_restricted_sampled_query_error_for_bound[OF wf controlled])
  have conflict_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_assignment_conflict)
      adversary_initial_state
    \<le> trace_fri_empty_sampled_assignment_structural_error_for budgets A"
    by (rule
        checked_staged_security_trace_fri_sampled_assignment_conflict_bound_structural
        [OF wf controlled])
  have header_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state
    \<le> trace_header_restricted_one_step_error_for budgets A (\<lambda>_. empty_bad)"
    by (rule trace_header_restricted_one_step_error_for_bound
        [OF wf controlled])
  have zero_openings_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state
    \<le> trace_empty_header_restricted_openings_zero_error_for budgets A empty_bad"
    unfolding trace_empty_header_restricted_openings_zero_error_for_def
    by (rule
        checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_agreement_sets_header_and_openings
        [OF wf controlled header_bound])
  have zero_nonnormalized_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state
    \<le> trace_empty_header_restricted_nonnormalized_zero_error_for budgets A empty_bad"
    unfolding trace_empty_header_restricted_nonnormalized_zero_error_for_def
    by (rule
        checked_staged_security_trace_fri_zero_round_final_obstruction_bound_from_agreement_sets_header_and_nonnormalized
        [OF wf controlled header_bound])
  have zero_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_final_obstruction)
      adversary_initial_state
    \<le> min (trace_empty_header_restricted_openings_zero_error_for budgets A empty_bad)
        (trace_empty_header_restricted_nonnormalized_zero_error_for budgets A empty_bad)"
    using zero_openings_bound zero_nonnormalized_bound by simp
  have branch:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state
      \<le> trace_restricted_sampled_query_error_for budgets A (\<lambda>_. empty_bad) +
        (trace_fri_empty_sampled_assignment_structural_error_for budgets A +
         min (trace_empty_header_restricted_openings_zero_error_for budgets A empty_bad)
          (trace_empty_header_restricted_nonnormalized_zero_error_for budgets A empty_bad))"
    by (rule
        checked_staged_security_trace_fri_empty_header_bound_from_staged_sampled_conflict_and_zero
        [OF sampled conflict_bound zero_bound])
  show ?thesis
    using branch
    by (simp add:
        trace_empty_header_restricted_sampled_split_one_step_error_for_def)
qed

definition composition_no_full_cover_sampled_query_error_for
where
  "composition_no_full_cover_sampled_query_error_for budgets bad =
    (\<Sum>dg \<in> UNIV.
      \<Sum>challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
        (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
          (nnreal
            (card
              (composition_fri_sampled_query_no_full_cover_failure_query_fiber
                bad dg challenges)) *
            (1 / nnreal (card query_sample_space)) ^ rounds)) +
    hash_relation_budget_value
      (query_index_raw_list_relation_fiber_bound
        (\<Union>dg \<in> UNIV.
          \<Union>challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
            composition_fri_sampled_query_no_full_cover_failure_query_fiber
              bad dg challenges))
      (staged_attacker_query_budget budgets + staged_challenge_query_budget) +
    hash_relation_budget_value
      (\<Sum>dg \<in> (UNIV :: 'f set).
        card (fri_challenge_space (ceil_log (to_nat dg + 1))) *
          ceil_log (maxDegree + 1))
      (staged_attacker_query_budget budgets + staged_challenge_query_budget)"

definition composition_canonical_full_cover_shape_failure_error_for
where
  "composition_canonical_full_cover_shape_failure_error_for A bad =
    reachable_verifier_event_bound_for A
      (\<lambda>s. composition_fri_sampled_full_cover_proximity_failure s bad) +
    reachable_verifier_event_bound_for A
      composition_fri_sampled_full_cover_index_failure +
    reachable_verifier_event_bound_for A
      composition_fri_sampled_full_cover_shape_failure"

definition composition_restricted_sampled_query_error_for
where
  "composition_restricted_sampled_query_error_for budgets A bad =
    composition_no_full_cover_sampled_query_error_for budgets bad +
    composition_canonical_full_cover_shape_failure_error_for A bad"

lemma composition_restricted_sampled_query_error_for_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> composition_restricted_sampled_query_error_for budgets A bad"
proof -
  have no_full:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          composition_fri_sampled_query_no_full_cover_failure_candidate s
            bad))
      adversary_initial_state
    \<le> composition_no_full_cover_sampled_query_error_for budgets bad"
    unfolding composition_no_full_cover_sampled_query_error_for_def
    by (rule
        checked_staged_security_composition_fri_sampled_query_no_full_cover_failure_candidate_bound_from_restricted_pairs
        [OF wf controlled])
  have failure:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_canonical_full_cover_failure s bad))
      adversary_initial_state
    \<le> composition_canonical_full_cover_shape_failure_error_for A bad"
    unfolding composition_canonical_full_cover_shape_failure_error_for_def
  proof (rule
      checked_staged_security_composition_fri_sampled_canonical_full_cover_failure_bound_from_shape_subcases)
    fix data attacker_state
    assume support:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        (\<lambda>s. composition_fri_sampled_full_cover_proximity_failure s bad)"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  next
    fix data attacker_state
    assume support:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        composition_fri_sampled_full_cover_index_failure"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  next
    fix data attacker_state
    assume support:
      "Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    show "wp_event verify_monad
        (composition_fri_sampled_full_cover_shape_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
      \<le> reachable_verifier_event_bound_for A
        composition_fri_sampled_full_cover_shape_failure"
      by (rule reachable_verifier_event_bound_for_ge[OF support])
  qed
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> composition_no_full_cover_sampled_query_error_for budgets bad +
      composition_canonical_full_cover_shape_failure_error_for A bad"
    by (rule
        checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_no_full_cover_or_canonical_failure
        [OF no_full failure])
  show ?thesis
    using sampled
    by (simp add: composition_restricted_sampled_query_error_for_def)
qed

definition composition_restricted_verifier_tied_controlled_error_for
where
  "composition_restricted_verifier_tied_controlled_error_for budgets A comp_bad =
    composition_restricted_sampled_query_error_for budgets A comp_bad +
      (((composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0 + 0) +
        composition_one_step_controlled_merkle_error_for budgets) + 0 + 0)"

definition concrete_composition_restricted_one_step_error_for
where
  "concrete_composition_restricted_one_step_error_for budgets A =
    composition_restricted_verifier_tied_controlled_error_for budgets A
      (\<lambda>dg _. composition_one_step_split_bad dg)"

lemma composition_restricted_verifier_tied_controlled_error_for_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state
    \<le> composition_restricted_verifier_tied_controlled_error_for budgets A
        comp_bad"
proof -
  have sampled_query:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state
    \<le> composition_restricted_sampled_query_error_for budgets A comp_bad"
    by (rule composition_restricted_sampled_query_error_for_bound
        [OF wf controlled])
  have sampled:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state
    \<le> composition_restricted_sampled_query_error_for budgets A comp_bad"
    by (rule
        checked_staged_security_composition_fri_verifier_tied_sampled_layer_chain_bound_from_sampled_query
        [OF sampled_query])
  have conflict:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_sampled_assignment_conflict)
      adversary_initial_state \<le>
      (((composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0) +
        (composition_one_step_controlled_merkle_error_for budgets + 0 + 0) +
        composition_one_step_controlled_merkle_error_for budgets) + 0)"
    by (rule
        checked_staged_security_composition_fri_verifier_tied_sampled_assignment_conflict_bound_by_controlled_merkle
        [OF wf controlled])
  have zero:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_verifier_tied_zero_round_final_obstruction)
      adversary_initial_state \<le> (0::prob)"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (simp_all add:
        composition_fri_verifier_tied_zero_round_final_obstruction_false
        wp_composition_fri_verifier_tied_zero_round_final_obstruction_zero)
  have branch:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      composition_restricted_sampled_query_error_for budgets A comp_bad +
        ((((composition_one_step_controlled_merkle_error_for budgets + 0) +
          (composition_one_step_controlled_merkle_error_for budgets + 0) +
          (composition_one_step_controlled_merkle_error_for budgets + 0) +
          (composition_one_step_controlled_merkle_error_for budgets + 0 + 0) +
          composition_one_step_controlled_merkle_error_for budgets) + 0) + 0)"
    by (rule
        checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_staged_sampled_conflict_and_zero
        [OF sampled conflict zero])
  show ?thesis
    using branch
    by (simp add:
        composition_restricted_verifier_tied_controlled_error_for_def)
qed

definition active_route_current_prefix_conceptual_prefix_collision_hit_at
where
  "active_route_current_prefix_conceptual_prefix_collision_hit_at i out
    \<longleftrightarrow>
    checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
      i out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        hash_map_output_collision prefix_state)"

definition active_route_current_prefix_conceptual_algebraic_residual_hit_at
where
  "active_route_current_prefix_conceptual_algebraic_residual_hit_at i out
    \<longleftrightarrow>
    checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
      i out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        \<not> trace_table_low_degree
          (query_prefix_trace_conceptual_table prefix prefix_state) \<or>
        \<not> composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table prefix prefix_state) \<or>
        all_queries_consistent
          (query_prefix_trace_conceptual_table prefix prefix_state)
          (query_prefix_composition_conceptual_table prefix prefix_state)
          (sqp_alphas prefix))"

definition active_route_current_prefix_conceptual_algebraic_residual_error_for
where
  "active_route_current_prefix_conceptual_algebraic_residual_error_for A i =
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (active_route_current_prefix_conceptual_algebraic_residual_hit_at i)
      adversary_initial_state"

definition active_route_current_prefix_conceptual_trace_low_degree_bad_at
where
  "active_route_current_prefix_conceptual_trace_low_degree_bad_at i out
    \<longleftrightarrow>
    active_route_current_prefix_conceptual_algebraic_residual_hit_at i out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        \<not> trace_table_low_degree
          (query_prefix_trace_conceptual_table prefix prefix_state))"

definition active_route_current_prefix_conceptual_composition_low_degree_bad_at
where
  "active_route_current_prefix_conceptual_composition_low_degree_bad_at i out
    \<longleftrightarrow>
    active_route_current_prefix_conceptual_algebraic_residual_hit_at i out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        \<not> composition_table_low_degree maxDegree
          (query_prefix_composition_conceptual_table prefix prefix_state))"

definition active_route_current_prefix_conceptual_alpha_bad_set_hit_at
where
  "active_route_current_prefix_conceptual_alpha_bad_set_hit_at i out
    \<longleftrightarrow>
    active_route_current_prefix_conceptual_algebraic_residual_hit_at i out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        sqp_alphas prefix \<in>
          composition_trace_bad_alpha_space
            (query_prefix_trace_conceptual_table prefix prefix_state))"

definition active_route_current_prefix_conceptual_trace_low_degree_error_for
where
  "active_route_current_prefix_conceptual_trace_low_degree_error_for A i =
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (active_route_current_prefix_conceptual_trace_low_degree_bad_at i)
      adversary_initial_state"

definition active_route_current_prefix_conceptual_composition_low_degree_error_for
where
  "active_route_current_prefix_conceptual_composition_low_degree_error_for A i =
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (active_route_current_prefix_conceptual_composition_low_degree_bad_at i)
      adversary_initial_state"

definition active_route_current_prefix_conceptual_alpha_bad_set_error_for
where
  "active_route_current_prefix_conceptual_alpha_bad_set_error_for A i =
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (active_route_current_prefix_conceptual_alpha_bad_set_hit_at i)
      adversary_initial_state"

lemma active_route_current_prefix_conceptual_alpha_bad_set_hit_at_imp_data_state_alpha_prefix_bad_set_hit_on_support:
  assumes support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and candidate:
      "\<And>alpha_prefix alpha_prefix_state.
        alpha_prefix =
          (sqp_trace_root prefix, sqp_trace_fri_roots prefix,
            sqp_trace_fri_challenges prefix, sqp_trace_final prefix) \<Longrightarrow>
        Some (alpha_prefix, alpha_prefix_state) \<in>
          set_dist
            (execute (staged_alpha_prefix_program A)
              adversary_initial_state) \<Longrightarrow>
        query_prefix_trace_conceptual_table prefix prefix_state \<in>
          alpha_prefix_trace_table_candidates alpha_prefix_state
            (sqp_trace_root prefix)"
    and hit:
      "active_route_current_prefix_conceptual_alpha_bad_set_hit_at i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
      composition_trace_bad_alpha_space
      (Some (((data, attacker_state), result), final_state))"
proof -
  obtain alpha_prefix alpha_prefix_state where alpha_prefix_eq:
      "alpha_prefix =
        (sqp_trace_root prefix, sqp_trace_fri_roots prefix,
          sqp_trace_fri_challenges prefix, sqp_trace_final prefix)"
    and alpha_support:
      "Some (alpha_prefix, alpha_prefix_state) \<in>
        set_dist
          (execute (staged_alpha_prefix_program A) adversary_initial_state)"
    by (rule checked_staged_security_with_query_prefix_data_state_alpha_prefix_support
        [OF support])
  have table_candidate:
    "query_prefix_trace_conceptual_table prefix prefix_state \<in>
      alpha_prefix_trace_table_candidates alpha_prefix_state
        (sqp_trace_root prefix)"
    by (rule candidate[OF alpha_prefix_eq alpha_support])
  have alphas_eq: "staged_alphas data = sqp_alphas prefix"
    by (rule checked_staged_security_with_query_prefix_data_state_alphas_eq
        [OF support])
  have alpha_bad:
    "sqp_alphas prefix \<in>
      composition_trace_bad_alpha_space
        (query_prefix_trace_conceptual_table prefix prefix_state)"
    using hit
    unfolding active_route_current_prefix_conceptual_alpha_bad_set_hit_at_def
    by simp
  have staged_alpha_bad:
    "staged_alphas data \<in>
      composition_trace_bad_alpha_space
        (query_prefix_trace_conceptual_table prefix prefix_state)"
    using alpha_bad alphas_eq by simp
  have staged_alpha_in_space: "staged_alphas data \<in> alpha_space"
    using staged_alpha_bad composition_trace_bad_alpha_space_subset_alpha_space
    by blast
  have union_hit:
    "staged_alphas data \<in>
      alpha_prefix_union_bad_sets alpha_prefix_state
        composition_trace_bad_alpha_space (staged_trace_root data)"
  proof -
    have root_eq: "staged_trace_root data = sqp_trace_root prefix"
      using support
      unfolding
        checked_staged_security_experiment_with_query_prefix_data_state_def
        checked_staged_after_query_prefix_receive_with_verifier_def
        checked_staged_after_query_prefix_receive_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    have table_candidate':
      "query_prefix_trace_conceptual_table prefix prefix_state \<in>
        alpha_prefix_trace_table_candidates alpha_prefix_state
          (staged_trace_root data)"
      using table_candidate root_eq by simp
    show ?thesis
      unfolding alpha_prefix_union_bad_sets_def
      using table_candidate' staged_alpha_bad staged_alpha_in_space
      by auto
  qed
  have prefix_components:
    "staged_trace_root data = fst alpha_prefix \<and>
     staged_trace_fri_roots data = fst (snd alpha_prefix) \<and>
     staged_trace_fri_challenges data = fst (snd (snd alpha_prefix)) \<and>
     staged_trace_final data = snd (snd (snd alpha_prefix))"
    using support alpha_prefix_eq
    unfolding
      checked_staged_security_experiment_with_query_prefix_data_state_def
      checked_staged_after_query_prefix_receive_with_verifier_def
      checked_staged_after_query_prefix_receive_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  show ?thesis
    unfolding checked_staged_security_with_data_state_alpha_prefix_bad_set_hit_def
    using alpha_support prefix_components union_hit
    by auto
qed

lemma active_route_current_prefix_conceptual_alpha_bad_set_error_for_bound_from_data_state_alpha_prefix:
  assumes i_bound: "i < rounds"
    and candidate:
      "\<And>prefix prefix_state raw raw_state data attacker_state result
          final_state alpha_prefix alpha_prefix_state.
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state A i)
              adversary_initial_state) \<Longrightarrow>
        alpha_prefix =
          (sqp_trace_root prefix, sqp_trace_fri_roots prefix,
            sqp_trace_fri_challenges prefix, sqp_trace_final prefix) \<Longrightarrow>
        Some (alpha_prefix, alpha_prefix_state) \<in>
          set_dist
            (execute (staged_alpha_prefix_program A)
              adversary_initial_state) \<Longrightarrow>
        query_prefix_trace_conceptual_table prefix prefix_state \<in>
          alpha_prefix_trace_table_candidates alpha_prefix_state
            (sqp_trace_root prefix)"
    and data_state_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> C"
  shows
    "active_route_current_prefix_conceptual_alpha_bad_set_error_for A i \<le> C"
proof -
  let ?Data =
    "checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
      composition_trace_bad_alpha_space"
  let ?Projected =
    "\<lambda>out. case out of
      None \<Rightarrow> ?Data None
    | Some (packed, t) \<Rightarrow> ?Data (Some (snd packed, t))"
  let ?E = "active_route_current_prefix_conceptual_alpha_bad_set_hit_at i"
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      ?E adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      ?Projected adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
      and hit: "?E out"
    show "?Projected out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding active_route_current_prefix_conceptual_alpha_bad_set_hit_at_def
      by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
        "out =
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      have support':
        "Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state A i)
              adversary_initial_state)"
        using support unfolding out_eq .
      have hit':
        "active_route_current_prefix_conceptual_alpha_bad_set_hit_at i
          (Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state))"
        using hit unfolding out_eq .
      have data_hit:
        "?Data (Some (((data, attacker_state), result), final_state))"
        by (rule
            active_route_current_prefix_conceptual_alpha_bad_set_hit_at_imp_data_state_alpha_prefix_bad_set_hit_on_support
            [OF support' _ hit'])
          (rule candidate[OF support'])
      show ?thesis
        unfolding out_eq using data_hit by simp
    qed
  qed
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      ?Projected adversary_initial_state =
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?Data adversary_initial_state"
    using checked_staged_security_experiment_with_query_prefix_data_state_projection_event
      [OF i_bound, of A ?Data]
    by simp
  show ?thesis
    unfolding active_route_current_prefix_conceptual_alpha_bad_set_error_for_def
    by (rule order_trans[OF event_le])
      (simp add: projection data_state_bound)
qed

definition active_route_current_prefix_split_algebraic_residual_bound_for
where
  "active_route_current_prefix_split_algebraic_residual_bound_for A i =
    active_route_current_prefix_conceptual_trace_low_degree_error_for A i +
    active_route_current_prefix_conceptual_composition_low_degree_error_for A i +
    active_route_current_prefix_conceptual_alpha_bad_set_error_for A i"

definition active_route_current_prefix_split_conceptual_bound_for
where
  "active_route_current_prefix_split_conceptual_bound_for budgets A i =
    staged_phase_relation_error size
      (staged_query_search_queries budgets i + 1) +
    query_error_bound +
    hash_collision_budget_value 0
      (staged_query_search_queries budgets i + 1) +
    active_route_current_prefix_split_algebraic_residual_bound_for A i"

lemma active_route_current_prefix_conceptual_prefix_collision_hit_at_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (active_route_current_prefix_conceptual_prefix_collision_hit_at i)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
proof -
  have i_le: "i \<le> rounds"
    using i_bound by simp
  have prefix_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      checked_staged_query_prefix_hash_map_output_collision
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    by (rule checked_staged_query_prefix_hash_map_output_collision_bound
        [OF wf controlled i_le])
  show ?thesis
  proof (rule
      checked_staged_security_experiment_with_query_prefix_data_state_bound_by_prefix
        [OF prefix_bound])
    show
      "active_route_current_prefix_conceptual_prefix_collision_hit_at i None
        \<Longrightarrow> checked_staged_query_prefix_hash_map_output_collision None"
      unfolding
        active_route_current_prefix_conceptual_prefix_collision_hit_at_def
        checked_staged_query_prefix_hash_map_output_collision_def
      by simp
  next
    fix prefix_out t out
    assume
      "Some (prefix_out, t) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
      and cont:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>prefix_state.
                checked_staged_after_query_prefix_receive_with_verifier A i
                  prefix_out \<bind>
                (\<lambda>result. return ((prefix_out, prefix_state), result))))
            t)"
      and event:
      "active_route_current_prefix_conceptual_prefix_collision_hit_at i out"
    show
      "checked_staged_query_prefix_hash_map_output_collision
        (Some (prefix_out, t))"
      using cont event
      unfolding
        active_route_current_prefix_conceptual_prefix_collision_hit_at_def
        checked_staged_query_prefix_hash_map_output_collision_def
      by (auto elim!: set_dist_bindE split: option.splits prod.splits)
  qed
qed

lemma active_route_current_prefix_conceptual_hit_residual_split:
  assumes
    "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
      i out"
    and
    "checked_staged_security_with_query_prefix_conceptual_context_residual_at
      out"
  shows
    "active_route_current_prefix_conceptual_prefix_collision_hit_at i out \<or>
     active_route_current_prefix_conceptual_algebraic_residual_hit_at i out"
  using assms
  unfolding
    active_route_current_prefix_conceptual_prefix_collision_hit_at_def
    active_route_current_prefix_conceptual_algebraic_residual_hit_at_def
    checked_staged_security_with_query_prefix_conceptual_context_residual_at_def
  by (cases out) (auto split: prod.splits)

lemma active_route_current_prefix_conceptual_algebraic_residual_split_on_support:
  assumes false_statement: "\<not> exists_valid_trace"
    and support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "active_route_current_prefix_conceptual_algebraic_residual_hit_at i
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "active_route_current_prefix_conceptual_trace_low_degree_bad_at i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     active_route_current_prefix_conceptual_composition_low_degree_bad_at i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     active_route_current_prefix_conceptual_alpha_bad_set_hit_at i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  let ?trace = "query_prefix_trace_conceptual_table prefix prefix_state"
  let ?composition =
    "query_prefix_composition_conceptual_table prefix prefix_state"
  from hit have residual:
    "\<not> trace_table_low_degree ?trace \<or>
     \<not> composition_table_low_degree maxDegree ?composition \<or>
     all_queries_consistent ?trace ?composition (sqp_alphas prefix)"
    unfolding
      active_route_current_prefix_conceptual_algebraic_residual_hit_at_def
    by simp
  show ?thesis
  proof (cases "trace_table_low_degree ?trace")
    case False
    then show ?thesis
      using hit
      unfolding active_route_current_prefix_conceptual_trace_low_degree_bad_at_def
      by simp
  next
    case trace_low: True
    show ?thesis
    proof (cases "composition_table_low_degree maxDegree ?composition")
      case False
      then show ?thesis
        using hit
        unfolding
          active_route_current_prefix_conceptual_composition_low_degree_bad_at_def
        by simp
    next
      case composition_low: True
      from residual trace_low composition_low have all_queries:
        "all_queries_consistent ?trace ?composition (sqp_alphas prefix)"
        by simp
      have prefix_support:
        "Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state)"
        by (rule
            checked_staged_security_with_query_prefix_data_state_prefix_support
            [OF support])
      have alpha_len: "length (sqp_alphas prefix) = length spec"
        by (rule checked_staged_query_prefix_with_state_alphas_length
            [OF prefix_support])
      have alpha_bad:
        "sqp_alphas prefix \<in> composition_trace_bad_alpha_space ?trace"
        by (rule
            low_degree_all_queries_consistent_imp_composition_trace_bad_alpha_space
            [OF false_statement alpha_len trace_low composition_low
              all_queries])
      then show ?thesis
        using hit
        unfolding
          active_route_current_prefix_conceptual_alpha_bad_set_hit_at_def
        by simp
    qed
  qed
qed

lemma active_route_current_prefix_conceptual_algebraic_residual_bound_from_split:
  assumes false_statement: "\<not> exists_valid_trace"
  shows
    "active_route_current_prefix_conceptual_algebraic_residual_error_for A i
      \<le> active_route_current_prefix_split_algebraic_residual_bound_for A i"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Algebraic =
    "active_route_current_prefix_conceptual_algebraic_residual_hit_at i"
  let ?Trace =
    "active_route_current_prefix_conceptual_trace_low_degree_bad_at i"
  let ?Composition =
    "active_route_current_prefix_conceptual_composition_low_degree_bad_at i"
  let ?Alpha =
    "active_route_current_prefix_conceptual_alpha_bad_set_hit_at i"
  have event_le:
    "wp_event ?M ?Algebraic adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?Trace out \<or> ?Composition out \<or> ?Alpha out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit: "?Algebraic out"
    show "?Trace out \<or> ?Composition out \<or> ?Alpha out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          active_route_current_prefix_conceptual_algebraic_residual_hit_at_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
        "out =
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      have support':
        "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist (execute ?M adversary_initial_state)"
        using support unfolding out_eq .
      have hit':
        "?Algebraic
          (Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state))"
        using hit unfolding out_eq .
      show ?thesis
        unfolding out_eq
        by (rule
            active_route_current_prefix_conceptual_algebraic_residual_split_on_support
            [OF false_statement support' hit'])
    qed
  qed
  have union_bound:
    "wp_event ?M (\<lambda>out. ?Trace out \<or> ?Composition out \<or> ?Alpha out)
      adversary_initial_state \<le>
      wp_event ?M ?Trace adversary_initial_state +
      wp_event ?M ?Composition adversary_initial_state +
      wp_event ?M ?Alpha adversary_initial_state"
  proof -
    have "wp_event ?M
        (\<lambda>out. ?Trace out \<or> ?Composition out \<or> ?Alpha out)
        adversary_initial_state \<le>
      wp_event ?M ?Trace adversary_initial_state +
      wp_event ?M (\<lambda>out. ?Composition out \<or> ?Alpha out)
        adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le>
      wp_event ?M ?Trace adversary_initial_state +
      (wp_event ?M ?Composition adversary_initial_state +
       wp_event ?M ?Alpha adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  show ?thesis
    unfolding
      active_route_current_prefix_conceptual_algebraic_residual_error_for_def
      active_route_current_prefix_split_algebraic_residual_bound_for_def
      active_route_current_prefix_conceptual_trace_low_degree_error_for_def
      active_route_current_prefix_conceptual_composition_low_degree_error_for_def
      active_route_current_prefix_conceptual_alpha_bad_set_error_for_def
    by (rule order_trans[OF event_le union_bound])
qed

lemma active_route_current_prefix_authenticated_error_for_le_split_conceptual_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and false_statement: "\<not> exists_valid_trace"
  shows
    "active_route_current_prefix_authenticated_error_for A i \<le>
      active_route_current_prefix_split_conceptual_bound_for budgets A i"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A i"
  let ?Hit =
    "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
      i"
  let ?Conceptual =
    "checked_staged_security_with_query_prefix_conceptual_target_hit"
  let ?Collision =
    "active_route_current_prefix_conceptual_prefix_collision_hit_at i"
  let ?Algebraic =
    "active_route_current_prefix_conceptual_algebraic_residual_hit_at i"
  have event_le:
    "wp_event ?M ?Hit adversary_initial_state \<le>
     wp_event ?M
      (\<lambda>out. ?Conceptual out \<or> ?Collision out \<or> ?Algebraic out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit: "?Hit out"
    have conceptual_or_residual:
      "?Conceptual out \<or>
       checked_staged_security_with_query_prefix_conceptual_context_residual_at
        out"
      by (rule
          checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_imp_conceptual_or_residual_on_support
          [where budgets=budgets and A=A and i=i and out=out,
            OF wf controlled i_bound support hit])
    show "?Conceptual out \<or> ?Collision out \<or> ?Algebraic out"
      using conceptual_or_residual
    proof (elim disjE)
      assume conceptual: "?Conceptual out"
      then show ?thesis by simp
    next
      assume residual:
        "checked_staged_security_with_query_prefix_conceptual_context_residual_at
          out"
      have "?Collision out \<or> ?Algebraic out"
        by (rule active_route_current_prefix_conceptual_hit_residual_split
            [OF hit residual])
      then show ?thesis by simp
    qed
  qed
  have conceptual_bound:
    "wp_event ?M ?Conceptual adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_conceptual_target_hit_bound
        [OF wf controlled i_bound])
  have collision_bound:
    "wp_event ?M ?Collision adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    by (rule
        active_route_current_prefix_conceptual_prefix_collision_hit_at_bound
        [OF wf controlled i_bound])
  have algebraic_bound0:
    "active_route_current_prefix_conceptual_algebraic_residual_error_for A i \<le>
      active_route_current_prefix_split_algebraic_residual_bound_for A i"
    by (rule
        active_route_current_prefix_conceptual_algebraic_residual_bound_from_split
        [OF false_statement])
  have algebraic_bound:
    "wp_event ?M ?Algebraic adversary_initial_state \<le>
      active_route_current_prefix_split_algebraic_residual_bound_for A i"
    using algebraic_bound0
    unfolding active_route_current_prefix_conceptual_algebraic_residual_error_for_def
    by simp
  have union_bound:
    "wp_event ?M
      (\<lambda>out. ?Conceptual out \<or> ?Collision out \<or> ?Algebraic out)
      adversary_initial_state \<le>
      wp_event ?M ?Conceptual adversary_initial_state +
      wp_event ?M ?Collision adversary_initial_state +
      wp_event ?M ?Algebraic adversary_initial_state"
  proof -
    have
      "wp_event ?M
        (\<lambda>out. ?Conceptual out \<or> ?Collision out \<or> ?Algebraic out)
        adversary_initial_state \<le>
       wp_event ?M ?Conceptual adversary_initial_state +
       wp_event ?M (\<lambda>out. ?Collision out \<or> ?Algebraic out)
        adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le>
       wp_event ?M ?Conceptual adversary_initial_state +
       (wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Algebraic adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  have sum_bound:
    "wp_event ?M ?Conceptual adversary_initial_state +
      wp_event ?M ?Collision adversary_initial_state +
      wp_event ?M ?Algebraic adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      active_route_current_prefix_split_algebraic_residual_bound_for A i"
  proof -
    have tail_bound:
      "wp_event ?M ?Collision adversary_initial_state +
       wp_event ?M ?Algebraic adversary_initial_state \<le>
       hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
       active_route_current_prefix_split_algebraic_residual_bound_for A i"
      by (intro add_mono collision_bound algebraic_bound)
    have
      "wp_event ?M ?Conceptual adversary_initial_state +
       (wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Algebraic adversary_initial_state) \<le>
       (staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound) +
       (hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1) +
        active_route_current_prefix_split_algebraic_residual_bound_for A i)"
      by (intro add_mono conceptual_bound tail_bound)
    then show ?thesis
      by (simp add: add.assoc)
  qed
  show ?thesis
    unfolding active_route_current_prefix_authenticated_error_for_def
      active_route_current_prefix_split_conceptual_bound_for_def
    by (rule order_trans[OF event_le])
      (rule order_trans[OF union_bound sum_bound])
qed

definition active_route_current_empty_conceptual_prefix_collision_hit_at
where
  "active_route_current_empty_conceptual_prefix_collision_hit_at
      (_ :: 'f itself) out
    \<longleftrightarrow>
    checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
      0 out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        hash_map_output_collision prefix_state)"

definition active_route_current_empty_conceptual_trace_low_degree_bad_at
where
  "active_route_current_empty_conceptual_trace_low_degree_bad_at
      (_ :: 'f itself) out
    \<longleftrightarrow>
    checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
      0 out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        \<not> trace_table_low_degree
          (query_prefix_trace_conceptual_table prefix prefix_state))"

definition active_route_current_empty_conceptual_alpha_bad_set_hit_at
where
  "active_route_current_empty_conceptual_alpha_bad_set_hit_at
      (_ :: 'f itself) out
    \<longleftrightarrow>
    checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
      0 out \<and>
    (case out of
      None \<Rightarrow> False
    | Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<Rightarrow>
        sqp_alphas prefix \<in>
          composition_trace_bad_alpha_space
            (query_prefix_trace_conceptual_table prefix prefix_state))"

definition active_route_current_empty_conceptual_prefix_collision_error_for
where
  "active_route_current_empty_conceptual_prefix_collision_error_for A =
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A 0)
      (active_route_current_empty_conceptual_prefix_collision_hit_at
        TYPE('f))
      adversary_initial_state"

definition active_route_current_empty_conceptual_trace_low_degree_error_for
where
  "active_route_current_empty_conceptual_trace_low_degree_error_for A =
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A 0)
      (active_route_current_empty_conceptual_trace_low_degree_bad_at
        TYPE('f))
      adversary_initial_state"

definition active_route_current_empty_conceptual_alpha_bad_set_error_for
where
  "active_route_current_empty_conceptual_alpha_bad_set_error_for A =
    wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A 0)
      (active_route_current_empty_conceptual_alpha_bad_set_hit_at
        TYPE('f))
      adversary_initial_state"

lemma active_route_current_empty_conceptual_alpha_bad_set_hit_at_imp_data_state_alpha_prefix_bad_set_hit_on_support:
  assumes support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A 0)
            adversary_initial_state)"
    and candidate:
      "\<And>alpha_prefix alpha_prefix_state.
        alpha_prefix =
          (sqp_trace_root prefix, sqp_trace_fri_roots prefix,
            sqp_trace_fri_challenges prefix, sqp_trace_final prefix) \<Longrightarrow>
        Some (alpha_prefix, alpha_prefix_state) \<in>
          set_dist
            (execute (staged_alpha_prefix_program A)
              adversary_initial_state) \<Longrightarrow>
        query_prefix_trace_conceptual_table prefix prefix_state \<in>
          alpha_prefix_trace_table_candidates alpha_prefix_state
            (sqp_trace_root prefix)"
    and hit:
      "active_route_current_empty_conceptual_alpha_bad_set_hit_at
        TYPE('f)
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
      composition_trace_bad_alpha_space
      (Some (((data, attacker_state), result), final_state))"
proof -
  obtain alpha_prefix alpha_prefix_state where alpha_prefix_eq:
      "alpha_prefix =
        (sqp_trace_root prefix, sqp_trace_fri_roots prefix,
          sqp_trace_fri_challenges prefix, sqp_trace_final prefix)"
    and alpha_support:
      "Some (alpha_prefix, alpha_prefix_state) \<in>
        set_dist
          (execute (staged_alpha_prefix_program A) adversary_initial_state)"
    by (rule checked_staged_security_with_query_prefix_data_state_alpha_prefix_support
        [OF support])
  have table_candidate:
    "query_prefix_trace_conceptual_table prefix prefix_state \<in>
      alpha_prefix_trace_table_candidates alpha_prefix_state
        (sqp_trace_root prefix)"
    by (rule candidate[OF alpha_prefix_eq alpha_support])
  have alphas_eq: "staged_alphas data = sqp_alphas prefix"
    by (rule checked_staged_security_with_query_prefix_data_state_alphas_eq
        [OF support])
  have alpha_bad:
    "sqp_alphas prefix \<in>
      composition_trace_bad_alpha_space
        (query_prefix_trace_conceptual_table prefix prefix_state)"
    using hit
    unfolding active_route_current_empty_conceptual_alpha_bad_set_hit_at_def
    by simp
  have staged_alpha_bad:
    "staged_alphas data \<in>
      composition_trace_bad_alpha_space
        (query_prefix_trace_conceptual_table prefix prefix_state)"
    using alpha_bad alphas_eq by simp
  have staged_alpha_in_space: "staged_alphas data \<in> alpha_space"
    using staged_alpha_bad composition_trace_bad_alpha_space_subset_alpha_space
    by blast
  have root_eq: "staged_trace_root data = sqp_trace_root prefix"
    using support
    unfolding
      checked_staged_security_experiment_with_query_prefix_data_state_def
      checked_staged_after_query_prefix_receive_with_verifier_def
      checked_staged_after_query_prefix_receive_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have union_hit:
    "staged_alphas data \<in>
      alpha_prefix_union_bad_sets alpha_prefix_state
        composition_trace_bad_alpha_space (staged_trace_root data)"
  proof -
    have table_candidate':
      "query_prefix_trace_conceptual_table prefix prefix_state \<in>
        alpha_prefix_trace_table_candidates alpha_prefix_state
          (staged_trace_root data)"
      using table_candidate root_eq by simp
    show ?thesis
    unfolding alpha_prefix_union_bad_sets_def
      using table_candidate' staged_alpha_bad staged_alpha_in_space
      by auto
  qed
  have prefix_components:
    "staged_trace_root data = fst alpha_prefix \<and>
     staged_trace_fri_roots data = fst (snd alpha_prefix) \<and>
     staged_trace_fri_challenges data = fst (snd (snd alpha_prefix)) \<and>
     staged_trace_final data = snd (snd (snd alpha_prefix))"
    using support alpha_prefix_eq
    unfolding
      checked_staged_security_experiment_with_query_prefix_data_state_def
      checked_staged_after_query_prefix_receive_with_verifier_def
      checked_staged_after_query_prefix_receive_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  show ?thesis
    unfolding checked_staged_security_with_data_state_alpha_prefix_bad_set_hit_def
    using alpha_support prefix_components union_hit
    by auto
qed

lemma active_route_current_empty_conceptual_alpha_bad_set_error_for_bound_from_data_state_alpha_prefix:
  assumes candidate:
      "\<And>prefix prefix_state raw raw_state data attacker_state result
          final_state alpha_prefix alpha_prefix_state.
        Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state A 0)
              adversary_initial_state) \<Longrightarrow>
        alpha_prefix =
          (sqp_trace_root prefix, sqp_trace_fri_roots prefix,
            sqp_trace_fri_challenges prefix, sqp_trace_final prefix) \<Longrightarrow>
        Some (alpha_prefix, alpha_prefix_state) \<in>
          set_dist
            (execute (staged_alpha_prefix_program A)
              adversary_initial_state) \<Longrightarrow>
        query_prefix_trace_conceptual_table prefix prefix_state \<in>
          alpha_prefix_trace_table_candidates alpha_prefix_state
            (sqp_trace_root prefix)"
    and data_state_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> C"
  shows
    "active_route_current_empty_conceptual_alpha_bad_set_error_for A \<le> C"
proof -
  let ?Data =
    "checked_staged_security_with_data_state_alpha_prefix_bad_set_hit A
      composition_trace_bad_alpha_space"
  let ?Projected =
    "\<lambda>out. case out of
      None \<Rightarrow> ?Data None
    | Some (packed, t) \<Rightarrow> ?Data (Some (snd packed, t))"
  let ?E =
    "active_route_current_empty_conceptual_alpha_bad_set_hit_at
      TYPE('f)"
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A 0)
      ?E adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A 0)
      ?Projected adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A 0)
            adversary_initial_state)"
      and hit: "?E out"
    show "?Projected out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding active_route_current_empty_conceptual_alpha_bad_set_hit_at_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
        "out =
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      have support':
        "Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state) \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state A 0)
              adversary_initial_state)"
        using support unfolding out_eq .
      have hit':
        "active_route_current_empty_conceptual_alpha_bad_set_hit_at
          TYPE('f)
          (Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state))"
        using hit unfolding out_eq .
      have data_hit:
        "?Data (Some (((data, attacker_state), result), final_state))"
        by (rule
            active_route_current_empty_conceptual_alpha_bad_set_hit_at_imp_data_state_alpha_prefix_bad_set_hit_on_support
            [OF support' _ hit'])
          (rule candidate[OF support'])
      show ?thesis
        unfolding out_eq using data_hit by simp
    qed
  qed
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A 0)
      ?Projected adversary_initial_state =
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?Data adversary_initial_state"
    using checked_staged_security_experiment_with_query_prefix_data_state_projection_event
      [OF rounds_positive, of A ?Data]
    by simp
  show ?thesis
    unfolding active_route_current_empty_conceptual_alpha_bad_set_error_for_def
    by (rule order_trans[OF event_le])
      (simp add: projection data_state_bound)
qed

definition active_route_current_empty_split_residual_bound_for
where
  "active_route_current_empty_split_residual_bound_for A =
    active_route_current_empty_conceptual_prefix_collision_error_for A +
    active_route_current_empty_conceptual_trace_low_degree_error_for A +
    active_route_current_empty_conceptual_alpha_bad_set_error_for A"

definition active_route_current_empty_split_conceptual_bound_for
where
  "active_route_current_empty_split_conceptual_bound_for budgets A =
    staged_phase_relation_error size
      (staged_query_search_queries budgets 0 + 1) +
    query_error_bound +
    active_route_current_empty_split_residual_bound_for A +
    (active_route_transcript_pre_error_for A +
      staged_concrete_transcript_target_error_bound)"

lemma active_route_current_empty_conceptual_prefix_collision_hit_at_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "active_route_current_empty_conceptual_prefix_collision_error_for A \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets 0 + 1)"
proof -
  have i_le: "0 \<le> rounds"
    by simp
  have prefix_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A 0)
      checked_staged_query_prefix_hash_map_output_collision
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_query_search_queries budgets 0 + 1)"
    by (rule checked_staged_query_prefix_hash_map_output_collision_bound
        [OF wf controlled i_le])
  show ?thesis
    unfolding active_route_current_empty_conceptual_prefix_collision_error_for_def
  proof (rule
      checked_staged_security_experiment_with_query_prefix_data_state_bound_by_prefix
        [OF prefix_bound])
    show
      "active_route_current_empty_conceptual_prefix_collision_hit_at
        TYPE('f) None
        \<Longrightarrow> checked_staged_query_prefix_hash_map_output_collision None"
      unfolding
        active_route_current_empty_conceptual_prefix_collision_hit_at_def
        checked_staged_query_prefix_hash_map_output_collision_def
      by simp
  next
    fix prefix_out t out
    assume
      "Some (prefix_out, t) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A 0)
            adversary_initial_state)"
      and cont:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>prefix_state.
                checked_staged_after_query_prefix_receive_with_verifier A 0
                  prefix_out \<bind>
                (\<lambda>result. return ((prefix_out, prefix_state), result))))
            t)"
      and event:
      "active_route_current_empty_conceptual_prefix_collision_hit_at
        TYPE('f) out"
    show
      "checked_staged_query_prefix_hash_map_output_collision
        (Some (prefix_out, t))"
      using cont event
      unfolding
        active_route_current_empty_conceptual_prefix_collision_hit_at_def
        checked_staged_query_prefix_hash_map_output_collision_def
      by (auto elim!: set_dist_bindE split: option.splits prod.splits)
  qed
qed

lemma active_route_current_empty_conceptual_residual_split_on_support:
  assumes false_statement: "\<not> exists_valid_trace"
    and support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A 0)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
        0
        (Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state))"
  shows
    "active_route_current_empty_conceptual_prefix_collision_hit_at
      TYPE('f)
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     active_route_current_empty_conceptual_trace_low_degree_bad_at
      TYPE('f)
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)) \<or>
     active_route_current_empty_conceptual_alpha_bad_set_hit_at
      TYPE('f)
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  let ?trace = "query_prefix_trace_conceptual_table prefix prefix_state"
  let ?composition = "replicate (scale * clength) (sqp_composition_final prefix)"
  from hit have residual:
    "hash_map_output_collision prefix_state \<or>
     \<not> trace_table_low_degree ?trace \<or>
     all_queries_consistent ?trace ?composition (sqp_alphas prefix)"
    unfolding
      checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at_def
      checked_staged_security_with_query_prefix_conceptual_empty_context_residual_at_def
    by simp
  show ?thesis
  proof (cases "hash_map_output_collision prefix_state")
    case True
    then show ?thesis
      using hit
      unfolding
        active_route_current_empty_conceptual_prefix_collision_hit_at_def
      by simp
  next
    case clean: False
    show ?thesis
    proof (cases "trace_table_low_degree ?trace")
      case False
      then show ?thesis
        using hit
        unfolding
          active_route_current_empty_conceptual_trace_low_degree_bad_at_def
        by simp
    next
      case trace_low: True
      from residual clean trace_low have all_queries:
        "all_queries_consistent ?trace ?composition (sqp_alphas prefix)"
        by simp
      have prefix_support:
        "Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A 0)
              adversary_initial_state)"
        by (rule
            checked_staged_security_with_query_prefix_data_state_prefix_support
            [OF support])
      have alpha_len: "length (sqp_alphas prefix) = length spec"
        by (rule checked_staged_query_prefix_with_state_alphas_length
            [OF prefix_support])
      have alpha_bad:
        "sqp_alphas prefix \<in> composition_trace_bad_alpha_space ?trace"
        by (rule
            low_degree_all_queries_consistent_imp_composition_trace_bad_alpha_space
            [OF false_statement alpha_len trace_low
              constant_composition_table_low_degree all_queries])
      then show ?thesis
        using hit
        unfolding
          active_route_current_empty_conceptual_alpha_bad_set_hit_at_def
        by simp
    qed
  qed
qed

lemma active_route_current_empty_conceptual_residual_bound_from_split:
  assumes false_statement: "\<not> exists_valid_trace"
  shows
    "active_route_current_empty_conceptual_residual_error_for TYPE('f) A \<le>
      active_route_current_empty_split_residual_bound_for A"
proof -
  let ?M = "checked_staged_security_experiment_with_query_prefix_data_state A 0"
  let ?Residual =
    "\<lambda>out.
      checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
        0 out"
  let ?Collision =
    "active_route_current_empty_conceptual_prefix_collision_hit_at
      TYPE('f)"
  let ?Trace =
    "active_route_current_empty_conceptual_trace_low_degree_bad_at
      TYPE('f)"
  let ?Alpha =
    "active_route_current_empty_conceptual_alpha_bad_set_hit_at
      TYPE('f)"
  have event_le:
    "wp_event ?M ?Residual adversary_initial_state \<le>
     wp_event ?M (\<lambda>out. ?Collision out \<or> ?Trace out \<or> ?Alpha out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit: "?Residual out"
    show "?Collision out \<or> ?Trace out \<or> ?Alpha out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at_def
          checked_staged_security_with_query_prefix_conceptual_empty_context_residual_at_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
        "out =
          Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      have support':
        "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist (execute ?M adversary_initial_state)"
        using support unfolding out_eq .
      have hit':
        "?Residual
          (Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state))"
        using hit unfolding out_eq .
      show ?thesis
        unfolding out_eq
        by (rule
            active_route_current_empty_conceptual_residual_split_on_support
            [OF false_statement support' hit'])
    qed
  qed
  have union_bound:
    "wp_event ?M (\<lambda>out. ?Collision out \<or> ?Trace out \<or> ?Alpha out)
      adversary_initial_state \<le>
      wp_event ?M ?Collision adversary_initial_state +
      wp_event ?M ?Trace adversary_initial_state +
      wp_event ?M ?Alpha adversary_initial_state"
  proof -
    have
      "wp_event ?M
        (\<lambda>out. ?Collision out \<or> ?Trace out \<or> ?Alpha out)
        adversary_initial_state \<le>
       wp_event ?M ?Collision adversary_initial_state +
       wp_event ?M (\<lambda>out. ?Trace out \<or> ?Alpha out)
        adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le>
       wp_event ?M ?Collision adversary_initial_state +
       (wp_event ?M ?Trace adversary_initial_state +
        wp_event ?M ?Alpha adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  show ?thesis
    unfolding
      active_route_current_empty_conceptual_residual_error_for_def
      active_route_current_empty_split_residual_bound_for_def
      active_route_current_empty_conceptual_prefix_collision_error_for_def
      active_route_current_empty_conceptual_trace_low_degree_error_for_def
      active_route_current_empty_conceptual_alpha_bad_set_error_for_def
    by (rule order_trans[OF event_le union_bound])
qed

lemma active_route_current_empty_query_error_for_le_split_conceptual_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "active_route_current_empty_query_error_for A \<le>
      active_route_current_empty_split_conceptual_bound_for budgets A"
proof -
  have i_bound: "0 < rounds"
    using rounds_positive by simp
  have residual_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A 0)
      (checked_staged_security_with_query_prefix_conceptual_empty_context_residual_hit_at
        0)
      adversary_initial_state \<le>
      active_route_current_empty_split_residual_bound_for A"
    using active_route_current_empty_conceptual_residual_bound_from_split
        [OF false_statement]
    unfolding active_route_current_empty_conceptual_residual_error_for_def .
  have pre_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_pre_hit
      adversary_initial_state \<le> active_route_transcript_pre_error_for A"
    by (simp add: active_route_transcript_pre_error_for_def)
  have new_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state \<le> staged_concrete_transcript_target_error_bound"
    by (rule checked_staged_security_with_data_state_transcript_new_hit_bound
        [OF wf controlled])
  show ?thesis
    unfolding active_route_current_empty_query_error_for_def
      active_route_current_empty_split_conceptual_bound_for_def
    by (rule
        checked_staged_security_with_data_state_current_empty_query_opening_hit_at_bound_from_conceptual_empty_residual_and_transcript
        [OF wf controlled i_bound residual_bound pre_bound new_bound])
qed

theorem stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_restricted_trace_endpoint:
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
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound)) +
      (\<Sum>i<rounds.
        active_route_current_prefix_split_conceptual_bound_for budgets A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
    concrete_trace_header_restricted_one_step_error_for budgets A +
      concrete_composition_restricted_one_step_error_for budgets A +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound) +
      concrete_trace_empty_header_restricted_sampled_split_one_step_error_for budgets A +
      active_route_current_empty_split_conceptual_bound_for budgets A)"
proof -
  have trace_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state
    \<le> concrete_trace_header_restricted_one_step_error_for budgets A"
    unfolding concrete_trace_header_restricted_one_step_error_for_def
    by (rule trace_header_restricted_one_step_error_for_bound
        [OF wf controlled])
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state
    \<le> concrete_composition_restricted_one_step_error_for budgets A"
    unfolding concrete_composition_restricted_one_step_error_for_def
    by (rule composition_restricted_verifier_tied_controlled_error_for_bound
        [OF wf controlled])
  have empty_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state
    \<le> concrete_trace_empty_header_restricted_sampled_split_one_step_error_for
        budgets A"
    unfolding
      concrete_trace_empty_header_restricted_sampled_split_one_step_error_for_def
    by (rule trace_empty_header_restricted_sampled_split_one_step_error_for_bound
        [OF wf controlled])
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
        (\<Sum>i<rounds.
          active_route_current_prefix_authenticated_error_for A i +
          (active_route_transcript_pre_error_for A +
            staged_concrete_transcript_target_error_bound) +
          (active_route_transcript_pre_error_for A +
            staged_concrete_transcript_target_error_bound)) +
      concrete_trace_header_restricted_one_step_error_for budgets A +
        concrete_composition_restricted_one_step_error_for budgets A +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        concrete_trace_empty_header_restricted_sampled_split_one_step_error_for budgets A +
        active_route_current_empty_query_error_for A)"
    by (rule
        stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_from_active_fri_bounds
        [OF false_statement wf controlled trace_bound comp_bound empty_bound])
  have prefix_terms:
    "(\<Sum>i<rounds.
        active_route_current_prefix_authenticated_error_for A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound))
      \<le>
     (\<Sum>i<rounds.
        active_route_current_prefix_split_conceptual_bound_for budgets A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound))"
    by (intro sum_mono add_mono order_refl
        active_route_current_prefix_authenticated_error_for_le_split_conceptual_bound
        [OF wf controlled _ false_statement])
      simp
  have empty_term:
    "active_route_current_empty_query_error_for A \<le>
      active_route_current_empty_split_conceptual_bound_for budgets A"
    by (rule active_route_current_empty_query_error_for_le_split_conceptual_bound
        [OF false_statement wf controlled])
  have route_le:
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
      concrete_trace_header_restricted_one_step_error_for budgets A +
        concrete_composition_restricted_one_step_error_for budgets A +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        concrete_trace_empty_header_restricted_sampled_split_one_step_error_for budgets A +
        active_route_current_empty_query_error_for A)
      \<le>
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
          active_route_current_prefix_split_conceptual_bound_for budgets A i +
          (active_route_transcript_pre_error_for A +
            staged_concrete_transcript_target_error_bound) +
          (active_route_transcript_pre_error_for A +
            staged_concrete_transcript_target_error_bound)) +
      concrete_trace_header_restricted_one_step_error_for budgets A +
        concrete_composition_restricted_one_step_error_for budgets A +
      (composition_error_bound +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        hash_collision_budget_value 0
          (staged_alpha_search_queries budgets 0) +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        concrete_trace_empty_header_restricted_sampled_split_one_step_error_for budgets A +
        active_route_current_empty_split_conceptual_bound_for budgets A)"
    by (intro add_mono order_refl prefix_terms empty_term)
  show ?thesis
    by (rule order_trans[OF route route_le])
qed

definition concrete_restricted_trace_stark_soundness_bound_for
where
  "concrete_restricted_trace_stark_soundness_bound_for budgets A =
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
        active_route_current_prefix_split_conceptual_bound_for budgets A i +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound) +
        (active_route_transcript_pre_error_for A +
          staged_concrete_transcript_target_error_bound)) +
    concrete_trace_header_restricted_one_step_error_for budgets A +
      concrete_composition_restricted_one_step_error_for budgets A +
    (composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (active_route_transcript_pre_error_for A +
        staged_concrete_transcript_target_error_bound) +
      concrete_trace_empty_header_restricted_sampled_split_one_step_error_for budgets A +
      active_route_current_empty_split_conceptual_bound_for budgets A)"

theorem stark_soundness:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows "checked_staged_adversary_acceptance_probability A \<le>
    concrete_restricted_trace_stark_soundness_bound_for budgets A"
  unfolding concrete_restricted_trace_stark_soundness_bound_for_def
  by (rule
      stark_soundness_from_current_public_prefix_current_query_relevant_drift_route_restricted_trace_endpoint
      [OF false_statement wf controlled])

end

end
