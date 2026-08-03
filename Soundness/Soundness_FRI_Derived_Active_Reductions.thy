(*  Title:      Stark/Soundness_FRI_Derived_Active_Reductions.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Derived_Active_Reductions
  imports
    Soundness_FRI_Staged_Replay_Bounds
    Soundness_FRI_Full_Cover_Staged_Bounds
begin

text \<open>
  Derived active-FRI packaging.

  This layer keeps the near-threshold staged replay theory stable.  It packages
  the already proved trace and composition verifier-state reductions into the
  active-FRI interface consumed by the public route.  It does not add protocol
  assumptions or change the FRI model.
\<close>

context soundness
begin

lemma trace_fri_header_tied_reduction_from_envelope_witness_domain_without_head_slot_and_selected_zero:
  assumes future: "trace_fri_future_fresh s"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and challenge_bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le> R"
    and proximity:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and witness_length:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_witness_length_failure s) s \<le> W"
    and domain:
      "wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and zero:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> z_b"
    and merkle:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    and structural:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s
        \<le> h_b"
    and next_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap s) s \<le> n_b"
    and successor:
      "wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap s) s \<le> s_b"
    and total:
      "(R + (P + I + W + D)) +
        (((((p_b + h_b) + p_b) + n_b + s_b +
          (p_b + 0 + 0)) + p_b) + 0 + z_b)
        \<le> trace_fri_error"
  shows "trace_fri_header_tied_reduction s"
  by (rule trace_fri_header_tied_reduction_from_residual_obligations)
    (rule
      trace_fri_header_tied_residual_obligations_from_envelope_witness_domain_without_head_slot_and_selected_zero
      [OF future envelope subset challenge_bound proximity index
        witness_length domain zero merkle structural next_bound successor
        total])

lemma composition_fri_verifier_tied_reduction_from_envelope_witness_domain_slot_zero:
  assumes future: "composition_fri_future_fresh s"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and challenge_bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> R"
    and proximity:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure s bad) s
        \<le> P"
    and index:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and witness_length:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_witness_length_failure s) s
        \<le> W"
    and domain:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and merkle:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    and next_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap s) s \<le> n_b"
    and successor:
      "wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap s) s \<le> s_b"
    and final_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap s) s \<le> g_b"
    and total:
      "(R + (P + I + W + D)) +
        (((p_b + 0) + n_b + s_b + g_b + p_b) + 0)
        \<le> composition_fri_error"
  shows "composition_fri_verifier_tied_reduction s"
  by (rule composition_fri_verifier_tied_reduction_from_residual_obligations)
    (rule
      composition_fri_verifier_tied_residual_obligations_from_envelope_witness_domain_slot_zero
      [OF future envelope subset challenge_bound proximity index
        witness_length domain merkle next_bound successor final_bound total])

lemma composition_fri_verifier_tied_reduction_from_envelope_witness_domain_merkle:
  assumes future: "composition_fri_future_fresh s"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and challenge_bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> R"
    and proximity:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure s bad) s
        \<le> P"
    and index:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and witness_length:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_witness_length_failure s) s
        \<le> W"
    and domain:
      "wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and merkle:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and total:
      "(R + (P + I + W + D)) +
        (((M + 0) + (M + 0) + (M + 0) + (M + 0 + 0) + M) + 0)
        \<le> composition_fri_error"
  shows "composition_fri_verifier_tied_reduction s"
proof -
  have slot:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> 0"
    by (rule
        wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero)
  have next_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_next_value_replay_gap s) s \<le> M + 0"
    by (rule
        wp_composition_fri_verifier_tied_next_value_replay_gap_bound_from_merkle_and_slot)
      (rule merkle, rule slot)
  have successor:
    "wp_event verify_monad
      (composition_fri_verifier_tied_successor_replay_gap s) s \<le> M + 0"
    by (rule
        wp_composition_fri_verifier_tied_successor_replay_gap_bound_from_merkle_and_slot)
      (rule merkle, rule slot)
  have final_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap s) s
      \<le> M + 0 + 0"
    by (rule
        wp_composition_fri_verifier_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
      (rule merkle, rule slot,
       rule
        wp_composition_fri_verifier_tied_final_value_selected_step_missing_gap_zero)
  show ?thesis
    by (rule
        composition_fri_verifier_tied_reduction_from_envelope_witness_domain_slot_zero
        [OF future envelope subset challenge_bound proximity index
          witness_length domain merkle next_bound successor final_bound total])
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_full_cover_domain_conflict_and_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and domain_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> DL"
    and sampled_domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> SD"
    and conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
    and zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      ((F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
        (P + I + (I + DL) + (I + SD))) + (C + Z)"
proof (rule
    checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_sampled_conflict_and_staged_zero)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
    by (rule
        checked_staged_security_trace_fri_header_tied_sampled_layer_chain_bound_from_full_cover_fresh_and_domain_split
        [OF wf controlled finite_B envelope fresh_bound proximity index
          domain_length sampled_domain])
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_sampled_assignment_conflict)
      adversary_initial_state \<le> C"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (auto simp: trace_fri_header_tied_sampled_assignment_conflict_def
        accepted_fri_opening_transcript_def conflict_bound)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state \<le> Z"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (auto simp: trace_fri_header_tied_zero_round_final_obstruction_def
        accepted_fri_opening_transcript_def zero_bound)
qed

lemma checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_full_cover_witness_domain_conflict_and_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and witness_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_witness_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> W"
    and domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> D"
    and conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
    and zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le>
      ((F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
        (P + I + W + D)) + (C + Z)"
proof (rule
    checked_staged_security_trace_fri_header_tied_partial_candidate_bound_from_sampled_conflict_and_staged_zero)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + W + D)"
    by (rule
        checked_staged_security_trace_fri_header_tied_sampled_layer_chain_bound_from_full_cover_fresh_and_witness_domain
        [OF wf controlled finite_B envelope fresh_bound proximity index
          witness_length domain])
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_sampled_assignment_conflict)
      adversary_initial_state \<le> C"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (auto simp: trace_fri_header_tied_sampled_assignment_conflict_def
        accepted_fri_opening_transcript_def conflict_bound)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_header_tied_zero_round_final_obstruction)
      adversary_initial_state \<le> Z"
    by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
      (auto simp: trace_fri_header_tied_zero_round_final_obstruction_def
        accepted_fri_opening_transcript_def zero_bound)
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_full_cover_domain_conflict_and_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and envelope:
    "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets bad dg composition_table
        \<subseteq> B dg"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and domain_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> DL"
    and sampled_domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> SD"
    and conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
    and zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      ((F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
        (P + I + (I + DL) + (I + SD))) + (C + Z)"
proof (rule
    checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_sampled_and_missing)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
    by (rule
        checked_staged_security_composition_fri_verifier_tied_sampled_layer_chain_bound_from_full_cover_fresh_and_domain_split
        [OF wf controlled finite_B envelope fresh_bound proximity index
          domain_length sampled_domain])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (composition_fri_verifier_tied_missing_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> C + Z"
    by (rule
        wp_composition_fri_verifier_tied_missing_sampled_bound_from_assignment_obstruction)
      (rule
        wp_composition_fri_verifier_tied_assignment_obstruction_bound_from_conflict_and_zero
        [OF conflict_bound[OF support] zero_bound[OF support]])
qed

lemma checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_full_cover_witness_domain_conflict_and_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "\<And>dg. finite (B dg)"
    and envelope:
    "\<And>data attacker_state dg composition_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_multiround_bad_sets bad dg composition_table
        \<subseteq> B dg"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and witness_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_witness_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> W"
    and domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> D"
    and conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
    and zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le>
      ((F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
        (P + I + W + D)) + (C + Z)"
proof (rule
    checked_staged_security_composition_fri_verifier_tied_partial_candidate_bound_from_sampled_and_missing)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_sampled_layer_chain)
      adversary_initial_state \<le>
      (F +
        hash_relation_budget_value
          (\<Sum>dg \<in> (UNIV :: 'f set).
            card (B dg) * ceil_log (maxDegree + 1))
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + W + D)"
    by (rule
        checked_staged_security_composition_fri_verifier_tied_sampled_layer_chain_bound_from_full_cover_fresh_and_witness_domain
        [OF wf controlled finite_B envelope fresh_bound proximity index
          witness_length domain])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (composition_fri_verifier_tied_missing_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      \<le> C + Z"
    by (rule
        wp_composition_fri_verifier_tied_missing_sampled_bound_from_assignment_obstruction)
      (rule
        wp_composition_fri_verifier_tied_assignment_obstruction_bound_from_conflict_and_zero
        [OF conflict_bound[OF support] zero_bound[OF support]])
qed

lemma checked_staged_security_trace_fri_empty_header_bound_from_full_cover_domain_conflict_and_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and domain_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> DL"
    and sampled_domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_sampled_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> SD"
    and conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
    and zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      ((F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
        (P + I + (I + DL) + (I + SD))) + (C + Z)"
proof (rule checked_staged_security_trace_fri_empty_header_bound_from_sampled_and_missing)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + (I + DL) + (I + SD))"
    by (rule
        checked_staged_security_trace_fri_sampled_layer_chain_bound_from_full_cover_fresh_and_domain_split
        [OF wf controlled finite_B envelope fresh_bound proximity index
          domain_length sampled_domain])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have obstruction:
    "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction ?s) ?s \<le> C + Z"
  proof -
    have "wp_event verify_monad
        (trace_fri_sampled_layer_assignment_obstruction ?s) ?s \<le>
      wp_event verify_monad
        (\<lambda>out. trace_fri_sampled_assignment_conflict ?s out \<or>
          trace_fri_zero_round_final_obstruction ?s out) ?s"
      by (rule wp_event_mono)
        (rule
          trace_fri_sampled_layer_assignment_obstruction_imp_conflict_or_zero_round_final)
    also have "... \<le>
        wp_event verify_monad (trace_fri_sampled_assignment_conflict ?s) ?s +
        wp_event verify_monad (trace_fri_zero_round_final_obstruction ?s) ?s"
      by (rule wp_event_union_bound)
    also have "... \<le> C + Z"
      by (rule add_mono[OF conflict_bound[OF support]
            zero_bound[OF support]])
    finally show ?thesis .
  qed
  show "wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain
        ?s) ?s \<le> C + Z"
    by (rule wp_trace_fri_reachable_missing_sampled_bound_from_assignment_obstruction)
      (rule obstruction)
qed

lemma checked_staged_security_trace_fri_empty_header_bound_from_full_cover_witness_domain_conflict_and_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and finite_B: "finite B"
    and envelope:
    "\<And>data attacker_state trace_table.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_challenge_list_fresh_hit s B))
      adversary_initial_state \<le> F"
    and proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and witness_length:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_witness_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> W"
    and domain:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_domain_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> D"
    and conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> C"
    and zero_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_zero_round_final_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Z"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      ((F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
        (P + I + W + D)) + (C + Z)"
proof (rule checked_staged_security_trace_fri_empty_header_bound_from_sampled_and_missing)
  show "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_sampled_layer_chain)
      adversary_initial_state
      \<le>
      (F +
        hash_relation_budget_value (card B * ceil_log clength)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) +
      (P + I + W + D)"
    by (rule
        checked_staged_security_trace_fri_sampled_layer_chain_bound_from_full_cover_fresh_and_witness_domain
        [OF wf controlled finite_B envelope fresh_bound proximity index
          witness_length domain])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have obstruction:
    "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction ?s) ?s \<le> C + Z"
  proof -
    have "wp_event verify_monad
        (trace_fri_sampled_layer_assignment_obstruction ?s) ?s \<le>
      wp_event verify_monad
        (\<lambda>out. trace_fri_sampled_assignment_conflict ?s out \<or>
          trace_fri_zero_round_final_obstruction ?s out) ?s"
      by (rule wp_event_mono)
        (rule
          trace_fri_sampled_layer_assignment_obstruction_imp_conflict_or_zero_round_final)
    also have "... \<le>
        wp_event verify_monad (trace_fri_sampled_assignment_conflict ?s) ?s +
        wp_event verify_monad (trace_fri_zero_round_final_obstruction ?s) ?s"
      by (rule wp_event_union_bound)
    also have "... \<le> C + Z"
      by (rule add_mono[OF conflict_bound[OF support]
            zero_bound[OF support]])
    finally show ?thesis .
  qed
  show "wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain
        ?s) ?s \<le> C + Z"
    by (rule wp_trace_fri_reachable_missing_sampled_bound_from_assignment_obstruction)
      (rule obstruction)
qed

lemma active_fri_reductions_for_from_component_reductions:
  assumes trace_header:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_header_tied_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
    and composition:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_verifier_tied_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
    and empty_trace:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_empty_header_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows "active_fri_reductions_for A"
  unfolding active_fri_reductions_for_def
  by (intro allI impI conjI)
    (erule trace_header, erule composition, erule empty_trace)

lemma trace_fri_empty_header_reduction_from_sampled_and_missing_bounds:
  fixes R M :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain s) s \<le> M"
    and total_bound:
    "R + M \<le> trace_fri_error"
  shows "trace_fri_empty_header_reduction s"
proof -
  have reachable:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le> R + M"
    by (rule wp_trace_fri_reachable_bound_from_sampled_and_missing
        [OF sampled_bound missing_bound])
  have empty:
    "wp_event verify_monad
      (trace_fri_bad_with_empty_composition_header_candidates s) s \<le>
      R + M"
    by (rule order_trans[OF _ reachable])
      (rule wp_event_mono,
        rule
          trace_fri_bad_with_empty_composition_header_candidates_imp_reachable_partial_candidate)
  show ?thesis
    unfolding trace_fri_empty_header_reduction_def
    by (rule order_trans[OF empty total_bound])
qed

lemma trace_fri_empty_header_reduction_from_sampled_and_assignment_obstruction_bounds:
  fixes R M :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> R"
    and obstruction_bound:
    "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction s) s \<le> M"
    and total_bound:
    "R + M \<le> trace_fri_error"
  shows "trace_fri_empty_header_reduction s"
proof (rule trace_fri_empty_header_reduction_from_sampled_and_missing_bounds)
  show "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> R"
    by (rule sampled_bound)
  show "wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain s) s \<le> M"
    by (rule
        wp_trace_fri_reachable_missing_sampled_bound_from_assignment_obstruction
        [OF obstruction_bound])
  show "R + M \<le> trace_fri_error"
    by (rule total_bound)
qed

lemma wp_trace_fri_sampled_layer_assignment_obstruction_bound_from_conflict_and_zero:
  assumes conflict_bound:
    "wp_event verify_monad
      (trace_fri_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
    "wp_event verify_monad
      (trace_fri_zero_round_final_obstruction s) s \<le> Z"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction s) s \<le> C + Z"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction s) s \<le>
    wp_event verify_monad
      (\<lambda>out. trace_fri_sampled_assignment_conflict s out \<or>
        trace_fri_zero_round_final_obstruction s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_layer_assignment_obstruction_imp_conflict_or_zero_round_final)
  also have "... \<le>
      wp_event verify_monad (trace_fri_sampled_assignment_conflict s) s +
      wp_event verify_monad (trace_fri_zero_round_final_obstruction s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> C + Z"
    by (rule add_mono[OF conflict_bound zero_bound])
  finally show ?thesis .
qed

lemma trace_fri_empty_header_reduction_from_sampled_conflict_and_zero_bounds:
  fixes R C Z :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> R"
    and conflict_bound:
    "wp_event verify_monad
      (trace_fri_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
    "wp_event verify_monad
      (trace_fri_zero_round_final_obstruction s) s \<le> Z"
    and total_bound:
    "R + (C + Z) \<le> trace_fri_error"
  shows "trace_fri_empty_header_reduction s"
proof (rule
    trace_fri_empty_header_reduction_from_sampled_and_assignment_obstruction_bounds)
  show "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> R"
    by (rule sampled_bound)
  show "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction s) s \<le> C + Z"
    by (rule
        wp_trace_fri_sampled_layer_assignment_obstruction_bound_from_conflict_and_zero
        [OF conflict_bound zero_bound])
  show "R + (C + Z) \<le> trace_fri_error"
    by (rule total_bound)
qed

lemma trace_fri_header_tied_reduction_from_augmented_conflict_zero_merkle_bounds:
  fixes A C Z M :: prob
  assumes augmented_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_partial_candidate s) s
      \<le> A"
    and conflict_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
    and merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and total_bound:
    "A + ((C + Z) + M) \<le> trace_fri_error"
  shows "trace_fri_header_tied_reduction s"
proof -
  have missing_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_recorded_sibling_candidate_missing s) s
      \<le> C + Z"
    by (rule
        wp_trace_fri_header_tied_recorded_sibling_candidate_missing_bound_from_conflict_and_zero)
      (rule conflict_bound, rule zero_bound)
  show ?thesis
    by (rule
        trace_fri_header_tied_reduction_from_augmented_and_recorded_missing_bounds
        [OF augmented_bound missing_bound merkle_bound total_bound])
qed

lemma active_fri_reductions_for_from_trace_augmented_composition_sampled_and_empty:
  fixes TraceAug TraceMissing TraceMerkle CompSampled CompMerkle ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes trace_augmented_bound:
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
    and empty_trace:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_empty_header_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows "active_fri_reductions_for A"
proof (rule active_fri_reductions_for_from_component_reductions)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "trace_fri_header_tied_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
  proof -
    let ?s =
      "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
    have aug:
      "wp_event verify_monad
        (trace_fri_bad_with_header_tied_augmented_partial_candidate ?s)
        ?s \<le> TraceAug data attacker_state"
      by (rule trace_augmented_bound[OF support])
    have missing:
      "wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing ?s)
        ?s \<le> TraceMissing data attacker_state"
      by (rule trace_missing_bound[OF support])
    have merkle:
      "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
        \<le> TraceMerkle data attacker_state"
      by (rule trace_merkle_bound[OF support])
    have total:
      "TraceAug data attacker_state +
        (TraceMissing data attacker_state + TraceMerkle data attacker_state)
        \<le> trace_fri_error"
      by (rule trace_total[OF support])
    show ?thesis
      by (rule
          trace_fri_header_tied_reduction_from_augmented_and_recorded_missing_bounds
          [OF aug missing merkle total])
  qed
  show "composition_fri_verifier_tied_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    by (rule active_composition_fri_verifier_tied_reductions_from_sampled_and_merkle_bounds
        [OF composition_sampled_bound composition_merkle_bound
          composition_total support])
  show "trace_fri_empty_header_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    by (rule empty_trace[OF support])
qed

lemma active_fri_reductions_for_from_trace_augmented_composition_sampled_and_empty_sampled:
  fixes TraceAug TraceMissing TraceMerkle CompSampled CompMerkle EmptySampled EmptyMissing ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes trace_augmented_bound:
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
  shows "active_fri_reductions_for A"
proof (rule active_fri_reductions_for_from_trace_augmented_composition_sampled_and_empty)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_partial_candidate ?s) ?s
      \<le> TraceAug data attacker_state"
    by (rule trace_augmented_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_recorded_sibling_candidate_missing ?s) ?s
      \<le> TraceMissing data attacker_state"
    by (rule trace_missing_bound[OF support])
  show "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
      \<le> TraceMerkle data attacker_state"
    by (rule trace_merkle_bound[OF support])
  show "TraceAug data attacker_state +
      (TraceMissing data attacker_state + TraceMerkle data attacker_state)
      \<le> trace_fri_error"
    by (rule trace_total[OF support])
  show "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain ?s) ?s
      \<le> CompSampled data attacker_state"
    by (rule composition_sampled_bound[OF support])
  show "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
      \<le> CompMerkle data attacker_state"
    by (rule composition_merkle_bound[OF support])
  show "CompSampled data attacker_state +
      (((CompMerkle data attacker_state + 0) +
        (CompMerkle data attacker_state + 0) +
        (CompMerkle data attacker_state + 0) +
        (CompMerkle data attacker_state + 0 + 0) +
        CompMerkle data attacker_state) + 0)
      \<le> composition_fri_error"
    by (rule composition_total[OF support])
  show "trace_fri_empty_header_reduction ?s"
    by (rule trace_fri_empty_header_reduction_from_sampled_and_missing_bounds
        [OF empty_sampled_bound[OF support]
          empty_missing_bound[OF support] empty_total[OF support]])
qed

lemma active_fri_reductions_for_from_trace_augmented_composition_sampled_and_empty_assignment:
  fixes TraceAug TraceMissing TraceMerkle CompSampled CompMerkle EmptySampled EmptyObstruction ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes trace_augmented_bound:
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
    and empty_obstruction_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_layer_assignment_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      EmptyObstruction data attacker_state"
    and empty_total:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      EmptySampled data attacker_state + EmptyObstruction data attacker_state
      \<le> trace_fri_error"
  shows "active_fri_reductions_for A"
proof (rule active_fri_reductions_for_from_trace_augmented_composition_sampled_and_empty)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_partial_candidate ?s) ?s
      \<le> TraceAug data attacker_state"
    by (rule trace_augmented_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_recorded_sibling_candidate_missing ?s) ?s
      \<le> TraceMissing data attacker_state"
    by (rule trace_missing_bound[OF support])
  show "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
      \<le> TraceMerkle data attacker_state"
    by (rule trace_merkle_bound[OF support])
  show "TraceAug data attacker_state +
      (TraceMissing data attacker_state + TraceMerkle data attacker_state)
      \<le> trace_fri_error"
    by (rule trace_total[OF support])
  show "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain ?s) ?s
      \<le> CompSampled data attacker_state"
    by (rule composition_sampled_bound[OF support])
  show "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
      \<le> CompMerkle data attacker_state"
    by (rule composition_merkle_bound[OF support])
  show "CompSampled data attacker_state +
      (((CompMerkle data attacker_state + 0) +
        (CompMerkle data attacker_state + 0) +
        (CompMerkle data attacker_state + 0) +
        (CompMerkle data attacker_state + 0 + 0) +
        CompMerkle data attacker_state) + 0)
      \<le> composition_fri_error"
    by (rule composition_total[OF support])
  show "trace_fri_empty_header_reduction ?s"
    by (rule
        trace_fri_empty_header_reduction_from_sampled_and_assignment_obstruction_bounds
        [OF empty_sampled_bound[OF support]
          empty_obstruction_bound[OF support] empty_total[OF support]])
qed

lemma active_fri_reductions_for_from_trace_augmented_composition_sampled_and_empty_conflict_zero:
  fixes TraceAug TraceMissing TraceMerkle CompSampled CompMerkle EmptySampled EmptyConflict EmptyZero ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes trace_augmented_bound:
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
  shows "active_fri_reductions_for A"
proof (rule active_fri_reductions_for_from_trace_augmented_composition_sampled_and_empty_assignment
    [where EmptyObstruction =
      "\<lambda>data attacker_state.
        EmptyConflict data attacker_state + EmptyZero data attacker_state"])
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_partial_candidate ?s) ?s
      \<le> TraceAug data attacker_state"
    by (rule trace_augmented_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_recorded_sibling_candidate_missing ?s) ?s
      \<le> TraceMissing data attacker_state"
    by (rule trace_missing_bound[OF support])
  show "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
      \<le> TraceMerkle data attacker_state"
    by (rule trace_merkle_bound[OF support])
  show "TraceAug data attacker_state +
      (TraceMissing data attacker_state + TraceMerkle data attacker_state)
      \<le> trace_fri_error"
    by (rule trace_total[OF support])
  show "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain ?s) ?s
      \<le> CompSampled data attacker_state"
    by (rule composition_sampled_bound[OF support])
  show "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
      \<le> CompMerkle data attacker_state"
    by (rule composition_merkle_bound[OF support])
  show "CompSampled data attacker_state +
      (((CompMerkle data attacker_state + 0) +
        (CompMerkle data attacker_state + 0) +
        (CompMerkle data attacker_state + 0) +
        (CompMerkle data attacker_state + 0 + 0) +
        CompMerkle data attacker_state) + 0)
      \<le> composition_fri_error"
    by (rule composition_total[OF support])
  show "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain ?s) ?s
      \<le> EmptySampled data attacker_state"
    by (rule empty_sampled_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction ?s) ?s
      \<le> EmptyConflict data attacker_state + EmptyZero data attacker_state"
    by (rule
        wp_trace_fri_sampled_layer_assignment_obstruction_bound_from_conflict_and_zero)
      (rule empty_conflict_bound[OF support],
        rule empty_zero_bound[OF support])
  show "EmptySampled data attacker_state +
      (EmptyConflict data attacker_state + EmptyZero data attacker_state)
      \<le> trace_fri_error"
    by (rule empty_total[OF support])
qed

lemma active_fri_reductions_for_from_trace_augmented_conflict_zero_composition_sampled_and_empty_conflict_zero:
  fixes TraceAug TraceConflict TraceZero TraceMerkle CompSampled CompMerkle
    EmptySampled EmptyConflict EmptyZero ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes trace_augmented_bound:
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
  shows "active_fri_reductions_for A"
proof (rule active_fri_reductions_for_from_component_reductions)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "trace_fri_header_tied_reduction ?s"
    by (rule
        trace_fri_header_tied_reduction_from_augmented_conflict_zero_merkle_bounds)
      (rule trace_augmented_bound[OF support],
       rule trace_conflict_bound[OF support],
       rule trace_zero_bound[OF support],
       rule trace_merkle_bound[OF support],
       rule trace_total[OF support])
  show "composition_fri_verifier_tied_reduction ?s"
    by (rule active_composition_fri_verifier_tied_reductions_from_sampled_and_merkle_bounds
        [OF composition_sampled_bound composition_merkle_bound
          composition_total support])
  show "trace_fri_empty_header_reduction ?s"
    by (rule trace_fri_empty_header_reduction_from_sampled_conflict_and_zero_bounds)
      (rule empty_sampled_bound[OF support],
       rule empty_conflict_bound[OF support],
       rule empty_zero_bound[OF support],
       rule empty_total[OF support])
qed

lemma active_fri_reductions_for_from_trace_augmented_composition_canonical_and_empty_conflict_zero:
  fixes TraceAug TraceMissing TraceMerkle CompCanonical CompMerkle EmptyCanonical EmptyConflict EmptyZero ::
    "'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob"
  assumes trace_augmented_bound:
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
  shows "active_fri_reductions_for A"
proof (rule
    active_fri_reductions_for_from_trace_augmented_composition_sampled_and_empty_conflict_zero)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_partial_candidate ?s) ?s
      \<le> TraceAug data attacker_state"
    by (rule trace_augmented_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_recorded_sibling_candidate_missing ?s) ?s
      \<le> TraceMissing data attacker_state"
    by (rule trace_missing_bound[OF support])
  show "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
      \<le> TraceMerkle data attacker_state"
    by (rule trace_merkle_bound[OF support])
  show "TraceAug data attacker_state +
      (TraceMissing data attacker_state + TraceMerkle data attacker_state)
      \<le> trace_fri_error"
    by (rule trace_total[OF support])
  show "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain ?s) ?s
      \<le> CompCanonical data attacker_state"
    by (rule
        wp_composition_fri_verifier_tied_sampled_layer_chain_bound_from_sampled)
      (rule wp_composition_fri_sampled_bound_from_canonical,
        rule composition_canonical_bound[OF support])
  show "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
      \<le> CompMerkle data attacker_state"
    by (rule composition_merkle_bound[OF support])
  show "CompCanonical data attacker_state +
      (((CompMerkle data attacker_state + 0) +
        (CompMerkle data attacker_state + 0) +
        (CompMerkle data attacker_state + 0) +
        (CompMerkle data attacker_state + 0 + 0) +
        CompMerkle data attacker_state) + 0)
      \<le> composition_fri_error"
    by (rule composition_total[OF support])
  show "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain ?s) ?s
      \<le> EmptyCanonical data attacker_state"
    by (rule wp_trace_fri_sampled_bound_from_canonical)
      (rule empty_canonical_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_sampled_assignment_conflict ?s) ?s
      \<le> EmptyConflict data attacker_state"
    by (rule empty_conflict_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_zero_round_final_obstruction ?s) ?s
      \<le> EmptyZero data attacker_state"
    by (rule empty_zero_bound[OF support])
  show "EmptyCanonical data attacker_state +
      (EmptyConflict data attacker_state + EmptyZero data attacker_state)
      \<le> trace_fri_error"
    by (rule empty_total[OF support])
qed

end

end
