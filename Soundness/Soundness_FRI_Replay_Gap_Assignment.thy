(*  Title:      Stark/Soundness_FRI_Replay_Gap_Assignment.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Replay_Gap_Assignment
  imports
    Soundness_FRI_Trace_Untied_Active
begin

text \<open>
  Small adapters from the replay-gap residual predicates to the existing
  sampled-assignment conflict branches.  The replay gaps are represented as
  sampled next, successor, or final conflicts, so they are charged to the same
  FRI sampled-assignment layer rather than treated as independent
  probabilistic obligations.
\<close>

context soundness
begin

lemma trace_fri_header_tied_next_value_replay_gap_imp_without_same:
  assumes "trace_fri_header_tied_next_value_replay_gap s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding trace_fri_header_tied_next_value_replay_gap_def
  by (blast intro: trace_fri_header_tied_without_sameI_next)

lemma trace_fri_header_tied_successor_replay_gap_imp_without_same:
  assumes "trace_fri_header_tied_successor_replay_gap s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding trace_fri_header_tied_successor_replay_gap_def
  by (blast intro: trace_fri_header_tied_without_sameI_successor)

lemma trace_fri_header_tied_final_value_replay_gap_imp_without_same:
  assumes "trace_fri_header_tied_final_value_replay_gap s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding trace_fri_header_tied_final_value_replay_gap_def
  by (blast intro: trace_fri_header_tied_without_sameI_final)

lemma trace_fri_header_tied_without_same_imp_sampled_assignment_conflict:
  assumes
    "trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
      s out"
  shows "trace_fri_header_tied_sampled_assignment_conflict s out"
  using assms
  unfolding
    trace_fri_header_tied_sampled_assignment_conflict_without_same_layer_def
    trace_fri_header_tied_sampled_assignment_conflict_def
    generic_fri_sampled_assignment_conflict_without_same_layer_def
    generic_fri_sampled_assignment_conflict_def
  by blast

lemma wp_trace_fri_header_tied_next_value_replay_gap_bound_from_without_same:
  fixes C :: prob
  assumes conflict_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
        s) s \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le> C"
  by (rule order_trans[OF _ conflict_bound])
    (rule wp_event_mono,
      rule trace_fri_header_tied_next_value_replay_gap_imp_without_same)

lemma wp_trace_fri_header_tied_successor_replay_gap_bound_from_without_same:
  fixes C :: prob
  assumes conflict_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
        s) s \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le> C"
  by (rule order_trans[OF _ conflict_bound])
    (rule wp_event_mono,
      rule trace_fri_header_tied_successor_replay_gap_imp_without_same)

lemma wp_trace_fri_header_tied_final_value_replay_gap_bound_from_without_same:
  fixes C :: prob
  assumes conflict_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
        s) s \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_replay_gap s) s \<le> C"
  by (rule order_trans[OF _ conflict_bound])
    (rule wp_event_mono,
      rule trace_fri_header_tied_final_value_replay_gap_imp_without_same)

lemma wp_trace_fri_header_tied_without_same_bound_from_sampled_assignment_conflict:
  fixes C :: prob
  assumes conflict_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
        s) s \<le> C"
  by (rule order_trans[OF _ conflict_bound])
    (rule wp_event_mono,
      rule trace_fri_header_tied_without_same_imp_sampled_assignment_conflict)

lemma composition_fri_verifier_tied_next_value_replay_gap_imp_without_same:
  assumes "composition_fri_verifier_tied_next_value_replay_gap s out"
  shows
    "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding composition_fri_verifier_tied_next_value_replay_gap_def
  by (blast intro: composition_fri_verifier_tied_without_sameI_next)

lemma composition_fri_verifier_tied_successor_replay_gap_imp_without_same:
  assumes "composition_fri_verifier_tied_successor_replay_gap s out"
  shows
    "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding composition_fri_verifier_tied_successor_replay_gap_def
  by (blast intro: composition_fri_verifier_tied_without_sameI_successor)

lemma composition_fri_verifier_tied_final_value_replay_gap_imp_without_same:
  assumes "composition_fri_verifier_tied_final_value_replay_gap s out"
  shows
    "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out"
  using assms
  unfolding composition_fri_verifier_tied_final_value_replay_gap_def
  by (blast intro: composition_fri_verifier_tied_without_sameI_final)

lemma composition_fri_verifier_tied_without_same_imp_sampled_assignment_conflict:
  assumes
    "composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
      s out"
  shows "composition_fri_verifier_tied_sampled_assignment_conflict s out"
  using assms
  unfolding
    composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer_def
    composition_fri_verifier_tied_sampled_assignment_conflict_def
    generic_fri_sampled_assignment_conflict_without_same_layer_def
    generic_fri_sampled_assignment_conflict_def
  by blast

lemma wp_composition_fri_verifier_tied_next_value_replay_gap_bound_from_without_same:
  fixes C :: prob
  assumes conflict_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
        s) s \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_next_value_replay_gap s) s \<le> C"
  by (rule order_trans[OF _ conflict_bound])
    (rule wp_event_mono,
      rule composition_fri_verifier_tied_next_value_replay_gap_imp_without_same)

lemma wp_composition_fri_verifier_tied_successor_replay_gap_bound_from_without_same:
  fixes C :: prob
  assumes conflict_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
        s) s \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_successor_replay_gap s) s \<le> C"
  by (rule order_trans[OF _ conflict_bound])
    (rule wp_event_mono,
      rule composition_fri_verifier_tied_successor_replay_gap_imp_without_same)

lemma wp_composition_fri_verifier_tied_final_value_replay_gap_bound_from_without_same:
  fixes C :: prob
  assumes conflict_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
        s) s \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap s) s \<le> C"
  by (rule order_trans[OF _ conflict_bound])
    (rule wp_event_mono,
      rule composition_fri_verifier_tied_final_value_replay_gap_imp_without_same)

lemma wp_composition_fri_verifier_tied_without_same_bound_from_sampled_assignment_conflict:
  fixes C :: prob
  assumes conflict_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
        s) s \<le> C"
  by (rule order_trans[OF _ conflict_bound])
    (rule wp_event_mono,
      rule composition_fri_verifier_tied_without_same_imp_sampled_assignment_conflict)

lemma trace_fri_header_tied_residual_obligations_from_without_same_bounds:
  fixes C :: prob
  assumes sampled:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> r_b"
    and zero:
    "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> z_b"
    and merkle:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    and structural:
    "wp_event verify_monad
      (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> h_b"
    and without_same:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
        s) s \<le> C"
    and total:
    "r_b + (((((p_b + h_b) + p_b) + C + C +
      (p_b + 0 + 0)) + p_b) + 0 + z_b)
      \<le> trace_fri_error"
  shows
    "trace_fri_header_tied_residual_obligations s
      r_b z_b 0 p_b h_b p_b C C 0"
  by (rule
      trace_fri_header_tied_residual_obligations_from_bounds_without_head_slot_and_selected_zero)
    (rule sampled, rule zero, rule merkle, rule structural,
     rule wp_trace_fri_header_tied_next_value_replay_gap_bound_from_without_same
      [OF without_same],
     rule wp_trace_fri_header_tied_successor_replay_gap_bound_from_without_same
      [OF without_same],
     rule total)

lemma composition_fri_verifier_tied_residual_obligations_from_without_same_bounds:
  fixes C :: prob
  assumes sampled:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s
      \<le> r_b"
    and merkle:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    and without_same:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
        s) s \<le> C"
    and total:
    "r_b + (((p_b + 0) + C + C + C + p_b) + 0)
      \<le> composition_fri_error"
  shows
    "composition_fri_verifier_tied_residual_obligations s r_b 0 p_b C C C"
  by (rule composition_fri_verifier_tied_residual_obligations_from_bounds_slot_zero)
    (rule sampled, rule merkle,
     rule wp_composition_fri_verifier_tied_next_value_replay_gap_bound_from_without_same
      [OF without_same],
     rule wp_composition_fri_verifier_tied_successor_replay_gap_bound_from_without_same
      [OF without_same],
     rule wp_composition_fri_verifier_tied_final_value_replay_gap_bound_from_without_same
      [OF without_same],
     rule total)

lemma active_trace_fri_residual_obligations_from_without_same_bounds:
  fixes
    Rt Zt Pt Ht Ct ::
      "('f staged_proof_data \<Rightarrow>
        'f protocol_channel \<Rightarrow> prob)"
  assumes trace_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Rt data attacker_state"
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
          (staged_proof_transcript data)) \<le>
      Zt data attacker_state"
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
          (staged_proof_transcript data)) \<le>
      Pt data attacker_state"
    and trace_structural_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ht data attacker_state"
    and trace_without_same_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ct data attacker_state"
    and trace_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rt data attacker_state +
        (((((Pt data attacker_state + Ht data attacker_state) +
            Pt data attacker_state) +
           Ct data attacker_state + Ct data attacker_state +
           (Pt data attacker_state + 0 + 0)) +
          Pt data attacker_state) +
         0 + Zt data attacker_state)
      \<le> trace_fri_error"
  shows "active_trace_fri_residual_obligations_for A Rt Zt
    (\<lambda>_ _. (0::prob)) Pt Ht Pt Ct Ct (\<lambda>_ _. (0::prob))"
  unfolding active_trace_fri_residual_obligations_for_def
proof (intro allI impI)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "trace_fri_header_tied_residual_obligations ?s
      (Rt data attacker_state) (Zt data attacker_state) 0
      (Pt data attacker_state) (Ht data attacker_state)
      (Pt data attacker_state) (Ct data attacker_state)
      (Ct data attacker_state) 0"
    by (rule trace_fri_header_tied_residual_obligations_from_without_same_bounds)
      (rule trace_sampled_bound[OF support],
       rule trace_zero_bound[OF support],
       rule trace_merkle_bound[OF support],
       rule trace_structural_bound[OF support],
       rule trace_without_same_bound[OF support],
       rule trace_total_bound[OF support])
qed

lemma active_composition_fri_residual_obligations_from_without_same_bounds:
  fixes
    Rc Pc Cc ::
      "('f staged_proof_data \<Rightarrow>
        'f protocol_channel \<Rightarrow> prob)"
  assumes comp_sampled_bound:
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
      Rc data attacker_state"
    and comp_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Pc data attacker_state"
    and comp_without_same_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Cc data attacker_state"
    and comp_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rc data attacker_state +
        (((Pc data attacker_state + 0) +
          Cc data attacker_state + Cc data attacker_state +
          Cc data attacker_state + Pc data attacker_state) +
         0)
      \<le> composition_fri_error"
  shows "active_composition_fri_residual_obligations_for A Rc
    (\<lambda>_ _. (0::prob)) Pc Cc Cc Cc"
  unfolding active_composition_fri_residual_obligations_for_def
proof (intro allI impI)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "composition_fri_verifier_tied_residual_obligations ?s
      (Rc data attacker_state) 0 (Pc data attacker_state)
      (Cc data attacker_state) (Cc data attacker_state)
      (Cc data attacker_state)"
    by (rule composition_fri_verifier_tied_residual_obligations_from_without_same_bounds)
      (rule comp_sampled_bound[OF support],
       rule comp_merkle_bound[OF support],
       rule comp_without_same_bound[OF support],
       rule comp_total_bound[OF support])
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_header_without_same_and_untied:
  fixes R Z P H C Q U :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and zero_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
    and header_partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and without_same_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
          s) s \<le> C"
    and gap_partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> Q"
    and untied_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
        s \<le> U"
    and total_bound:
      "R + (((((P + H) + P) + C + C + C) + P) + 0 + Z) +
        (Q + U) \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have head_neq:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap s) s \<le> P"
    by (rule
        wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle
        [OF header_partial_merkle_bound])
  have head_mismatch:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_mismatch_gap s) s \<le> P"
    by (rule
        wp_trace_fri_header_tied_base_head_value_mismatch_gap_bound_from_neq_gap
        [OF head_neq])
  have alignment:
    "wp_event verify_monad
      (trace_fri_header_tied_base_value_alignment_gap s) s \<le> P"
    by (rule
        wp_trace_fri_header_tied_base_value_alignment_gap_bound_from_head_value_mismatch_gap
        [OF head_mismatch])
  have next_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le> C"
    by (rule
        wp_trace_fri_header_tied_next_value_replay_gap_bound_from_without_same
        [OF without_same_bound])
  have successor_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le> C"
    by (rule
        wp_trace_fri_header_tied_successor_replay_gap_bound_from_without_same
        [OF without_same_bound])
  have final_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_replay_gap s) s \<le> C"
    by (rule
        wp_trace_fri_header_tied_final_value_replay_gap_bound_from_without_same
        [OF without_same_bound])
  have header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
      R + (((((P + H) + P) + C + C + C) + P) + 0 + Z)"
    by (rule
        wp_trace_fri_header_tied_bound_from_sampled_zero_slot_recorded_chunk_gap_and_residuals)
      (rule sampled_bound, rule zero_bound,
       rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero,
       rule header_partial_merkle_bound, rule structural_gap_bound,
       rule alignment, rule next_bound, rule successor_bound,
       rule final_bound)
  show ?thesis
    by (rule
        trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied)
      (rule header_bound, rule gap_partial_merkle_bound,
       rule untied_bound, rule total_bound)
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_header_without_same_hash_root_query:
  fixes R Z P H C Q K Rt Qt :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
    and zero_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
    and header_partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and structural_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> H"
    and without_same_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
          s) s \<le> C"
    and gap_partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> Q"
    and hash_bound:
      "wp_event verify_monad (hash_map_output_collision_bad s) s \<le> K"
    and root_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_root_gap s) s \<le> Rt"
    and query_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_query_gap s) s \<le> Qt"
    and total_bound:
      "R + (((((P + H) + P) + C + C + C) + P) + 0 + Z) +
        (Q + (K + (Rt + Qt))) \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have head_neq:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap s) s \<le> P"
    by (rule
        wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle
        [OF header_partial_merkle_bound])
  have head_mismatch:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_mismatch_gap s) s \<le> P"
    by (rule
        wp_trace_fri_header_tied_base_head_value_mismatch_gap_bound_from_neq_gap
        [OF head_neq])
  have alignment:
    "wp_event verify_monad
      (trace_fri_header_tied_base_value_alignment_gap s) s \<le> P"
    by (rule
        wp_trace_fri_header_tied_base_value_alignment_gap_bound_from_head_value_mismatch_gap
        [OF head_mismatch])
  have next_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le> C"
    by (rule
        wp_trace_fri_header_tied_next_value_replay_gap_bound_from_without_same
        [OF without_same_bound])
  have successor_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le> C"
    by (rule
        wp_trace_fri_header_tied_successor_replay_gap_bound_from_without_same
        [OF without_same_bound])
  have final_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_replay_gap s) s \<le> C"
    by (rule
        wp_trace_fri_header_tied_final_value_replay_gap_bound_from_without_same
        [OF without_same_bound])
  have header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
      R + (((((P + H) + P) + C + C + C) + P) + 0 + Z)"
    by (rule
        wp_trace_fri_header_tied_bound_from_sampled_zero_slot_recorded_chunk_gap_and_residuals)
      (rule sampled_bound, rule zero_bound,
       rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero,
       rule header_partial_merkle_bound, rule structural_gap_bound,
       rule alignment, rule next_bound, rule successor_bound,
       rule final_bound)
  show ?thesis
    by (rule
        trace_fri_reachable_partial_candidate_reduction_from_header_merkle_hash_root_query)
      (rule header_bound, rule gap_partial_merkle_bound, rule hash_bound,
       rule root_bound, rule query_bound, rule total_bound)
qed

lemma active_trace_fri_reachable_reduction_from_header_without_same_and_untied:
  fixes Rt Zt Pt Ht Ct Qt Ut ::
    "('f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob)"
  assumes trace_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Rt data attacker_state"
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
          (staged_proof_transcript data)) \<le>
      Zt data attacker_state"
    and trace_header_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Pt data attacker_state"
    and trace_structural_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ht data attacker_state"
    and trace_without_same_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ct data attacker_state"
    and trace_gap_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Qt data attacker_state"
    and trace_untied_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ut data attacker_state"
    and trace_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rt data attacker_state +
        (((((Pt data attacker_state + Ht data attacker_state) +
            Pt data attacker_state) +
           Ct data attacker_state + Ct data attacker_state +
           Ct data attacker_state) +
          Pt data attacker_state) +
         0 + Zt data attacker_state) +
        (Qt data attacker_state + Ut data attacker_state)
      \<le> trace_fri_error"
    and support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  shows
    "trace_fri_reachable_partial_candidate_reduction_assumption
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
  by (rule
        trace_fri_reachable_partial_candidate_reduction_from_header_without_same_and_untied)
    (rule trace_sampled_bound[OF support],
     rule trace_zero_bound[OF support],
     rule trace_header_merkle_bound[OF support],
     rule trace_structural_bound[OF support],
     rule trace_without_same_bound[OF support],
     rule trace_gap_merkle_bound[OF support],
     rule trace_untied_bound[OF support],
     rule trace_total_bound[OF support])

lemma active_trace_fri_reachable_reduction_from_header_without_same_hash_root_query:
  fixes Rt Zt Pt Ht Ct Qt Kt Ut Vt ::
    "('f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob)"
  assumes trace_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Rt data attacker_state"
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
          (staged_proof_transcript data)) \<le>
      Zt data attacker_state"
    and trace_header_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Pt data attacker_state"
    and trace_structural_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ht data attacker_state"
    and trace_without_same_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ct data attacker_state"
    and trace_gap_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Qt data attacker_state"
    and trace_hash_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (hash_map_output_collision_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Kt data attacker_state"
    and trace_root_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_root_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ut data attacker_state"
    and trace_query_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_query_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Vt data attacker_state"
    and trace_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rt data attacker_state +
        (((((Pt data attacker_state + Ht data attacker_state) +
            Pt data attacker_state) +
           Ct data attacker_state + Ct data attacker_state +
           Ct data attacker_state) +
          Pt data attacker_state) +
         0 + Zt data attacker_state) +
        (Qt data attacker_state +
          (Kt data attacker_state +
            (Ut data attacker_state + Vt data attacker_state)))
      \<le> trace_fri_error"
    and support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  shows
    "trace_fri_reachable_partial_candidate_reduction_assumption
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
  by (rule
      trace_fri_reachable_partial_candidate_reduction_from_header_without_same_hash_root_query)
    (rule trace_sampled_bound[OF support],
     rule trace_zero_bound[OF support],
     rule trace_header_merkle_bound[OF support],
     rule trace_structural_bound[OF support],
     rule trace_without_same_bound[OF support],
     rule trace_gap_merkle_bound[OF support],
     rule trace_hash_bound[OF support],
     rule trace_root_bound[OF support],
     rule trace_query_bound[OF support],
     rule trace_total_bound[OF support])

lemma composition_fri_reachable_partial_candidate_reduction_from_split_without_same_bounds:
  fixes R P C E Q T :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and verifier_partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and without_same_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
          s) s \<le> C"
    and empty_bound:
      "wp_event verify_monad
        (composition_fri_reachable_verifier_tie_empty_header_gap s) s \<le> E"
    and gap_partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> Q"
    and candidate_available_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_candidate_available_gap s) s \<le> T"
    and total_bound:
      "R + (((P + 0) + C + C + C + P) + 0) + (E + (Q + T))
        \<le> composition_fri_error"
  shows "composition_fri_reachable_partial_candidate_reduction_assumption s"
  by (rule
      composition_fri_reachable_partial_candidate_reduction_from_split_residual_bounds_with_candidate_available_and_recorded_missing_zero)
    (rule sampled_bound,
     rule wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero,
     rule verifier_partial_merkle_bound,
     rule wp_composition_fri_verifier_tied_next_value_replay_gap_bound_from_without_same
      [OF without_same_bound],
     rule wp_composition_fri_verifier_tied_successor_replay_gap_bound_from_without_same
      [OF without_same_bound],
     rule wp_composition_fri_verifier_tied_final_value_replay_gap_bound_from_without_same
      [OF without_same_bound],
     rule empty_bound,
     rule gap_partial_merkle_bound,
     rule candidate_available_bound,
     rule total_bound)

lemma composition_fri_reachable_partial_candidate_reduction_from_split_sampled_assignment_bounds:
  fixes R P C E Q T :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and verifier_partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and sampled_assignment_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict s) s
        \<le> C"
    and empty_bound:
      "wp_event verify_monad
        (composition_fri_reachable_verifier_tie_empty_header_gap s) s \<le> E"
    and gap_partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> Q"
    and candidate_available_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_candidate_available_gap s) s \<le> T"
    and total_bound:
      "R + (((P + 0) + C + C + C + P) + 0) + (E + (Q + T))
        \<le> composition_fri_error"
  shows "composition_fri_reachable_partial_candidate_reduction_assumption s"
  by (rule
      composition_fri_reachable_partial_candidate_reduction_from_split_without_same_bounds)
    (rule sampled_bound,
     rule verifier_partial_merkle_bound,
     rule wp_composition_fri_verifier_tied_without_same_bound_from_sampled_assignment_conflict
      [OF sampled_assignment_bound],
     rule empty_bound,
     rule gap_partial_merkle_bound,
     rule candidate_available_bound,
     rule total_bound)

lemma active_composition_fri_reachable_reduction_from_split_without_same_bounds:
  fixes Rc Pc Cc Ec Qc Tc ::
    "('f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob)"
  assumes comp_sampled_bound:
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
      Rc data attacker_state"
    and comp_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Pc data attacker_state"
    and comp_without_same_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Cc data attacker_state"
    and comp_empty_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_reachable_verifier_tie_empty_header_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ec data attacker_state"
    and comp_gap_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Qc data attacker_state"
    and comp_candidate_available_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_candidate_available_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Tc data attacker_state"
    and comp_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rc data attacker_state +
        (((Pc data attacker_state + 0) +
          Cc data attacker_state + Cc data attacker_state +
          Cc data attacker_state + Pc data attacker_state) +
         0) +
        (Ec data attacker_state +
          (Qc data attacker_state + Tc data attacker_state))
      \<le> composition_fri_error"
    and support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  shows
    "composition_fri_reachable_partial_candidate_reduction_assumption
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
  by (rule
      composition_fri_reachable_partial_candidate_reduction_from_split_without_same_bounds)
    (rule comp_sampled_bound[OF support],
     rule comp_merkle_bound[OF support],
     rule comp_without_same_bound[OF support],
     rule comp_empty_bound[OF support],
     rule comp_gap_merkle_bound[OF support],
     rule comp_candidate_available_bound[OF support],
     rule comp_total_bound[OF support])

lemma active_fri_reductions_from_without_same_and_untied_bounds:
  fixes
    Rt Zt Pt Ht Ct Qt Ut Rc Pc Cc Ec Qc Tc ::
      "('f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob)"
  assumes trace_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Rt data attacker_state"
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
          (staged_proof_transcript data)) \<le>
      Zt data attacker_state"
    and trace_header_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Pt data attacker_state"
    and trace_structural_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ht data attacker_state"
    and trace_without_same_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ct data attacker_state"
    and trace_gap_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Qt data attacker_state"
    and trace_untied_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ut data attacker_state"
    and trace_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rt data attacker_state +
        (((((Pt data attacker_state + Ht data attacker_state) +
            Pt data attacker_state) +
           Ct data attacker_state + Ct data attacker_state +
           Ct data attacker_state) +
          Pt data attacker_state) +
         0 + Zt data attacker_state) +
        (Qt data attacker_state + Ut data attacker_state)
      \<le> trace_fri_error"
    and comp_sampled_bound:
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
      Rc data attacker_state"
    and comp_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Pc data attacker_state"
    and comp_without_same_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Cc data attacker_state"
    and comp_empty_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_reachable_verifier_tie_empty_header_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ec data attacker_state"
    and comp_gap_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Qc data attacker_state"
    and comp_candidate_available_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_candidate_available_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Tc data attacker_state"
    and comp_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rc data attacker_state +
        (((Pc data attacker_state + 0) +
          Cc data attacker_state + Cc data attacker_state +
          Cc data attacker_state + Pc data attacker_state) +
         0) +
        (Ec data attacker_state +
          (Qc data attacker_state + Tc data attacker_state))
      \<le> composition_fri_error"
  shows "active_fri_reductions_for A"
proof (rule active_fri_reductions_from_reachable)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  have total:
    "Rt data attacker_state +
      (Pt data attacker_state + Ht data attacker_state +
       Pt data attacker_state +
       Ct data attacker_state +
       Ct data attacker_state +
       Ct data attacker_state +
       Pt data attacker_state +
       0 +
       Zt data attacker_state) +
      (Qt data attacker_state + Ut data attacker_state)
      \<le> trace_fri_error"
    using trace_total_bound[OF support] by (simp add: add.assoc)
  show "trace_fri_reachable_partial_candidate_reduction_assumption
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    using trace_sampled_bound[OF support]
      trace_zero_bound[OF support]
      trace_header_merkle_bound[OF support]
      trace_structural_bound[OF support]
      trace_without_same_bound[OF support]
      trace_gap_merkle_bound[OF support]
      trace_untied_bound[OF support]
      total
    by (rule
        trace_fri_reachable_partial_candidate_reduction_from_header_without_same_and_untied
        [where R = "Rt data attacker_state"
          and Z = "Zt data attacker_state"
          and P = "Pt data attacker_state"
          and H = "Ht data attacker_state"
          and C = "Ct data attacker_state"
          and Q = "Qt data attacker_state"
          and U = "Ut data attacker_state"])
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  have total:
    "Rc data attacker_state +
      (Pc data attacker_state + 0 + Cc data attacker_state +
       Cc data attacker_state +
       Cc data attacker_state +
       Pc data attacker_state +
       0) +
      (Ec data attacker_state +
       (Qc data attacker_state + Tc data attacker_state))
      \<le> composition_fri_error"
    using comp_total_bound[OF support] by (simp add: add.assoc)
  show "composition_fri_reachable_partial_candidate_reduction_assumption
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    using comp_sampled_bound[OF support]
      comp_merkle_bound[OF support]
      comp_without_same_bound[OF support]
      comp_empty_bound[OF support]
      comp_gap_merkle_bound[OF support]
      comp_candidate_available_bound[OF support]
      total
    by (rule
        composition_fri_reachable_partial_candidate_reduction_from_split_without_same_bounds
        [where R = "Rc data attacker_state"
          and P = "Pc data attacker_state"
          and C = "Cc data attacker_state"
          and E = "Ec data attacker_state"
          and Q = "Qc data attacker_state"
          and T = "Tc data attacker_state"])
qed

lemma active_fri_reductions_from_without_same_hash_root_query_bounds:
  fixes
    Rt Zt Pt Ht Ct Qt Kt Ut Vt Rc Pc Cc Ec Qc Tc ::
      "('f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob)"
  assumes trace_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Rt data attacker_state"
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
          (staged_proof_transcript data)) \<le>
      Zt data attacker_state"
    and trace_header_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Pt data attacker_state"
    and trace_structural_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ht data attacker_state"
    and trace_without_same_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict_without_same_layer
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ct data attacker_state"
    and trace_gap_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Qt data attacker_state"
    and trace_hash_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (hash_map_output_collision_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Kt data attacker_state"
    and trace_root_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_root_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ut data attacker_state"
    and trace_query_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_query_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Vt data attacker_state"
    and trace_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rt data attacker_state +
        (((((Pt data attacker_state + Ht data attacker_state) +
            Pt data attacker_state) +
           Ct data attacker_state + Ct data attacker_state +
           Ct data attacker_state) +
          Pt data attacker_state) +
         0 + Zt data attacker_state) +
        (Qt data attacker_state +
          (Kt data attacker_state +
            (Ut data attacker_state + Vt data attacker_state)))
      \<le> trace_fri_error"
    and comp_sampled_bound:
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
      Rc data attacker_state"
    and comp_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Pc data attacker_state"
    and comp_without_same_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Cc data attacker_state"
    and comp_empty_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_reachable_verifier_tie_empty_header_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ec data attacker_state"
    and comp_gap_merkle_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (partial_merkle_inconsistency_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Qc data attacker_state"
    and comp_candidate_available_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_candidate_available_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Tc data attacker_state"
    and comp_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rc data attacker_state +
        (((Pc data attacker_state + 0) +
          Cc data attacker_state + Cc data attacker_state +
          Cc data attacker_state + Pc data attacker_state) +
         0) +
        (Ec data attacker_state +
          (Qc data attacker_state + Tc data attacker_state))
      \<le> composition_fri_error"
  shows "active_fri_reductions_for A"
  apply (rule active_fri_reductions_from_without_same_and_untied_bounds
    [where Rt = Rt and Zt = Zt and Pt = Pt and Ht = Ht and Ct = Ct
      and Qt = Qt
      and Ut =
        "\<lambda>data attacker_state.
          Kt data attacker_state +
            (Ut data attacker_state + Vt data attacker_state)"
      and Rc = Rc and Pc = Pc and Cc = Cc and Ec = Ec and Qc = Qc
      and Tc = Tc])
                apply (rule trace_sampled_bound, assumption)
               apply (rule trace_zero_bound, assumption)
              apply (rule trace_header_merkle_bound, assumption)
             apply (rule trace_structural_bound, assumption)
            apply (rule trace_without_same_bound, assumption)
           apply (rule trace_gap_merkle_bound, assumption)
          apply (rule
            wp_trace_fri_header_tied_low_candidate_untied_gap_bound_from_hash_root_query)
            apply (rule trace_hash_bound, assumption)
           apply (rule trace_root_bound, assumption)
          apply (rule trace_query_bound, assumption)
         apply (rule trace_total_bound, assumption)
        apply (rule comp_sampled_bound, assumption)
       apply (rule comp_merkle_bound, assumption)
      apply (rule comp_without_same_bound, assumption)
     apply (rule comp_empty_bound, assumption)
    apply (rule comp_gap_merkle_bound, assumption)
   apply (rule comp_candidate_available_bound, assumption)
  apply (rule comp_total_bound, assumption)
  done

end

end
