(*  Title:      Stark/Soundness_FRI_Active_Reductions.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Active_Reductions
  imports
    Soundness_FRI_Candidate_Transfer_Support
    Soundness_FRI_Empty_Header_Reduction
begin

text \<open>
  Staged packaging for the active FRI reductions used by the public route.
  This layer does not add assumptions; it names the exact verifier-local
  reductions consumed by the public-route bounds.
\<close>

text \<open>
  Internal symbolic FRI soundness interface for the public staged theorem.

  The trace side is intentionally stated in terms of the verifier-consumed
  header-tied branch and the empty-composition-header branch.  The composition
  side is stated in terms of the verifier-tied branch consumed by the active
  public route.
\<close>

locale soundness_fri = soundness +
  assumes trace_fri_active_reductions:
    "\<And>A data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_header_tied_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<and>
      trace_fri_empty_header_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  assumes composition_fri_active_reduction:
    "\<And>A data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_verifier_tied_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"

context soundness
begin

lemma active_composition_candidate_transfer_bound_from_classification_bound:
  assumes classification_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_misaligned_candidate_classification
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      T data attacker_state"
    and support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_candidate_transfer_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
      T data attacker_state"
  by (rule
      wp_composition_fri_verifier_tied_candidate_transfer_gap_bound_from_misaligned_classification)
    (rule classification_bound[OF support])

lemma active_composition_candidate_available_bound_from_transcript_consistent_classification_bound:
  assumes empty_bound:
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
      E data attacker_state"
    and merkle_bound:
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
      M data attacker_state"
    and classification_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_transcript_consistent_misaligned_classification
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      T data attacker_state"
    and support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_candidate_available_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
      E data attacker_state + (M data attacker_state +
        T data attacker_state)"
  by (rule
      wp_composition_fri_verifier_tied_candidate_available_gap_bound_from_empty_merkle_and_transcript_consistent_classification)
    (rule empty_bound[OF support], rule merkle_bound[OF support],
      rule classification_bound[OF support])

lemma active_composition_transcript_consistent_classification_bound_from_components:
  assumes false_statement: "\<not> exists_valid_trace"
    and comp_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_bad_with_partial_candidates
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      C data attacker_state"
    and trace_fri_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ft data attacker_state"
    and query_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (query_bad_with_aligned_transcript_partial_candidates
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Q data attacker_state"
    and support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_transcript_consistent_misaligned_classification
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
      C data attacker_state + Ft data attacker_state +
        Q data attacker_state"
  by (rule
      wp_composition_fri_verifier_tied_transcript_consistent_misaligned_classification_bound_from_cover_components
      [OF false_statement])
    (rule comp_bound[OF support], rule trace_fri_bound[OF support],
      rule query_bound[OF support])

lemma active_trace_fri_reachable_reduction_from_header_merkle_and_low_candidate_gap:
  fixes Ht Mt Tt ::
    "('f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow> prob)"
  assumes trace_header_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ht data attacker_state"
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
      Mt data attacker_state"
    and trace_low_gap_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Tt data attacker_state"
    and total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Ht data attacker_state +
        (Mt data attacker_state + Tt data attacker_state) \<le>
      trace_fri_error"
    and support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  shows
    "trace_fri_reachable_partial_candidate_reduction_assumption
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
  by (rule
      trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_low_candidate_gap)
    (rule trace_header_bound[OF support],
     rule trace_merkle_bound[OF support],
     rule trace_low_gap_bound[OF support],
     rule total_bound[OF support])

definition active_fri_reductions_for where
  "active_fri_reductions_for A \<longleftrightarrow>
    (\<forall>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<longrightarrow>
      trace_fri_header_tied_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<and>
      composition_fri_verifier_tied_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<and>
      trace_fri_empty_header_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))"

definition trace_fri_header_tied_residual_obligations
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      prob \<Rightarrow> prob \<Rightarrow> prob \<Rightarrow> prob \<Rightarrow> prob \<Rightarrow> prob \<Rightarrow>
      prob \<Rightarrow> prob \<Rightarrow> prob \<Rightarrow> bool"
where
  "trace_fri_header_tied_residual_obligations s r_b z_b a_b p_b h_b g_b n_b s_b f_b
    \<longleftrightarrow>
    wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> r_b \<and>
    wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> z_b \<and>
    wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s
      \<le> a_b \<and>
    wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b \<and>
    wp_event verify_monad
      (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> h_b \<and>
    wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap s) s \<le> g_b \<and>
    wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le> n_b \<and>
    wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le> s_b \<and>
    wp_event verify_monad
      (trace_fri_header_tied_final_value_selected_step_missing_gap s) s
      \<le> f_b \<and>
    r_b + (((((p_b + h_b) + g_b) + n_b + s_b +
      (p_b + a_b + f_b)) + p_b) + a_b + z_b)
      \<le> trace_fri_error"

definition composition_fri_verifier_tied_residual_obligations
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      prob \<Rightarrow> prob \<Rightarrow> prob \<Rightarrow> prob \<Rightarrow> prob \<Rightarrow>
      prob \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_residual_obligations s r_b a_b p_b n_b s_b g_b
    \<longleftrightarrow>
    wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s
      \<le> r_b \<and>
    wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> a_b \<and>
    wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b \<and>
    wp_event verify_monad
      (composition_fri_verifier_tied_next_value_replay_gap s) s \<le> n_b \<and>
    wp_event verify_monad
      (composition_fri_verifier_tied_successor_replay_gap s) s \<le> s_b \<and>
    wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap s) s \<le> g_b \<and>
    r_b + (((p_b + a_b) + n_b + s_b + g_b + p_b) + a_b)
      \<le> composition_fri_error"

lemma trace_fri_header_tied_residual_obligations_from_bounds_without_head:
  assumes sampled:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> r_b"
    and zero:
    "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> z_b"
    and slot:
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s
      \<le> a_b"
    and merkle:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    and structural:
    "wp_event verify_monad
      (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> h_b"
    and next_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le> n_b"
    and successor:
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le> s_b"
    and final_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_selected_step_missing_gap s) s
      \<le> f_b"
    and total:
    "r_b + (((((p_b + h_b) + p_b) + n_b + s_b +
      (p_b + a_b + f_b)) + p_b) + a_b + z_b)
      \<le> trace_fri_error"
  shows
    "trace_fri_header_tied_residual_obligations s
      r_b z_b a_b p_b h_b p_b n_b s_b f_b"
proof -
  have head:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap s) s \<le> p_b"
    by (rule
        wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle
        [OF merkle])
  show ?thesis
    using sampled zero slot merkle structural head next_bound successor
      final_bound total
    unfolding trace_fri_header_tied_residual_obligations_def by blast
qed

lemma trace_fri_header_tied_residual_obligations_from_bounds_without_head_and_selected_zero:
  assumes sampled:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> r_b"
    and zero:
    "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> z_b"
    and slot:
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s
      \<le> a_b"
    and merkle:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    and structural:
    "wp_event verify_monad
      (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> h_b"
    and next_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le> n_b"
    and successor:
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le> s_b"
    and total:
    "r_b + (((((p_b + h_b) + p_b) + n_b + s_b +
      (p_b + a_b + 0)) + p_b) + a_b + z_b)
      \<le> trace_fri_error"
  shows
    "trace_fri_header_tied_residual_obligations s
      r_b z_b a_b p_b h_b p_b n_b s_b 0"
  by (rule trace_fri_header_tied_residual_obligations_from_bounds_without_head)
    (rule sampled, rule zero, rule slot, rule merkle, rule structural,
     rule next_bound, rule successor,
     rule wp_trace_fri_header_tied_final_value_selected_step_missing_gap_zero,
     rule total)

lemma trace_fri_header_tied_residual_obligations_from_bounds_without_head_slot_and_selected_zero:
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
    and next_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le> n_b"
    and successor:
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le> s_b"
    and total:
    "r_b + (((((p_b + h_b) + p_b) + n_b + s_b +
      (p_b + 0 + 0)) + p_b) + 0 + z_b)
      \<le> trace_fri_error"
  shows
    "trace_fri_header_tied_residual_obligations s
      r_b z_b 0 p_b h_b p_b n_b s_b 0"
  by (rule
      trace_fri_header_tied_residual_obligations_from_bounds_without_head_and_selected_zero)
    (rule sampled, rule zero,
     rule wp_trace_fri_header_tied_authenticated_slot_recorded_chunk_gap_zero,
     rule merkle, rule structural, rule next_bound, rule successor, rule total)

lemma composition_fri_verifier_tied_residual_obligations_from_bounds:
  assumes sampled:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s
      \<le> r_b"
    and slot:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> a_b"
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
    "r_b + (((p_b + a_b) + n_b + s_b + g_b + p_b) + a_b)
      \<le> composition_fri_error"
  shows
    "composition_fri_verifier_tied_residual_obligations s
      r_b a_b p_b n_b s_b g_b"
  using sampled slot merkle next_bound successor final_bound total
  unfolding composition_fri_verifier_tied_residual_obligations_def by blast

lemma composition_fri_verifier_tied_residual_obligations_from_bounds_slot_zero:
  assumes sampled:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s
      \<le> r_b"
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
    "r_b + (((p_b + 0) + n_b + s_b + g_b + p_b) + 0)
      \<le> composition_fri_error"
  shows
    "composition_fri_verifier_tied_residual_obligations s
      r_b 0 p_b n_b s_b g_b"
  by (rule composition_fri_verifier_tied_residual_obligations_from_bounds)
    (rule sampled,
     rule wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero,
     rule merkle, rule next_bound, rule successor, rule final_bound,
     rule total)

lemma active_composition_fri_reachable_reduction_from_split_bounds_without_empty_with_candidate_available:
  fixes
    Rc Ac Pc Nc Sc Gc Qc Tc ::
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
    and comp_slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ac data attacker_state"
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
    and comp_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nc data attacker_state"
    and comp_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Sc data attacker_state"
    and comp_final_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Gc data attacker_state"
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
          Nc data attacker_state + Sc data attacker_state +
          Gc data attacker_state + Pc data attacker_state) +
         Ac data attacker_state) +
        (Qc data attacker_state + Tc data attacker_state)
      \<le> composition_fri_error"
  assumes support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  shows
    "composition_fri_reachable_partial_candidate_reduction_assumption
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show ?thesis
    by (rule
        composition_fri_reachable_partial_candidate_reduction_from_split_residual_bounds_with_candidate_available_and_recorded_missing_zero
        [where E = 0])
      (rule comp_sampled_bound[OF support],
       rule comp_slot_bound[OF support],
       rule comp_merkle_bound[OF support],
       rule comp_next_bound[OF support],
       rule comp_successor_bound[OF support],
       rule comp_final_bound[OF support],
       simp add: wp_composition_fri_reachable_verifier_tie_empty_header_gap_zero,
       rule comp_gap_merkle_bound[OF support],
       rule comp_candidate_available_bound[OF support],
       insert comp_total_bound[OF support], simp)
qed

definition active_fri_residual_obligations_for where
  "active_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
      Rc Ac Pc Nc Sc Gc \<longleftrightarrow>
    (\<forall>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<longrightarrow>
      (let s =
        verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)
       in
        trace_fri_header_tied_residual_obligations s
          (Rt data attacker_state) (Zt data attacker_state)
          (At data attacker_state) (Pt data attacker_state)
          (Ht data attacker_state) (Gt data attacker_state)
          (Nt data attacker_state) (St data attacker_state)
          (Ft data attacker_state) \<and>
        composition_fri_verifier_tied_residual_obligations s
          (Rc data attacker_state) (Ac data attacker_state)
          (Pc data attacker_state)
          (Nc data attacker_state) (Sc data attacker_state)
          (Gc data attacker_state) \<and>
        trace_fri_empty_header_reduction s))"

definition active_trace_fri_residual_obligations_for where
  "active_trace_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
    \<longleftrightarrow>
    (\<forall>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<longrightarrow>
      trace_fri_header_tied_residual_obligations
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Rt data attacker_state) (Zt data attacker_state)
        (At data attacker_state) (Pt data attacker_state)
        (Ht data attacker_state) (Gt data attacker_state)
        (Nt data attacker_state) (St data attacker_state)
        (Ft data attacker_state))"

definition active_composition_fri_residual_obligations_for where
  "active_composition_fri_residual_obligations_for A Rc Ac Pc Nc Sc Gc
    \<longleftrightarrow>
    (\<forall>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<longrightarrow>
      composition_fri_verifier_tied_residual_obligations
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Rc data attacker_state) (Ac data attacker_state)
        (Pc data attacker_state)
        (Nc data attacker_state) (Sc data attacker_state)
        (Gc data attacker_state))"

definition active_empty_trace_fri_reduction_for where
  "active_empty_trace_fri_reduction_for A \<longleftrightarrow>
    (\<forall>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<longrightarrow>
      trace_fri_empty_header_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))"

lemma active_fri_residual_obligations_from_components:
  assumes
    "active_trace_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft"
    "active_composition_fri_residual_obligations_for A Rc Ac Pc Nc Sc Gc"
    "active_empty_trace_fri_reduction_for A"
  shows "active_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
    Rc Ac Pc Nc Sc Gc"
  using assms
  unfolding active_fri_residual_obligations_for_def
    active_trace_fri_residual_obligations_for_def
    active_composition_fri_residual_obligations_for_def
    active_empty_trace_fri_reduction_for_def
  by (simp add: Let_def)

lemma active_fri_residual_obligations_trace_component:
  assumes "active_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
    Rc Ac Pc Nc Sc Gc"
  shows "active_trace_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft"
  using assms
  unfolding active_fri_residual_obligations_for_def
    active_trace_fri_residual_obligations_for_def
  by (simp add: Let_def)

lemma active_fri_residual_obligations_composition_component:
  assumes "active_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
    Rc Ac Pc Nc Sc Gc"
  shows "active_composition_fri_residual_obligations_for A Rc Ac Pc Nc Sc Gc"
  using assms
  unfolding active_fri_residual_obligations_for_def
    active_composition_fri_residual_obligations_for_def
  by (simp add: Let_def)

lemma active_fri_residual_obligations_empty_trace_component:
  assumes "active_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
    Rc Ac Pc Nc Sc Gc"
  shows "active_empty_trace_fri_reduction_for A"
  using assms
  unfolding active_fri_residual_obligations_for_def
    active_empty_trace_fri_reduction_for_def
  by (simp add: Let_def)

lemma active_trace_fri_residual_obligations_from_bounds_without_head:
  fixes
    Rt Zt At Pt Ht Nt St Ft ::
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
    and trace_slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      At data attacker_state"
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
    and trace_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nt data attacker_state"
    and trace_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      St data attacker_state"
    and trace_final_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_final_value_selected_step_missing_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ft data attacker_state"
    and trace_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rt data attacker_state +
        (((((Pt data attacker_state + Ht data attacker_state) +
            Pt data attacker_state) +
           Nt data attacker_state + St data attacker_state +
           (Pt data attacker_state + At data attacker_state +
            Ft data attacker_state)) +
          Pt data attacker_state) +
         At data attacker_state + Zt data attacker_state)
      \<le> trace_fri_error"
  shows "active_trace_fri_residual_obligations_for A Rt Zt At Pt Ht Pt
    Nt St Ft"
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
      (Rt data attacker_state) (Zt data attacker_state)
      (At data attacker_state) (Pt data attacker_state)
      (Ht data attacker_state) (Pt data attacker_state)
      (Nt data attacker_state) (St data attacker_state)
      (Ft data attacker_state)"
    by (rule trace_fri_header_tied_residual_obligations_from_bounds_without_head)
      (rule trace_sampled_bound[OF support],
       rule trace_zero_bound[OF support],
       rule trace_slot_bound[OF support],
       rule trace_merkle_bound[OF support],
       rule trace_structural_bound[OF support],
       rule trace_next_bound[OF support],
       rule trace_successor_bound[OF support],
       rule trace_final_bound[OF support],
       rule trace_total_bound[OF support])
qed

lemma active_trace_fri_residual_obligations_from_bounds_without_head_and_selected_zero:
  fixes
    Rt Zt At Pt Ht Nt St ::
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
    and trace_slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      At data attacker_state"
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
    and trace_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nt data attacker_state"
    and trace_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      St data attacker_state"
    and trace_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rt data attacker_state +
        (((((Pt data attacker_state + Ht data attacker_state) +
            Pt data attacker_state) +
           Nt data attacker_state + St data attacker_state +
           (Pt data attacker_state + At data attacker_state + 0)) +
          Pt data attacker_state) +
         At data attacker_state + Zt data attacker_state)
      \<le> trace_fri_error"
  shows "active_trace_fri_residual_obligations_for A Rt Zt At Pt Ht Pt
    Nt St (\<lambda>_ _. (0::prob))"
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
      (Rt data attacker_state) (Zt data attacker_state)
      (At data attacker_state) (Pt data attacker_state)
      (Ht data attacker_state) (Pt data attacker_state)
      (Nt data attacker_state) (St data attacker_state) 0"
    by (rule
        trace_fri_header_tied_residual_obligations_from_bounds_without_head_and_selected_zero)
      (rule trace_sampled_bound[OF support],
       rule trace_zero_bound[OF support],
       rule trace_slot_bound[OF support],
       rule trace_merkle_bound[OF support],
       rule trace_structural_bound[OF support],
       rule trace_next_bound[OF support],
       rule trace_successor_bound[OF support],
       rule trace_total_bound[OF support])
qed

lemma active_trace_fri_residual_obligations_from_bounds_without_head_slot_and_selected_zero:
  fixes
    Rt Zt Pt Ht Nt St ::
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
    and trace_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nt data attacker_state"
    and trace_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      St data attacker_state"
    and trace_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rt data attacker_state +
        (((((Pt data attacker_state + Ht data attacker_state) +
            Pt data attacker_state) +
           Nt data attacker_state + St data attacker_state +
           (Pt data attacker_state + 0 + 0)) +
          Pt data attacker_state) +
         0 + Zt data attacker_state)
      \<le> trace_fri_error"
  shows
    "active_trace_fri_residual_obligations_for A Rt Zt
      (\<lambda>_ _. (0::prob)) Pt Ht Pt Nt St (\<lambda>_ _. (0::prob))"
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
      (Pt data attacker_state) (Nt data attacker_state)
      (St data attacker_state) 0"
    by (rule
        trace_fri_header_tied_residual_obligations_from_bounds_without_head_slot_and_selected_zero)
      (rule trace_sampled_bound[OF support],
       rule trace_zero_bound[OF support],
       rule trace_merkle_bound[OF support],
       rule trace_structural_bound[OF support],
       rule trace_next_bound[OF support],
       rule trace_successor_bound[OF support],
       rule trace_total_bound[OF support])
qed

lemma active_composition_fri_residual_obligations_from_bounds:
  fixes
    Rc Ac Pc Nc Sc Gc ::
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
    and comp_slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ac data attacker_state"
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
    and comp_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nc data attacker_state"
    and comp_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Sc data attacker_state"
    and comp_final_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Gc data attacker_state"
    and comp_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rc data attacker_state +
        (((Pc data attacker_state + Ac data attacker_state) +
          Nc data attacker_state + Sc data attacker_state +
          Gc data attacker_state + Pc data attacker_state) +
         Ac data attacker_state)
      \<le> composition_fri_error"
  shows "active_composition_fri_residual_obligations_for A Rc Ac Pc Nc Sc Gc"
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
      (Rc data attacker_state) (Ac data attacker_state)
      (Pc data attacker_state)
      (Nc data attacker_state) (Sc data attacker_state)
      (Gc data attacker_state)"
    by (rule composition_fri_verifier_tied_residual_obligations_from_bounds)
      (rule comp_sampled_bound[OF support],
       rule comp_slot_bound[OF support],
       rule comp_merkle_bound[OF support],
       rule comp_next_bound[OF support],
       rule comp_successor_bound[OF support],
       rule comp_final_bound[OF support],
       rule comp_total_bound[OF support])
qed

lemma active_composition_fri_residual_obligations_from_bounds_slot_zero:
  fixes
    Rc Pc Nc Sc Gc ::
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
    and comp_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nc data attacker_state"
    and comp_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Sc data attacker_state"
    and comp_final_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Gc data attacker_state"
    and comp_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rc data attacker_state +
        (((Pc data attacker_state + 0) +
          Nc data attacker_state + Sc data attacker_state +
          Gc data attacker_state + Pc data attacker_state) +
         0)
      \<le> composition_fri_error"
  shows
    "active_composition_fri_residual_obligations_for A Rc
      (\<lambda>_ _. (0::prob)) Pc Nc Sc Gc"
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
      (Nc data attacker_state) (Sc data attacker_state)
      (Gc data attacker_state)"
    by (rule composition_fri_verifier_tied_residual_obligations_from_bounds_slot_zero)
      (rule comp_sampled_bound[OF support],
       rule comp_merkle_bound[OF support],
       rule comp_next_bound[OF support],
       rule comp_successor_bound[OF support],
       rule comp_final_bound[OF support],
       rule comp_total_bound[OF support])
qed

lemma active_fri_reductions_forD:
  assumes "active_fri_reductions_for A"
    and "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  shows
    "trace_fri_header_tied_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    "composition_fri_verifier_tied_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    "trace_fri_empty_header_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
  using assms unfolding active_fri_reductions_for_def by blast+

lemma trace_fri_header_tied_reduction_from_residual_obligations:
  assumes
    "trace_fri_header_tied_residual_obligations s r_b z_b a_b p_b h_b g_b n_b s_b f_b"
  shows "trace_fri_header_tied_reduction s"
proof -
  have sampled:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> r_b"
    using assms unfolding trace_fri_header_tied_residual_obligations_def
    by blast
  have zero:
    "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> z_b"
    using assms unfolding trace_fri_header_tied_residual_obligations_def
    by blast
  have slot:
    "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap s) s
      \<le> a_b"
    using assms unfolding trace_fri_header_tied_residual_obligations_def
    by blast
  have merkle:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    using assms unfolding trace_fri_header_tied_residual_obligations_def
    by blast
  have structural:
    "wp_event verify_monad
      (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> h_b"
    using assms unfolding trace_fri_header_tied_residual_obligations_def
    by blast
  have head_neq:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap s) s \<le> g_b"
    using assms unfolding trace_fri_header_tied_residual_obligations_def
    by blast
  have head_mismatch:
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_mismatch_gap s) s \<le> g_b"
    by (rule
        wp_trace_fri_header_tied_base_head_value_mismatch_gap_bound_from_neq_gap
        [OF head_neq])
  have alignment:
    "wp_event verify_monad
      (trace_fri_header_tied_base_value_alignment_gap s) s \<le> g_b"
    by (rule
        wp_trace_fri_header_tied_base_value_alignment_gap_bound_from_head_value_mismatch_gap
        [OF head_mismatch])
  have next_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le> n_b"
    using assms unfolding trace_fri_header_tied_residual_obligations_def
    by blast
  have successor:
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le> s_b"
    using assms unfolding trace_fri_header_tied_residual_obligations_def
    by blast
  have selected_final:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_selected_step_missing_gap s) s
      \<le> f_b"
    using assms unfolding trace_fri_header_tied_residual_obligations_def
    by blast
  have final_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_final_value_replay_gap s) s \<le>
      p_b + a_b + f_b"
    by (rule
        wp_trace_fri_header_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step)
      (rule merkle, rule slot, rule selected_final)
  have total:
    "r_b + (((((p_b + h_b) + g_b) + n_b + s_b +
        (p_b + a_b + f_b)) + p_b) + a_b + z_b)
        \<le> trace_fri_error"
    using assms unfolding trace_fri_header_tied_residual_obligations_def
    by blast
  show ?thesis
    by (rule trace_fri_header_tied_reduction_from_residual_bounds
        [OF sampled zero slot merkle structural alignment next_bound successor final_bound
          total])
qed

lemma composition_fri_verifier_tied_reduction_from_residual_obligations:
  assumes
    "composition_fri_verifier_tied_residual_obligations s r_b a_b p_b n_b s_b g_b"
  shows "composition_fri_verifier_tied_reduction s"
proof -
  have sampled:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s
      \<le> r_b"
    using assms
    unfolding composition_fri_verifier_tied_residual_obligations_def
    by blast
  have slot:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> a_b"
    using assms
    unfolding composition_fri_verifier_tied_residual_obligations_def
    by blast
  have merkle:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    using assms
    unfolding composition_fri_verifier_tied_residual_obligations_def
    by blast
  have next_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_next_value_replay_gap s) s \<le> n_b"
    using assms
    unfolding composition_fri_verifier_tied_residual_obligations_def
    by blast
  have successor:
    "wp_event verify_monad
      (composition_fri_verifier_tied_successor_replay_gap s) s \<le> s_b"
    using assms
    unfolding composition_fri_verifier_tied_residual_obligations_def
    by blast
  have final_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap s) s \<le> g_b"
    using assms
    unfolding composition_fri_verifier_tied_residual_obligations_def
    by blast
  have total:
    "r_b + (((p_b + a_b) + n_b + s_b + g_b + p_b) + a_b)
      \<le> composition_fri_error"
    using assms
    unfolding composition_fri_verifier_tied_residual_obligations_def
    by blast
  have total_zero:
    "r_b + (((p_b + 0) + n_b + s_b + g_b + p_b) + a_b)
      \<le> composition_fri_error"
    by (rule order_trans[OF _ total]) simp
  show ?thesis
    by (rule
        composition_fri_verifier_tied_reduction_from_residual_bounds_with_recorded_missing_zero
        [OF sampled slot merkle next_bound successor final_bound total_zero])
qed

lemma active_fri_reductions_from_residual_obligations:
  assumes "active_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
    Rc Ac Pc Nc Sc Gc"
  shows "active_fri_reductions_for A"
  unfolding active_fri_reductions_for_def
proof (intro allI impI conjI)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have trace_obs:
    "trace_fri_header_tied_residual_obligations ?s
      (Rt data attacker_state) (Zt data attacker_state)
      (At data attacker_state) (Pt data attacker_state)
      (Ht data attacker_state) (Gt data attacker_state)
      (Nt data attacker_state) (St data attacker_state)
      (Ft data attacker_state)"
    using assms support
    unfolding active_fri_residual_obligations_for_def by (simp add: Let_def)
  have composition_obs:
    "composition_fri_verifier_tied_residual_obligations ?s
      (Rc data attacker_state) (Ac data attacker_state)
      (Pc data attacker_state)
      (Nc data attacker_state) (Sc data attacker_state)
      (Gc data attacker_state)"
    using assms support
    unfolding active_fri_residual_obligations_for_def by (simp add: Let_def)
  have empty_obs:
    "trace_fri_empty_header_reduction ?s"
    using assms support
    unfolding active_fri_residual_obligations_for_def by (simp add: Let_def)
  show "trace_fri_header_tied_reduction ?s"
    by (rule trace_fri_header_tied_reduction_from_residual_obligations
        [OF trace_obs])
  show "composition_fri_verifier_tied_reduction ?s"
    by (rule
        composition_fri_verifier_tied_reduction_from_residual_obligations
        [OF composition_obs])
  show "trace_fri_empty_header_reduction ?s"
    by (rule empty_obs)
qed

lemma active_fri_reductions_from_reachable:
  assumes trace_reachable:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_reachable_partial_candidate_reduction_assumption
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
    and composition_reachable:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_reachable_partial_candidate_reduction_assumption
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows "active_fri_reductions_for A"
  unfolding active_fri_reductions_for_def
proof (intro allI impI conjI)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "trace_fri_header_tied_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    by (rule trace_fri_header_tied_reduction_from_reachable_reduction)
      (rule trace_reachable[OF support])
  show "composition_fri_verifier_tied_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    by (rule composition_fri_verifier_tied_reduction_from_reachable_reduction)
      (rule composition_reachable[OF support])
  show "trace_fri_empty_header_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    by (rule trace_fri_empty_header_reduction_from_reachable_reduction)
      (rule trace_reachable[OF support])
qed

lemma active_fri_residual_obligations_from_bounds:
  fixes
    Rt Zt At Pt Ht Gt Nt St Ft ::
      "('f staged_proof_data \<Rightarrow>
        'f protocol_channel \<Rightarrow> prob)"
    and Rc Ac Pc Nc Sc Gc ::
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
    and trace_slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      At data attacker_state"
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
    and trace_head_neq_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_base_head_value_neq_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Gt data attacker_state"
    and trace_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nt data attacker_state"
    and trace_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      St data attacker_state"
    and trace_final_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_final_value_selected_step_missing_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ft data attacker_state"
    and trace_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rt data attacker_state +
        (((((Pt data attacker_state + Ht data attacker_state) +
            Gt data attacker_state) +
           Nt data attacker_state + St data attacker_state +
           (Pt data attacker_state + At data attacker_state +
            Ft data attacker_state)) +
          Pt data attacker_state) +
         At data attacker_state + Zt data attacker_state)
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
    and comp_slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ac data attacker_state"
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
    and comp_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nc data attacker_state"
    and comp_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Sc data attacker_state"
    and comp_final_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Gc data attacker_state"
    and comp_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rc data attacker_state +
        (((Pc data attacker_state + Ac data attacker_state) +
          Nc data attacker_state + Sc data attacker_state +
          Gc data attacker_state + Pc data attacker_state) +
         Ac data attacker_state)
      \<le> composition_fri_error"
    and empty_header_reduction:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_empty_header_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows "active_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
    Rc Ac Pc Nc Sc Gc"
  unfolding active_fri_residual_obligations_for_def
proof (intro allI impI)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "(let s =
        verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)
       in
        trace_fri_header_tied_residual_obligations s
          (Rt data attacker_state) (Zt data attacker_state)
          (At data attacker_state) (Pt data attacker_state)
          (Ht data attacker_state) (Gt data attacker_state)
          (Nt data attacker_state) (St data attacker_state)
          (Ft data attacker_state) \<and>
        composition_fri_verifier_tied_residual_obligations s
          (Rc data attacker_state) (Ac data attacker_state)
          (Pc data attacker_state)
          (Nc data attacker_state) (Sc data attacker_state)
          (Gc data attacker_state) \<and>
        trace_fri_empty_header_reduction s)"
    using trace_sampled_bound[OF support] trace_zero_bound[OF support]
      trace_slot_bound[OF support] trace_merkle_bound[OF support]
      trace_structural_bound[OF support] trace_head_neq_bound[OF support]
      trace_next_bound[OF support] trace_successor_bound[OF support]
      trace_final_bound[OF support] trace_total_bound[OF support]
      comp_sampled_bound[OF support] comp_slot_bound[OF support]
      comp_merkle_bound[OF support] comp_next_bound[OF support]
      comp_successor_bound[OF support]
      comp_final_bound[OF support] comp_total_bound[OF support]
      empty_header_reduction[OF support]
    unfolding trace_fri_header_tied_residual_obligations_def
      composition_fri_verifier_tied_residual_obligations_def
    by (simp add: Let_def)
qed

lemma active_fri_residual_obligations_from_bounds_without_head:
  fixes
    Rt Zt At Pt Ht Nt St Ft ::
      "('f staged_proof_data \<Rightarrow>
        'f protocol_channel \<Rightarrow> prob)"
    and Rc Ac Pc Nc Sc Gc ::
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
    and trace_slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      At data attacker_state"
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
    and trace_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nt data attacker_state"
    and trace_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      St data attacker_state"
    and trace_final_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_final_value_selected_step_missing_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ft data attacker_state"
    and trace_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rt data attacker_state +
        (((((Pt data attacker_state + Ht data attacker_state) +
            Pt data attacker_state) +
           Nt data attacker_state + St data attacker_state +
           (Pt data attacker_state + At data attacker_state +
            Ft data attacker_state)) +
          Pt data attacker_state) +
         At data attacker_state + Zt data attacker_state)
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
    and comp_slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ac data attacker_state"
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
    and comp_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nc data attacker_state"
    and comp_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Sc data attacker_state"
    and comp_final_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Gc data attacker_state"
    and comp_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rc data attacker_state +
        (((Pc data attacker_state + Ac data attacker_state) +
          Nc data attacker_state + Sc data attacker_state +
          Gc data attacker_state + Pc data attacker_state) +
         Ac data attacker_state)
      \<le> composition_fri_error"
    and empty_header_reduction:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_empty_header_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows "active_fri_residual_obligations_for A Rt Zt At Pt Ht Pt Nt St Ft
    Rc Ac Pc Nc Sc Gc"
proof (rule active_fri_residual_obligations_from_bounds)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Rt data attacker_state"
    by (rule trace_sampled_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Zt data attacker_state"
    by (rule trace_zero_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    At data attacker_state"
    by (rule trace_slot_bound[OF support])
  show "wp_event verify_monad
      (partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Pt data attacker_state"
    by (rule trace_merkle_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_sibling_mismatch_structural_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Ht data attacker_state"
    by (rule trace_structural_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Pt data attacker_state"
    by (rule
        wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle)
      (rule trace_merkle_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Nt data attacker_state"
    by (rule trace_next_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    St data attacker_state"
    by (rule trace_successor_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_final_value_selected_step_missing_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Ft data attacker_state"
    by (rule trace_final_bound[OF support])
  show "Rt data attacker_state +
      (((((Pt data attacker_state + Ht data attacker_state) +
          Pt data attacker_state) +
         Nt data attacker_state + St data attacker_state +
         (Pt data attacker_state + At data attacker_state +
          Ft data attacker_state)) +
        Pt data attacker_state) +
       At data attacker_state + Zt data attacker_state)
    \<le> trace_fri_error"
    by (rule trace_total_bound[OF support])
  show "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Rc data attacker_state"
    by (rule comp_sampled_bound[OF support])
  show "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Ac data attacker_state"
    by (rule comp_slot_bound[OF support])
  show "wp_event verify_monad
      (partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Pc data attacker_state"
    by (rule comp_merkle_bound[OF support])
  show "wp_event verify_monad
      (composition_fri_verifier_tied_next_value_replay_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Nc data attacker_state"
    by (rule comp_next_bound[OF support])
  show "wp_event verify_monad
      (composition_fri_verifier_tied_successor_replay_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Sc data attacker_state"
    by (rule comp_successor_bound[OF support])
  show "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le>
    Gc data attacker_state"
    by (rule comp_final_bound[OF support])
  show "Rc data attacker_state +
      (((Pc data attacker_state + Ac data attacker_state) +
        Nc data attacker_state + Sc data attacker_state +
        Gc data attacker_state + Pc data attacker_state) +
       Ac data attacker_state)
    \<le> composition_fri_error"
    by (rule comp_total_bound[OF support])
  show "trace_fri_empty_header_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    by (rule empty_header_reduction[OF support])
qed

lemma active_fri_residual_obligations_from_bounds_without_head_and_selected_zero:
  fixes
    Rt Zt At Pt Ht Nt St ::
      "('f staged_proof_data \<Rightarrow>
        'f protocol_channel \<Rightarrow> prob)"
    and Rc Ac Pc Nc Sc Gc ::
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
    and trace_slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      At data attacker_state"
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
    and trace_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nt data attacker_state"
    and trace_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      St data attacker_state"
    and trace_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rt data attacker_state +
        (((((Pt data attacker_state + Ht data attacker_state) +
            Pt data attacker_state) +
           Nt data attacker_state + St data attacker_state +
           (Pt data attacker_state + At data attacker_state + 0)) +
          Pt data attacker_state) +
         At data attacker_state + Zt data attacker_state)
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
    and comp_slot_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ac data attacker_state"
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
    and comp_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nc data attacker_state"
    and comp_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Sc data attacker_state"
    and comp_final_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Gc data attacker_state"
    and comp_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rc data attacker_state +
        (((Pc data attacker_state + Ac data attacker_state) +
          Nc data attacker_state + Sc data attacker_state +
          Gc data attacker_state + Pc data attacker_state) +
         Ac data attacker_state)
      \<le> composition_fri_error"
    and empty_header_reduction:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_empty_header_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows "active_fri_residual_obligations_for A Rt Zt At Pt Ht Pt Nt St
    (\<lambda>_ _. (0::prob)) Rc Ac Pc Nc Sc Gc"
proof (rule active_fri_residual_obligations_from_components)
  show "active_trace_fri_residual_obligations_for A Rt Zt At Pt Ht Pt
      Nt St (\<lambda>_ _. (0::prob))"
    by (rule
        active_trace_fri_residual_obligations_from_bounds_without_head_and_selected_zero)
      (erule trace_sampled_bound, erule trace_zero_bound,
       erule trace_slot_bound, erule trace_merkle_bound,
       erule trace_structural_bound, erule trace_next_bound,
       erule trace_successor_bound, erule trace_total_bound)
  show "active_composition_fri_residual_obligations_for A Rc Ac Pc Nc Sc Gc"
    by (rule active_composition_fri_residual_obligations_from_bounds)
      (erule comp_sampled_bound, erule comp_slot_bound,
       erule comp_merkle_bound, erule comp_next_bound,
       erule comp_successor_bound, erule comp_final_bound,
       erule comp_total_bound)
  show "active_empty_trace_fri_reduction_for A"
    unfolding active_empty_trace_fri_reduction_for_def
    by (intro allI impI, erule empty_header_reduction)
qed

lemma active_fri_residual_obligations_from_bounds_without_head_slot_and_selected_zero:
  fixes
    Rt Zt Pt Ht Nt St ::
      "('f staged_proof_data \<Rightarrow>
        'f protocol_channel \<Rightarrow> prob)"
    and Rc Pc Nc Sc Gc ::
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
    and trace_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nt data attacker_state"
    and trace_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      St data attacker_state"
    and trace_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rt data attacker_state +
        (((((Pt data attacker_state + Ht data attacker_state) +
            Pt data attacker_state) +
           Nt data attacker_state + St data attacker_state +
           (Pt data attacker_state + 0 + 0)) +
          Pt data attacker_state) +
         0 + Zt data attacker_state)
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
    and comp_next_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Nc data attacker_state"
    and comp_successor_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Sc data attacker_state"
    and comp_final_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Gc data attacker_state"
    and comp_total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Rc data attacker_state +
        (((Pc data attacker_state + 0) +
          Nc data attacker_state + Sc data attacker_state +
          Gc data attacker_state + Pc data attacker_state) +
         0)
      \<le> composition_fri_error"
    and empty_header_reduction:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_empty_header_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows
    "active_fri_residual_obligations_for A Rt Zt (\<lambda>_ _. (0::prob))
      Pt Ht Pt Nt St (\<lambda>_ _. (0::prob)) Rc (\<lambda>_ _. (0::prob))
      Pc Nc Sc Gc"
proof (rule active_fri_residual_obligations_from_components)
  show "active_trace_fri_residual_obligations_for A Rt Zt
      (\<lambda>_ _. (0::prob)) Pt Ht Pt Nt St (\<lambda>_ _. (0::prob))"
    by (rule
        active_trace_fri_residual_obligations_from_bounds_without_head_slot_and_selected_zero)
      (erule trace_sampled_bound, erule trace_zero_bound,
       erule trace_merkle_bound, erule trace_structural_bound,
       erule trace_next_bound, erule trace_successor_bound,
       erule trace_total_bound)
  show "active_composition_fri_residual_obligations_for A Rc
      (\<lambda>_ _. (0::prob)) Pc Nc Sc Gc"
    by (rule active_composition_fri_residual_obligations_from_bounds_slot_zero)
      (erule comp_sampled_bound, erule comp_merkle_bound,
       erule comp_next_bound, erule comp_successor_bound,
       erule comp_final_bound, erule comp_total_bound)
  show "active_empty_trace_fri_reduction_for A"
    unfolding active_empty_trace_fri_reduction_for_def
    by (intro allI impI, erule empty_header_reduction)
qed

lemmas active_fri_reductions_from_residual_bounds =
  active_fri_reductions_from_residual_obligations[
    OF active_fri_residual_obligations_from_bounds]

lemmas active_fri_reductions_from_residual_bounds_without_head =
  active_fri_reductions_from_residual_obligations[
    OF active_fri_residual_obligations_from_bounds_without_head]

lemmas active_fri_reductions_from_residual_bounds_without_head_and_selected_zero =
  active_fri_reductions_from_residual_obligations[
    OF active_fri_residual_obligations_from_bounds_without_head_and_selected_zero]

lemmas active_fri_reductions_from_residual_bounds_without_head_slot_and_selected_zero =
  active_fri_reductions_from_residual_obligations[
    OF active_fri_residual_obligations_from_bounds_without_head_slot_and_selected_zero]

lemma active_fri_reductions_staged_trace_bound:
  assumes active: "active_fri_reductions_for A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> trace_fri_error"
  by (rule trace_fri_header_tied_reduction_staged_bound)
    (rule active_fri_reductions_forD(1)[OF active])

lemma active_fri_reductions_staged_composition_bound:
  assumes active: "active_fri_reductions_for A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> composition_fri_error"
  by (rule composition_fri_verifier_tied_reduction_staged_bound)
    (rule active_fri_reductions_forD(2)[OF active])

lemma active_fri_reductions_staged_empty_header_bound:
  assumes active: "active_fri_reductions_for A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
  by (rule trace_fri_empty_header_reduction_staged_bound)
    (rule active_fri_reductions_forD(3)[OF active])

lemma active_trace_fri_residual_obligations_staged_trace_bound:
  assumes
    "active_trace_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> trace_fri_error"
proof (rule trace_fri_header_tied_reduction_staged_bound)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have residual:
    "trace_fri_header_tied_residual_obligations ?s
      (Rt data attacker_state) (Zt data attacker_state)
      (At data attacker_state) (Pt data attacker_state)
      (Ht data attacker_state) (Gt data attacker_state)
      (Nt data attacker_state) (St data attacker_state)
      (Ft data attacker_state)"
    using assms support
    unfolding active_trace_fri_residual_obligations_for_def by simp
  show "trace_fri_header_tied_reduction ?s"
    by (rule trace_fri_header_tied_reduction_from_residual_obligations
        [OF residual])
qed

lemma active_composition_fri_residual_obligations_staged_composition_bound:
  assumes
    "active_composition_fri_residual_obligations_for A Rc Ac Pc Nc Sc Gc"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> composition_fri_error"
proof (rule composition_fri_verifier_tied_reduction_staged_bound)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have residual:
    "composition_fri_verifier_tied_residual_obligations ?s
      (Rc data attacker_state) (Ac data attacker_state)
      (Pc data attacker_state)
      (Nc data attacker_state) (Sc data attacker_state)
      (Gc data attacker_state)"
    using assms support
    unfolding active_composition_fri_residual_obligations_for_def by simp
  show "composition_fri_verifier_tied_reduction ?s"
    by (rule composition_fri_verifier_tied_reduction_from_residual_obligations
        [OF residual])
qed

lemma active_empty_trace_fri_reduction_staged_empty_header_bound:
  assumes "active_empty_trace_fri_reduction_for A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
  by (rule trace_fri_empty_header_reduction_staged_bound)
    (use assms in
      \<open>unfold active_empty_trace_fri_reduction_for_def, blast\<close>)

lemma active_fri_residual_obligations_staged_trace_bound:
  assumes "active_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
    Rc Ac Pc Nc Sc Gc"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_header_tied_partial_candidate)
      adversary_initial_state \<le> trace_fri_error"
  by (rule active_fri_reductions_staged_trace_bound)
    (rule active_fri_reductions_from_residual_obligations[OF assms])

lemma active_fri_residual_obligations_staged_composition_bound:
  assumes "active_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
    Rc Ac Pc Nc Sc Gc"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> composition_fri_error"
  by (rule active_fri_reductions_staged_composition_bound)
    (rule active_fri_reductions_from_residual_obligations[OF assms])

lemma active_fri_residual_obligations_staged_empty_header_bound:
  assumes "active_fri_residual_obligations_for A Rt Zt At Pt Ht Gt Nt St Ft
    Rc Ac Pc Nc Sc Gc"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
  by (rule active_fri_reductions_staged_empty_header_bound)
    (rule active_fri_reductions_from_residual_obligations[OF assms])

end

context soundness_fri
begin

lemma active_fri_reductions_for_from_locale:
  "active_fri_reductions_for A"
  unfolding active_fri_reductions_for_def
proof (intro allI impI conjI)
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "trace_fri_header_tied_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    using trace_fri_active_reductions[OF support] by blast
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "composition_fri_verifier_tied_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    by (rule composition_fri_active_reduction[OF support])
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "trace_fri_empty_header_reduction
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
    using trace_fri_active_reductions[OF support] by blast
qed

end

end
