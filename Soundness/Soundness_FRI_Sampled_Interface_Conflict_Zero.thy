(*  Title:      Stark/Soundness_FRI_Sampled_Interface_Conflict_Zero.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Sampled_Interface_Conflict_Zero
  imports Soundness_FRI_Sampled_Interface
begin

text \<open>
  Conflict/zero active-FRI wrapper for the sampled-query interface.

  This narrow layer keeps the sampled-interface theory from
  growing further while exposing the cleaner trace route that does not carry a
  separate recorded-sibling-missing component.
\<close>

context soundness
begin

lemma active_fri_reductions_for_from_trace_augmented_conflict_zero_composition_sampled_query_and_empty_conflict_zero:
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
  shows "active_fri_reductions_for A"
proof (rule
    active_fri_reductions_for_from_trace_augmented_conflict_zero_composition_sampled_and_empty_conflict_zero)
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
      (trace_fri_header_tied_sampled_assignment_conflict ?s) ?s
      \<le> TraceConflict data attacker_state"
    by (rule trace_conflict_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction ?s) ?s
      \<le> TraceZero data attacker_state"
    by (rule trace_zero_bound[OF support])
  show "wp_event verify_monad (partial_merkle_inconsistency_bad ?s) ?s
      \<le> TraceMerkle data attacker_state"
    by (rule trace_merkle_bound[OF support])
  show "TraceAug data attacker_state +
      ((TraceConflict data attacker_state + TraceZero data attacker_state) +
        TraceMerkle data attacker_state)
      \<le> trace_fri_error"
    by (rule trace_total[OF support])
  show "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain ?s) ?s
      \<le> CompSampled data attacker_state"
    by (rule wp_composition_fri_verifier_tied_sampled_layer_chain_bound_from_sampled)
      (rule wp_composition_fri_sampled_bound_from_canonical,
        insert composition_sampled_bound[OF support],
        simp add: wp_composition_fri_sampled_query_bad_candidate_iff_canonical)
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
    by (rule wp_trace_fri_sampled_bound_from_canonical)
      (insert empty_sampled_bound[OF support],
        simp add: wp_trace_fri_sampled_query_bad_candidate_iff_canonical)
  show "wp_event verify_monad
      (trace_fri_sampled_assignment_conflict ?s) ?s
      \<le> EmptyConflict data attacker_state"
    by (rule empty_conflict_bound[OF support])
  show "wp_event verify_monad
      (trace_fri_zero_round_final_obstruction ?s) ?s
      \<le> EmptyZero data attacker_state"
    by (rule empty_zero_bound[OF support])
  show "EmptySampled data attacker_state +
      (EmptyConflict data attacker_state + EmptyZero data attacker_state)
      \<le> trace_fri_error"
    by (rule empty_total[OF support])
qed

end

end
