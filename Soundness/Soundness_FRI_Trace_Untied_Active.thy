(*  Title:      Stark/Soundness_FRI_Trace_Untied_Active.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Trace_Untied_Active
  imports
    Soundness_FRI_Active_Reductions
    Soundness_FRI_Trace_Untied_Cases
begin

text \<open>
  Active-level packaging for the trace FRI untied-witness blocker.  This theory
  is intentionally downstream of the large active-reduction layer so that the
  new diagnostic event can be used without growing that file further.
\<close>

context soundness
begin

lemma active_trace_fri_reachable_reduction_from_header_merkle_and_untied:
  fixes Ht Mt Ut ::
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
    and total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Ht data attacker_state +
        (Mt data attacker_state + Ut data attacker_state) \<le>
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
      trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied)
    (rule trace_header_bound[OF support],
     rule trace_merkle_bound[OF support],
     rule trace_untied_bound[OF support],
     rule total_bound[OF support])

lemma active_trace_fri_reachable_reduction_from_header_merkle_and_untied_cases:
  fixes Ht Mt Rt Qt Ot ::
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
      Rt data attacker_state"
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
      Qt data attacker_state"
    and trace_openings_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_openings_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ot data attacker_state"
    and total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Ht data attacker_state +
        (Mt data attacker_state +
          (Rt data attacker_state +
            (Qt data attacker_state + Ot data attacker_state))) \<le>
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
      trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied_cases)
    (rule trace_header_bound[OF support],
     rule trace_merkle_bound[OF support],
     rule trace_root_bound[OF support],
     rule trace_query_bound[OF support],
     rule trace_openings_bound[OF support],
     rule total_bound[OF support])

lemma active_trace_fri_reachable_reduction_from_header_merkle_and_untied_query_openings:
  fixes Ht Mt Qt Ot ::
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
      Qt data attacker_state"
    and trace_openings_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_openings_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ot data attacker_state"
    and total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Ht data attacker_state +
        (Mt data attacker_state +
          (Qt data attacker_state + Ot data attacker_state)) \<le>
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
      trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied_query_openings)
    (rule trace_header_bound[OF support],
     rule trace_merkle_bound[OF support],
     rule trace_query_bound[OF support],
     rule trace_openings_bound[OF support],
     rule total_bound[OF support])

lemma active_trace_fri_reachable_reduction_from_header_merkle_and_untied_openings:
  fixes Ht Mt Ot ::
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
    and trace_openings_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_openings_gap
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le>
      Ot data attacker_state"
    and total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Ht data attacker_state +
        (Mt data attacker_state + Ot data attacker_state) \<le>
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
      trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied_openings)
    (rule trace_header_bound[OF support],
     rule trace_merkle_bound[OF support],
     rule trace_openings_bound[OF support],
     rule total_bound[OF support])

lemma active_trace_fri_reachable_reduction_from_header_merkle_hash_root_query:
  fixes Ht Mt Kt Rt Qt ::
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
      Rt data attacker_state"
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
      Qt data attacker_state"
    and total_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      Ht data attacker_state +
        (Mt data attacker_state +
          (Kt data attacker_state +
            (Rt data attacker_state + Qt data attacker_state))) \<le>
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
      trace_fri_reachable_partial_candidate_reduction_from_header_merkle_hash_root_query)
    (rule trace_header_bound[OF support],
     rule trace_merkle_bound[OF support],
     rule trace_hash_bound[OF support],
     rule trace_root_bound[OF support],
     rule trace_query_bound[OF support],
     rule total_bound[OF support])

end

end
