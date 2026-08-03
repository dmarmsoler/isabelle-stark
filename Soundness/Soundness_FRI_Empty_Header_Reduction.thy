(*  Title:      Stark/Soundness_FRI_Empty_Header_Reduction.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Empty_Header_Reduction
  imports Soundness_FRI_Trace_Residuals
begin

text \<open>
  Named reduction interface for the empty-composition-header trace FRI branch.
  This keeps the large reachable-FRI theory stable while giving the final route
  the same active-bound shape for all three FRI components.
\<close>

context soundness
begin

definition trace_fri_empty_header_reduction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
where
  "trace_fri_empty_header_reduction s \<longleftrightarrow>
    wp_event verify_monad
      (trace_fri_bad_with_empty_composition_header_candidates s) s \<le>
      trace_fri_error"

lemma trace_fri_empty_header_reductionD:
  assumes "trace_fri_empty_header_reduction s"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_empty_composition_header_candidates s) s \<le>
      trace_fri_error"
  using assms unfolding trace_fri_empty_header_reduction_def by simp

lemma trace_fri_empty_header_reduction_staged_bound:
  assumes reductions:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      trace_fri_empty_header_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> trace_fri_error"
  by (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
    (simp_all add: trace_fri_bad_with_empty_composition_header_candidates_not_None
      trace_fri_empty_header_reductionD reductions)

lemma trace_fri_empty_header_reduction_from_reachable_reduction:
  assumes "trace_fri_reachable_partial_candidate_reduction_assumption s"
  shows "trace_fri_empty_header_reduction s"
proof -
  have reachable:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le>
      trace_fri_error"
    using assms
    unfolding trace_fri_reachable_partial_candidate_reduction_assumption_def
    by simp
  show ?thesis
    unfolding trace_fri_empty_header_reduction_def
    by (rule order_trans[OF _ reachable])
      (rule wp_event_mono,
        rule
          trace_fri_bad_with_empty_composition_header_candidates_imp_reachable_partial_candidate)
qed

end

end
