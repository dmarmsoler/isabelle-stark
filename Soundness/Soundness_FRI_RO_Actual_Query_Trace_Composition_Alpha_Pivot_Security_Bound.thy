(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Security_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Security_Bound
  imports
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Closed_Bound
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Obstruction_Classification
begin

context soundness
begin

lemma
  wp_ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent_le:
  "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
      s
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_first_root_trace_composition_all_queries_consistent
      s"
  unfolding
    ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
proof (rule wp_event_bind_bound_by_head_event)
  show
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_first_root_trace_composition_all_queries_consistent
      s
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_first_root_trace_composition_all_queries_consistent
      s"
    by simp
next
  show
    "ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
        None \<Longrightarrow>
      ro_checked_staged_first_root_trace_composition_all_queries_consistent
        None"
    unfolding
      ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent_def
      ro_checked_staged_first_root_trace_composition_all_queries_consistent_def
    by simp
next
  fix x t out
  assume head:
    "Some (x, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          s)"
  obtain prefix_with_state data query_start raws query_states where x_eq:
    "x = (prefix_with_state, data, query_start, raws, query_states)"
    by (cases x) auto
  assume tail:
    "out \<in>
      set_dist
        (execute
          (case x of
            (prefix_with_state, data, query_start, raws, query_states) \<Rightarrow>
              get \<bind>
              (\<lambda>attacker_state.
                put
                  (verifier_state_from_adversary attacker_state
                    (staged_proof_transcript data)) \<bind>
                (\<lambda>_. ro_verify_monad \<bind>
                  (\<lambda>result.
                    return
                      (((prefix_with_state, data, query_start, raws,
                          query_states), attacker_state), result)))))
          t)"
    and all_consistent:
      "ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
        out"
  show
    "ro_checked_staged_first_root_trace_composition_all_queries_consistent
      (Some (x, t))"
    using tail all_consistent
    unfolding x_eq
      ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent_def
      ro_checked_staged_first_root_trace_composition_all_queries_consistent_def
    by (auto simp: wpsimps elim!: set_dist_bindE
        split: option.splits prod.splits)
qed

lemma
  wp_ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent
      adversary_initial_state
    \<le> ro_checked_staged_first_root_alpha_pivot_error budgets"
  by (rule order_trans[
      OF
        wp_ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent_le
        wp_ro_checked_staged_first_root_all_queries_consistent_bound[
          OF false_statement wf controlled nonempty]])

end
end
