(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Trace_Composition_Security_Query_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Security_Query_Bound
  imports
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Prequery_Closed_Bound
begin

context soundness
begin

definition
  ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
where
  "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix_with_state, data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        ro_query_head_dependent_actual_query_index_list_hit Q
          (Some
            ((prefix_with_state, data, query_start, raws, query_states),
              attacker_state)))"


lemma
  wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le:
  "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        Q)
      s
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit Q)
      s"
  unfolding
    ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
proof (rule wp_event_bind_bound_by_head_event)
  show
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit Q)
      s
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit Q)
      s"
    by simp
next
  show
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        Q None \<Longrightarrow>
      ro_query_head_dependent_actual_query_index_list_hit Q None"
    unfolding
      ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
    by simp
next
  fix x t out
  assume head:
    "Some (x, t) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
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
    and hit:
      "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        Q out"
  show
    "ro_query_head_dependent_actual_query_index_list_hit Q (Some (x, t))"
    using tail hit
    unfolding x_eq
      ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
    by (auto simp: wpsimps elim!: set_dist_bindE
        split: option.splits prod.splits)
qed


definition
  active_route_ro_absorb_trace_composition_good_actual_query_error_for
  :: "'f staged_adversary \<Rightarrow> prob"
where
  "active_route_ro_absorb_trace_composition_good_actual_query_error_for A =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_trace_composition_good_query_lists)
      adversary_initial_state"


lemma active_route_ro_absorb_trace_composition_good_actual_query_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "active_route_ro_absorb_trace_composition_good_actual_query_error_for A
      \<le> ro_checked_staged_trace_composition_good_actual_query_error budgets"
  unfolding
    active_route_ro_absorb_trace_composition_good_actual_query_error_for_def
  by (rule order_trans[
        OF
          wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
          wp_ro_checked_staged_trace_composition_good_actual_query_bound[
            OF wf controlled nonempty]])

end
end
