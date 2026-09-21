(*  Title:      Stark/Soundness_FRI_First_Root_RO_Security_Query_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_Security_Query_Bound
  imports
    Soundness_FRI_First_Root_RO_Prequery_Closed_Bound
    Staged_Security_Experiment_RO_Query_List_Actual_Path
begin

text \<open>
  Carries the first trace-FRI-root prefix and actual query witnesses through
  the domain-separated absorbing verifier experiment.  The extra components
  are ghost data: the projection theorem below erases them and recovers the
  existing absorbing security experiment.
\<close>

context soundness
begin

definition
  ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
where
  "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A =
    do {
      (prefix_with_state, data, query_start, raws, query_states) \<leftarrow>
        ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A;
      attacker_state \<leftarrow> get;
      put
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data));
      result \<leftarrow> ro_verify_monad;
      return
        (((prefix_with_state, data, query_start, raws, query_states),
            attacker_state), result)
    }"

lemma
  ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection:
  assumes nonempty: "0 < ceil_log clength"
  shows
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A \<bind>
      (\<lambda>(((prefix_with_state, data, query_start, raws, query_states),
            attacker_state), result).
        return
          (((data, query_start, raws, query_states), attacker_state), result)) =
    ro_absorb_checked_staged_security_experiment_with_query_witnesses A"
proof -
  have projection':
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A \<bind>
        (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
          return (data, query_start, raws, query_states)) =
      ro_checked_staged_transcript_program_with_query_witnesses A"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_projection[
        OF nonempty])
  let ?K =
    "\<lambda>(data, query_start, raws, query_states).
      get \<bind> (\<lambda>attacker_state.
        put
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) \<bind>
        (\<lambda>_. ro_verify_monad \<bind>
          (\<lambda>result.
            return
              (((data, query_start, raws, query_states), attacker_state),
                result))))"
  have
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A \<bind>
        (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
          ?K (data, query_start, raws, query_states)) =
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A \<bind>
        (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
          return (data, query_start, raws, query_states))) \<bind> ?K"
    by (simp add: sm_bind_assoc split_def)
  also have "... =
      ro_checked_staged_transcript_program_with_query_witnesses A \<bind> ?K"
    by (simp only: projection')
  finally show ?thesis
    unfolding
      ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
      ro_absorb_checked_staged_security_experiment_with_query_witnesses_def
    by (simp add: sm_bind_assoc split_def)
qed

lemma
  ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection_all_rounds:
  "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A \<bind>
    (\<lambda>(((prefix_with_state, data, query_start, raws, query_states),
          attacker_state), result).
      return
        (((data, query_start, raws, query_states), attacker_state), result)) =
  ro_absorb_checked_staged_security_experiment_with_query_witnesses A"
proof -
  have projection':
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A \<bind>
        (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
          return (data, query_start, raws, query_states)) =
      ro_checked_staged_transcript_program_with_query_witnesses A"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_projection_all_rounds)
  let ?K =
    "\<lambda>(data, query_start, raws, query_states).
      get \<bind> (\<lambda>attacker_state.
        put
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) \<bind>
        (\<lambda>_. ro_verify_monad \<bind>
          (\<lambda>result.
            return
              (((data, query_start, raws, query_states), attacker_state),
                result))))"
  have
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A \<bind>
        (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
          ?K (data, query_start, raws, query_states)) =
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A \<bind>
        (\<lambda>(prefix_with_state, data, query_start, raws, query_states).
          return (data, query_start, raws, query_states))) \<bind> ?K"
    by (simp add: sm_bind_assoc split_def)
  also have "... =
      ro_checked_staged_transcript_program_with_query_witnesses A \<bind> ?K"
    by (simp only: projection')
  finally show ?thesis
    unfolding
      ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
      ro_absorb_checked_staged_security_experiment_with_query_witnesses_def
    by (simp add: sm_bind_assoc split_def)
qed

definition
  ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
where
  "ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
      Q out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix_with_state, data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        ro_checked_staged_first_root_dependent_actual_query_index_list_hit Q
          (Some
            ((prefix_with_state, data, query_start, raws, query_states),
              attacker_state)))"

lemma
  wp_ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit_le:
  "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      (ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
        Q)
      s
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_checked_staged_first_root_dependent_actual_query_index_list_hit Q)
      s"
  unfolding
    ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
proof (rule wp_event_bind_bound_by_head_event)
  show
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_checked_staged_first_root_dependent_actual_query_index_list_hit Q)
      s
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_checked_staged_first_root_dependent_actual_query_index_list_hit Q)
      s"
    by simp
next
  show
    "ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
        Q None \<Longrightarrow>
      ro_checked_staged_first_root_dependent_actual_query_index_list_hit Q None"
    unfolding
      ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit_def
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
      "ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
        Q out"
  show
    "ro_checked_staged_first_root_dependent_actual_query_index_list_hit
      Q (Some (x, t))"
    using tail hit
    unfolding x_eq
      ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit_def
    by (auto simp: wpsimps elim!: set_dist_bindE
        split: option.splits prod.splits)
qed

definition active_route_ro_absorb_first_root_good_actual_query_error_for
  :: "'f staged_adversary \<Rightarrow> prob"
where
  "active_route_ro_absorb_first_root_good_actual_query_error_for A =
    wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      (ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
        first_trace_fri_root_prefix_good_agreement_query_lists)
      adversary_initial_state"

(* The security-level good-query bound feeds the RO verifier evidence layer below. *)
lemma active_route_ro_absorb_first_root_good_actual_query_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "active_route_ro_absorb_first_root_good_actual_query_error_for A
      \<le> ro_checked_staged_first_root_good_actual_query_error budgets"
  unfolding active_route_ro_absorb_first_root_good_actual_query_error_for_def
  by (rule order_trans[
        OF
          wp_ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit_le
          wp_ro_checked_staged_first_root_good_actual_query_bound[
            OF wf controlled nonempty]])

end
end
