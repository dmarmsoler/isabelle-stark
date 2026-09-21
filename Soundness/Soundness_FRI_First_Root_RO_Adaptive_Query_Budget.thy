(*  Title:      Stark/Soundness_FRI_First_Root_RO_Adaptive_Query_Budget.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_Adaptive_Query_Budget
  imports
    Soundness_FRI_First_Root_RO_Bounded_State_Relation
    Staged_Security_Experiment_RO_Transcript_Adaptive_State_Relation
begin

text \<open>
  The proof-only first-root/query witnesses preserve the exact final hash map,
  so the adaptive transcript query budget transfers through both projections.
\<close>

context soundness
begin

lemma adaptive_hash_query_budget_ro_checked_staged_transcript_program_with_query_witnesses:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "adaptive_hash_query_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets)
      (ro_checked_staged_transcript_program_with_query_witnesses A)"
proof (rule adaptive_hash_query_budget_of_projection[
    where project="\<lambda>(data, query_start, raws, query_states). data"])
  show
    "ro_checked_staged_transcript_program_with_query_witnesses A \<bind>
        (\<lambda>x. return
          ((\<lambda>(data, query_start, raws, query_states). data) x)) =
      ro_checked_staged_transcript_program A"
    using ro_checked_staged_transcript_program_with_query_witnesses_projection[
      of A]
    by (simp add: split_def)
  show
    "adaptive_hash_query_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets)
      (ro_checked_staged_transcript_program A)"
    by (rule adaptive_hash_query_budget_ro_checked_staged_transcript_program[
      OF wf controlled])
qed

lemma adaptive_hash_query_budget_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "adaptive_hash_query_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets)
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)"
proof (rule adaptive_hash_query_budget_of_projection[
    where project=
      "\<lambda>(prefix_with_state, data, query_start, raws, query_states).
        (data, query_start, raws, query_states)"])
  show
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A \<bind>
        (\<lambda>x. return
          ((\<lambda>(prefix_with_state, data, query_start, raws, query_states).
              (data, query_start, raws, query_states)) x)) =
      ro_checked_staged_transcript_program_with_query_witnesses A"
    using
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_projection[
        OF nonempty, of A]
    by (simp add: split_def)
  show
    "adaptive_hash_query_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets)
      (ro_checked_staged_transcript_program_with_query_witnesses A)"
    by (rule
      adaptive_hash_query_budget_ro_checked_staged_transcript_program_with_query_witnesses[
        OF wf controlled])
qed

lemma adaptive_hash_query_budget_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_all_rounds:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "adaptive_hash_query_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets)
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)"
proof (rule adaptive_hash_query_budget_of_projection[
    where project=
      "\<lambda>(prefix_with_state, data, query_start, raws, query_states).
        (data, query_start, raws, query_states)"])
  show
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A \<bind>
        (\<lambda>x. return
          ((\<lambda>(prefix_with_state, data, query_start, raws, query_states).
              (data, query_start, raws, query_states)) x)) =
      ro_checked_staged_transcript_program_with_query_witnesses A"
    using
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_projection_all_rounds[
        of A]
    by (simp add: split_def)
  show
    "adaptive_hash_query_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets)
      (ro_checked_staged_transcript_program_with_query_witnesses A)"
    by (rule
      adaptive_hash_query_budget_ro_checked_staged_transcript_program_with_query_witnesses[
        OF wf controlled])
qed


lemma wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_adaptive_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event R
          (HashMap adversary_initial_state))
        adversary_initial_state
      \<le>
      nnreal
        (ro_checked_staged_transcript_hash_query_budget_for budgets * b) /
        nnreal size"
proof -
  have adaptive:
    "adaptive_hash_query_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets)
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)"
    by (rule
      adaptive_hash_query_budget_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses[
        OF wf controlled nonempty])
  have budget:
    "hash_state_relation_budget R b
      (ro_checked_staged_transcript_hash_query_budget_for budgets)
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)"
    using adaptive steps
    unfolding adaptive_hash_query_budget_def
    by blast
  show ?thesis
    using budget
    unfolding hash_state_relation_budget_def
      hash_relation_budget_value_def
    by blast
qed

lemma wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_adaptive_relation_bound_all_rounds:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and steps:
      "\<And>M x. fmlookup M x = None \<Longrightarrow>
        card {y.
          hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event R
          (HashMap adversary_initial_state))
        adversary_initial_state
      \<le>
      nnreal
        (ro_checked_staged_transcript_hash_query_budget_for budgets * b) /
        nnreal size"
proof -
  have adaptive:
    "adaptive_hash_query_budget
      (ro_checked_staged_transcript_hash_query_budget_for budgets)
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)"
    by (rule
      adaptive_hash_query_budget_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_all_rounds[
        OF wf controlled])
  have budget:
    "hash_state_relation_budget R b
      (ro_checked_staged_transcript_hash_query_budget_for budgets)
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)"
    using adaptive steps
    unfolding adaptive_hash_query_budget_def
    by blast
  show ?thesis
    using budget
    unfolding hash_state_relation_budget_def
      hash_relation_budget_value_def
    by blast
qed


lemma wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_first_root_bounded_relation:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  defines
    "q \<equiv> ro_checked_staged_transcript_hash_query_budget_for budgets"
  shows
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (first_root_absorbed_query_relation_bounded q)
          (HashMap adversary_initial_state))
        adversary_initial_state
      \<le>
      nnreal
        (q *
          (rounds * query_raw_preimage_card_envelope clength +
            (5 * q + 2))) /
        nnreal size"
proof -
  let ?Q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?B =
    "rounds * query_raw_preimage_card_envelope clength +
      (5 * ?Q + 2)"
  have steps:
    "\<And>M x. fmlookup M x = None \<Longrightarrow>
      card {y.
        hash_state_relation_transition
          (first_root_absorbed_query_relation_bounded ?Q)
          M (fmupd x y M)}
        \<le> ?B"
    by (rule first_root_bounded_transition_fiber_card_bound)
  have bound:
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (hash_state_relation_transition_event
          (first_root_absorbed_query_relation_bounded ?Q)
          (HashMap adversary_initial_state))
        adversary_initial_state
      \<le> nnreal (?Q * ?B) / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_adaptive_relation_bound[
        OF wf controlled nonempty steps])
  show ?thesis
    using bound
    unfolding q_def
    by simp
qed

end
end
