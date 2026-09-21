(*  Title:      Stark/Soundness_FRI_First_Root_RO_Prequery_Closed_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_Prequery_Closed_Bound
  imports Soundness_FRI_First_Root_RO_Prefix_Target_Bound
begin

text \<open>
  The semantic prequery event is reduced to four parameter-bounded random-oracle
  side events.  This layer keeps the exact fresh-query product separate; it
  closes only the pre-existing-state branch of the actual-query split.
\<close>

context soundness
begin


definition ro_checked_staged_first_root_good_prequery_side_event
  :: "staged_budgets \<Rightarrow>
      (((('f \<times> 'f list \<times> 'f) \<times> 'f protocol_channel) \<times>
        'f staged_proof_data \<times> 'f protocol_channel \<times>
        'f list \<times> 'f protocol_channel list) \<times> 'f protocol_channel) option \<Rightarrow>
      bool"
where
  "ro_checked_staged_first_root_good_prequery_side_event budgets out \<longleftrightarrow>
    final_hash_collision_event out \<or>
    hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state out \<or>
    ro_checked_staged_first_root_prefix_merkle_target_hit out \<or>
    hash_state_relation_transition_event
      (first_root_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state) out"


lemma ro_checked_staged_first_root_good_prequery_imp_side_event:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and prequery:
      "ro_checked_staged_first_root_dependent_query_start_prequery_hit
        first_trace_fri_root_prefix_good_agreement_query_lists out"
  shows
    "ro_checked_staged_first_root_good_prequery_side_event budgets out"
proof (cases out)
  case None
  then show ?thesis
    using prequery
    unfolding
      ro_checked_staged_first_root_dependent_query_start_prequery_hit_def
    by simp
next
  case (Some packed)
  obtain prefix prefix_state data query_start raws query_states
      attacker_state where packed_eq:
    "packed =
      (((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)"
    by (cases packed) (auto split: prod.splits)
  have outcome:
    "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)) \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          adversary_initial_state)"
    using support unfolding Some packed_eq .
  have prequery':
    "ro_checked_staged_first_root_dependent_query_start_prequery_hit
      first_trace_fri_root_prefix_good_agreement_query_lists
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
    using prequery unfolding Some packed_eq .
  have side:
    "final_hash_collision_event
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state))) \<or>
      hash_new_output_hit_event {PState adversary_initial_state}
        adversary_initial_state
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state))) \<or>
      ro_checked_staged_first_root_prefix_merkle_target_hit
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state))) \<or>
      hash_state_relation_transition_event
        (first_root_absorbed_query_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets))
        (HashMap adversary_initial_state)
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
    by (rule ro_checked_staged_first_root_good_prequery_some_imp_side_event[
      OF wf controlled nonempty outcome prequery'])
  show ?thesis
    using side
    unfolding ro_checked_staged_first_root_good_prequery_side_event_def
      Some packed_eq .
qed


definition ro_checked_staged_first_root_good_prequery_error
  :: "staged_budgets \<Rightarrow> prob" where
  "ro_checked_staged_first_root_good_prequery_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in hash_collision_budget_value 0 q +
       nnreal q / nnreal size +
       ro_checked_staged_first_root_prefix_merkle_target_error budgets +
       nnreal
         (q *
           (rounds * query_raw_preimage_card_envelope clength +
             (5 * q + 2))) /
         nnreal size)"


lemma wp_ro_checked_staged_first_root_good_prequery_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_checked_staged_first_root_dependent_query_start_prequery_hit
        first_trace_fri_root_prefix_good_agreement_query_lists)
      adversary_initial_state
    \<le> ro_checked_staged_first_root_good_prequery_error budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?Prequery =
    "ro_checked_staged_first_root_dependent_query_start_prequery_hit
      first_trace_fri_root_prefix_good_agreement_query_lists"
  let ?Collision = "final_hash_collision_event"
  let ?Initial =
    "hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state"
  let ?Merkle = "ro_checked_staged_first_root_prefix_merkle_target_hit"
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?Relation =
    "hash_state_relation_transition_event
      (first_root_absorbed_query_relation_bounded ?q)
      (HashMap adversary_initial_state)"
  have event_le:
    "wp_event ?M ?Prequery adversary_initial_state \<le>
      wp_event ?M
        (ro_checked_staged_first_root_good_prequery_side_event budgets)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and prequery: "?Prequery out"
    show "ro_checked_staged_first_root_good_prequery_side_event budgets out"
      by (rule ro_checked_staged_first_root_good_prequery_imp_side_event[
        OF wf controlled nonempty support prequery])
  qed
  have union:
    "wp_event ?M
        (ro_checked_staged_first_root_good_prequery_side_event budgets)
        adversary_initial_state
      \<le> wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Initial adversary_initial_state +
        wp_event ?M ?Merkle adversary_initial_state +
        wp_event ?M ?Relation adversary_initial_state"
    unfolding ro_checked_staged_first_root_good_prequery_side_event_def
    by (rule wp_event_union_bound4)
  have collision:
    "wp_event ?M ?Collision adversary_initial_state \<le>
      hash_collision_budget_value 0 ?q"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_collision_bound[
        OF wf controlled nonempty])
  have initial:
    "wp_event ?M ?Initial adversary_initial_state \<le>
      nnreal ?q / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_initial_target_bound[
        OF wf controlled nonempty])
  have merkle:
    "wp_event ?M ?Merkle adversary_initial_state \<le>
      ro_checked_staged_first_root_prefix_merkle_target_error budgets"
    by (rule
      wp_ro_checked_staged_first_root_prefix_merkle_target_hit_bound[
        OF nonempty wf controlled])
  have relation:
    "wp_event ?M ?Relation adversary_initial_state \<le>
      nnreal
        (?q *
          (rounds * query_raw_preimage_card_envelope clength +
            (5 * ?q + 2))) /
        nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_first_root_bounded_relation[
        OF wf controlled nonempty])
  have closed:
    "wp_event ?M
        (ro_checked_staged_first_root_good_prequery_side_event budgets)
        adversary_initial_state
      \<le> ro_checked_staged_first_root_good_prequery_error budgets"
    apply (rule order_trans[OF union])
    unfolding ro_checked_staged_first_root_good_prequery_error_def Let_def
    apply (intro add_mono)
       apply (rule collision)
      apply (rule initial)
     apply (rule merkle)
    apply (rule relation)
    done
  show ?thesis
    by (rule order_trans[OF event_le closed])
qed


lemma ro_checked_staged_first_root_query_head_program_output_lengths:
  assumes nonempty: "0 < ceil_log clength"
    and outcome:
      "Some (((prefix, prefix_state), data, query_start), t) \<in>
        set_dist
          (execute (ro_checked_staged_first_root_query_head_program A) s)"
  shows
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
      length (staged_composition_fri_roots data) \<le>
        ceil_log (maxDegree + 1)"
proof -
  from outcome obtain prefix_final where
    after:
      "Some (data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              prefix)
            prefix_final)"
    unfolding ro_checked_staged_first_root_query_head_program_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  obtain fr trace_bs first_root where prefix_eq:
    "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  show ?thesis
    by (rule
      ro_checked_staged_after_first_trace_fri_root_prefix_program_output_lengths[
        OF nonempty])
      (use after prefix_eq in simp)
qed


lemma wp_ro_checked_staged_first_root_good_query_phase_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_checked_staged_first_root_dependent_query_phase_relation_hit A
        first_trace_fri_root_prefix_good_agreement_query_lists)
      adversary_initial_state
    \<le> hash_relation_budget_value
      (rounds * query_raw_preimage_card_envelope clength)
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)"
proof (rule
    wp_ro_checked_staged_first_root_dependent_query_phase_relation_hit_bound[
      OF wf controlled])
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "query_index_raw_list_relation_fiber_bound
        (first_trace_fri_root_prefix_good_agreement_query_lists
          prefix prefix_state)
      \<le> rounds * query_raw_preimage_card_envelope clength"
    by (rule first_trace_fri_root_prefix_good_agreement_relation_fiber_bound)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show "length (staged_trace_fri_roots data) = ceil_log clength"
    using ro_checked_staged_first_root_query_head_program_output_lengths[
      OF nonempty head]
    by blast
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "length (staged_composition_fri_roots data) \<le>
      ceil_log (maxDegree + 1)"
    using ro_checked_staged_first_root_query_head_program_output_lengths[
      OF nonempty head]
    by blast
qed


definition ro_checked_staged_first_root_good_actual_query_error
  :: "staged_budgets \<Rightarrow> prob" where
  "ro_checked_staged_first_root_good_actual_query_error budgets =
    nnreal (clength ^ rounds) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds +
    ro_checked_staged_first_root_good_prequery_error budgets +
    hash_relation_budget_value
      (rounds * query_raw_preimage_card_envelope clength)
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)"


lemma wp_ro_checked_staged_first_root_good_actual_query_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_checked_staged_first_root_dependent_actual_query_index_list_hit
        first_trace_fri_root_prefix_good_agreement_query_lists)
      adversary_initial_state
    \<le> ro_checked_staged_first_root_good_actual_query_error budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?Q = "first_trace_fri_root_prefix_good_agreement_query_lists"
  let ?Fresh =
    "ro_checked_staged_first_root_dependent_query_index_list_fresh_hit ?Q"
  let ?Prequery =
    "ro_checked_staged_first_root_dependent_query_start_prequery_hit ?Q"
  let ?Relation =
    "ro_checked_staged_first_root_dependent_query_phase_relation_hit A ?Q"
  have split:
    "wp_event ?M
        (ro_checked_staged_first_root_dependent_actual_query_index_list_hit ?Q)
        adversary_initial_state
      \<le> wp_event ?M ?Fresh adversary_initial_state +
        wp_event ?M ?Prequery adversary_initial_state +
        wp_event ?M ?Relation adversary_initial_state"
    by (rule
      wp_ro_checked_staged_first_root_dependent_actual_query_index_list_hit_split[
        OF wf controlled])
  have fresh:
    "wp_event ?M ?Fresh adversary_initial_state \<le>
      nnreal (clength ^ rounds) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_good_agreement_fresh_bound)
  have prequery:
    "wp_event ?M ?Prequery adversary_initial_state \<le>
      ro_checked_staged_first_root_good_prequery_error budgets"
    by (rule wp_ro_checked_staged_first_root_good_prequery_bound[
      OF wf controlled nonempty])
  have relation:
    "wp_event ?M ?Relation adversary_initial_state \<le>
      hash_relation_budget_value
        (rounds * query_raw_preimage_card_envelope clength)
        (sum_list (query_opening_budgets budgets) + rounds +
          rounds * ro_checked_query_round_transcript_bound)"
    by (rule
      wp_ro_checked_staged_first_root_good_query_phase_relation_bound[
        OF wf controlled nonempty])
  show ?thesis
    by (rule order_trans[OF split])
      (use fresh prequery relation in
        \<open>simp add:
          ro_checked_staged_first_root_good_actual_query_error_def
          add_mono\<close>)
qed


end
end
