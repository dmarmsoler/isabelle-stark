(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Closed_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Closed_Bound
  imports
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Outcome_Bridge
begin

context soundness
begin

definition
  ro_checked_staged_first_root_trace_composition_all_queries_consistent
where
  "ro_checked_staged_first_root_trace_composition_all_queries_consistent
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        trace_table_low_degree
          (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
        composition_table_low_degree maxDegree
          (ro_actual_query_composition_candidate data query_start) \<and>
        all_queries_consistent
          (first_trace_fri_root_prefix_first_table prefix prefix_state)
          (ro_actual_query_composition_candidate data query_start)
          (staged_alphas data))"


definition
  ro_checked_staged_first_root_alpha_pivot_side_event
where
  "ro_checked_staged_first_root_alpha_pivot_side_event budgets out \<longleftrightarrow>
    final_hash_collision_event out \<or>
    hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state out \<or>
    ro_checked_staged_first_root_prefix_merkle_target_hit out \<or>
    hash_state_relation_transition_event
      (alpha_pivot_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state) out"


definition ro_checked_staged_first_root_alpha_pivot_error
where
  "ro_checked_staged_first_root_alpha_pivot_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in hash_collision_budget_value 0 q +
       nnreal q / nnreal size +
       ro_checked_staged_first_root_prefix_merkle_target_error budgets +
       nnreal (q * (1 + (6 * q + 2))) / nnreal size)"


lemma
  ro_checked_staged_first_root_all_queries_consistent_some_imp_alpha_pivot_side_event:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and all_consistent:
      "ro_checked_staged_first_root_trace_composition_all_queries_consistent
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
  shows
    "ro_checked_staged_first_root_alpha_pivot_side_event budgets
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
proof -
  have low_and_consistent:
      "trace_table_low_degree
          (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
       composition_table_low_degree maxDegree
          (ro_actual_query_composition_candidate data query_start) \<and>
       all_queries_consistent
          (first_trace_fri_root_prefix_first_table prefix prefix_state)
          (ro_actual_query_composition_candidate data query_start)
          (staged_alphas data)"
    using all_consistent
    unfolding
      ro_checked_staged_first_root_trace_composition_all_queries_consistent_def
    by simp
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome[
        OF nonempty outcome])
  have alpha_len: "length (staged_alphas data) = length spec"
    using ro_checked_staged_transcript_program_outcome_shape[
      OF original_out]
    by blast
  have as_bad:
      "staged_alphas data \<in>
        composition_trace_bad_alpha_space
          (first_trace_fri_root_prefix_first_table prefix prefix_state)"
    by (rule
      low_degree_all_queries_consistent_imp_composition_trace_bad_alpha_space[
        OF false_statement alpha_len])
      (use low_and_consistent in blast)+

  show ?thesis
  proof (cases "hash_map_output_collision attacker_state")
    case True
    then show ?thesis
      unfolding ro_checked_staged_first_root_alpha_pivot_side_event_def
        final_hash_collision_event_def
      by simp
  next
    case clean: False
    show ?thesis
    proof (cases
        "PState adversary_initial_state \<in>
          hash_map_output_values attacker_state")
      case True
      then obtain x where final_lookup:
          "fmlookup (HashMap attacker_state) x =
            Some (PState adversary_initial_state)"
        unfolding hash_map_output_values_def by blast
      have initial_lookup:
          "fmlookup (HashMap adversary_initial_state) x = None"
        unfolding adversary_initial_state_def by simp
      have initial_hit:
          "hash_map_new_output_hit {PState adversary_initial_state}
            adversary_initial_state attacker_state"
        unfolding hash_map_new_output_hit_def
        using initial_lookup final_lookup by blast
      then show ?thesis
        unfolding ro_checked_staged_first_root_alpha_pivot_side_event_def
          hash_new_output_hit_event_def
        by simp
    next
      case no_initial: False
      show ?thesis
      proof (cases
          "hash_map_new_output_hit
            (first_trace_fri_root_prefix_merkle_targets
              prefix prefix_state)
            prefix_state attacker_state")
        case True
        then show ?thesis
          unfolding ro_checked_staged_first_root_alpha_pivot_side_event_def
            ro_checked_staged_first_root_prefix_merkle_target_hit_def
          by simp
      next
        case no_merkle: False
        have relation:
            "hash_state_relation_transition
              (alpha_pivot_absorbed_query_relation_bounded
                (ro_checked_staged_transcript_hash_query_budget_for budgets))
              (HashMap adversary_initial_state)
              (HashMap attacker_state)"
          by (rule
            trace_composition_bad_alpha_imp_alpha_pivot_relation_transition[
              OF wf controlled nonempty outcome clean no_initial no_merkle
                as_bad])
        then show ?thesis
          unfolding ro_checked_staged_first_root_alpha_pivot_side_event_def
            hash_state_relation_transition_event_def
          by simp
      qed
    qed
  qed
qed


lemma
  ro_checked_staged_first_root_all_queries_consistent_imp_alpha_pivot_side_event:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and all_consistent:
      "ro_checked_staged_first_root_trace_composition_all_queries_consistent out"
  shows
    "ro_checked_staged_first_root_alpha_pivot_side_event budgets out"
proof (cases out)
  case None
  then show ?thesis
    using all_consistent
    unfolding
      ro_checked_staged_first_root_trace_composition_all_queries_consistent_def
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
  have all_consistent':
    "ro_checked_staged_first_root_trace_composition_all_queries_consistent
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
    using all_consistent unfolding Some packed_eq .
  have side:
    "ro_checked_staged_first_root_alpha_pivot_side_event budgets
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
    by (rule
      ro_checked_staged_first_root_all_queries_consistent_some_imp_alpha_pivot_side_event[
        OF false_statement wf controlled nonempty outcome all_consistent'])
  show ?thesis
    using side unfolding Some packed_eq .
qed


lemma wp_ro_checked_staged_first_root_all_queries_consistent_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_first_root_trace_composition_all_queries_consistent
      adversary_initial_state
    \<le> ro_checked_staged_first_root_alpha_pivot_error budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?All =
    "ro_checked_staged_first_root_trace_composition_all_queries_consistent"
  let ?Collision = "final_hash_collision_event"
  let ?Initial =
    "hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state"
  let ?Merkle = "ro_checked_staged_first_root_prefix_merkle_target_hit"
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?Relation =
    "hash_state_relation_transition_event
      (alpha_pivot_absorbed_query_relation_bounded ?q)
      (HashMap adversary_initial_state)"
  have event_le:
    "wp_event ?M ?All adversary_initial_state \<le>
      wp_event ?M
        (ro_checked_staged_first_root_alpha_pivot_side_event budgets)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and all_consistent: "?All out"
    show "ro_checked_staged_first_root_alpha_pivot_side_event budgets out"
      by (rule
        ro_checked_staged_first_root_all_queries_consistent_imp_alpha_pivot_side_event[
          OF false_statement wf controlled nonempty support all_consistent])
  qed
  have union:
    "wp_event ?M
        (ro_checked_staged_first_root_alpha_pivot_side_event budgets)
        adversary_initial_state
      \<le> wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Initial adversary_initial_state +
        wp_event ?M ?Merkle adversary_initial_state +
        wp_event ?M ?Relation adversary_initial_state"
    unfolding ro_checked_staged_first_root_alpha_pivot_side_event_def
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
      nnreal (?q * (1 + (6 * ?q + 2))) / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_alpha_pivot_bounded_relation[
        OF wf controlled nonempty])
  have closed:
    "wp_event ?M
        (ro_checked_staged_first_root_alpha_pivot_side_event budgets)
        adversary_initial_state
      \<le> ro_checked_staged_first_root_alpha_pivot_error budgets"
    apply (rule order_trans[OF union])
    unfolding ro_checked_staged_first_root_alpha_pivot_error_def Let_def
    apply (intro add_mono)
       apply (rule collision)
      apply (rule initial)
     apply (rule merkle)
    apply (rule relation)
    done
  show ?thesis
    by (rule order_trans[OF event_le closed])
qed


end
end
