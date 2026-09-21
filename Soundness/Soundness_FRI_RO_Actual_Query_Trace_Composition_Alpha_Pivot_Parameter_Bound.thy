(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Parameter_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Parameter_Bound
  imports
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Security_Bound
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Sampled_Bound
    Soundness_FRI_RO_Actual_Query_Obstruction_Bounds
begin

context soundness
begin

definition ro_absorb_checked_staged_trace_composition_parameter_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_absorb_checked_staged_trace_composition_parameter_error budgets =
    hash_collision_budget_value 0
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
    ro_checked_staged_trace_composition_good_actual_query_error budgets +
    trace_sampled_bad_actual_query_parameter_bound budgets +
    ro_absorb_checked_staged_composition_sampled_global_query_error budgets +
    ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
    ro_absorb_checked_staged_trace_composition_prefix_target_error budgets +
    ro_checked_staged_first_root_alpha_pivot_error budgets"

lemma
  wp_ro_absorb_checked_staged_security_with_first_root_acceptance_alpha_pivot_parameter_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> ro_absorb_checked_staged_trace_composition_parameter_error budgets"
proof -
  let ?M =
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      A"
  let ?Collision = "final_hash_collision_event"
  let ?Query =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      ro_actual_query_trace_composition_good_query_lists"
  let ?Trace =
    "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair"
  let ?Composition =
    "ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair"
  let ?TraceTarget =
    "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit"
  let ?CompositionTarget =
    "ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit"
  let ?Alpha =
    "ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent"

  have classified:
      "wp_event ?M accepted adversary_initial_state \<le>
        wp_event ?M
          (\<lambda>out.
            ?Collision out \<or>
            ?Query out \<or>
            ?Trace out \<or>
            ?Composition out \<or>
            ?TraceTarget out \<or>
            ?CompositionTarget out \<or>
            ?Alpha out)
          adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_acceptance_le_clean_trace_composition_obstruction_union[
        OF wf controlled nonempty])

  have union:
      "wp_event ?M
          (\<lambda>out.
            ?Collision out \<or>
            ?Query out \<or>
            ?Trace out \<or>
            ?Composition out \<or>
            ?TraceTarget out \<or>
            ?CompositionTarget out \<or>
            ?Alpha out)
          adversary_initial_state
        \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Query adversary_initial_state +
        wp_event ?M ?Trace adversary_initial_state +
        wp_event ?M ?Composition adversary_initial_state +
        wp_event ?M ?TraceTarget adversary_initial_state +
        wp_event ?M ?CompositionTarget adversary_initial_state +
        wp_event ?M ?Alpha adversary_initial_state"
  proof -
    have
      "wp_event ?M
          (\<lambda>out.
            ?Collision out \<or>
            ?Query out \<or>
            ?Trace out \<or>
            ?Composition out \<or>
            ?TraceTarget out \<or>
            ?CompositionTarget out \<or>
            ?Alpha out)
          adversary_initial_state
        \<le> wp_event ?M ?Collision adversary_initial_state +
          wp_event ?M
            (\<lambda>out.
              ?Query out \<or>
              ?Trace out \<or>
              ?Composition out \<or>
              ?TraceTarget out \<or>
              ?CompositionTarget out \<or>
              ?Alpha out)
            adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
          wp_event ?M
            (\<lambda>out.
              ?Trace out \<or>
              ?Composition out \<or>
              ?TraceTarget out \<or>
              ?CompositionTarget out \<or>
              ?Alpha out)
            adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
          (wp_event ?M ?Trace adversary_initial_state +
            wp_event ?M
              (\<lambda>out.
                ?Composition out \<or>
                ?TraceTarget out \<or>
                ?CompositionTarget out \<or>
                ?Alpha out)
              adversary_initial_state))"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
          (wp_event ?M ?Trace adversary_initial_state +
            (wp_event ?M ?Composition adversary_initial_state +
              wp_event ?M
                (\<lambda>out.
                  ?TraceTarget out \<or>
                  ?CompositionTarget out \<or>
                  ?Alpha out)
                adversary_initial_state)))"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
          (wp_event ?M ?Trace adversary_initial_state +
            (wp_event ?M ?Composition adversary_initial_state +
              (wp_event ?M ?TraceTarget adversary_initial_state +
                wp_event ?M
                  (\<lambda>out. ?CompositionTarget out \<or> ?Alpha out)
                  adversary_initial_state))))"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
          (wp_event ?M ?Trace adversary_initial_state +
            (wp_event ?M ?Composition adversary_initial_state +
              (wp_event ?M ?TraceTarget adversary_initial_state +
                (wp_event ?M ?CompositionTarget adversary_initial_state +
                  wp_event ?M ?Alpha adversary_initial_state)))))"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis
      by (simp add: add.assoc)
  qed

  have collision:
      "wp_event ?M ?Collision adversary_initial_state \<le>
        hash_collision_budget_value 0
          (ro_absorb_checked_staged_security_hash_query_budget_for budgets)"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_final_hash_collision_bound[
        OF wf controlled nonempty])
  have query:
      "wp_event ?M ?Query adversary_initial_state \<le>
        ro_checked_staged_trace_composition_good_actual_query_error budgets"
    using active_route_ro_absorb_trace_composition_good_actual_query_bound[
      OF wf controlled nonempty]
    unfolding
      active_route_ro_absorb_trace_composition_good_actual_query_error_for_def
    .
  have trace:
      "wp_event ?M ?Trace adversary_initial_state \<le>
        trace_sampled_bad_actual_query_parameter_bound budgets"
    using
      active_route_ro_absorb_first_root_trace_sampled_bad_pair_parameter_bound[
        OF wf controlled nonempty]
    unfolding
      active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for_def
    .
  have composition:
      "wp_event ?M ?Composition adversary_initial_state \<le>
        ro_absorb_checked_staged_composition_sampled_global_query_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair_bound[
        OF wf controlled nonempty])
  have trace_target:
      "wp_event ?M ?TraceTarget adversary_initial_state \<le>
        ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_bound[
        OF nonempty wf controlled])
  have composition_target:
      "wp_event ?M ?CompositionTarget adversary_initial_state \<le>
        ro_absorb_checked_staged_trace_composition_prefix_target_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_bound[
        OF nonempty wf controlled])
  have alpha:
      "wp_event ?M ?Alpha adversary_initial_state \<le>
        ro_checked_staged_first_root_alpha_pivot_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent_bound[
        OF false_statement wf controlled nonempty])

  have closed:
      "wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Query adversary_initial_state +
        wp_event ?M ?Trace adversary_initial_state +
        wp_event ?M ?Composition adversary_initial_state +
        wp_event ?M ?TraceTarget adversary_initial_state +
        wp_event ?M ?CompositionTarget adversary_initial_state +
        wp_event ?M ?Alpha adversary_initial_state
      \<le> ro_absorb_checked_staged_trace_composition_parameter_error budgets"
    unfolding
      ro_absorb_checked_staged_trace_composition_parameter_error_def
    by (intro add_mono collision query trace composition trace_target
        composition_target alpha)
  show ?thesis
    by (rule order_trans[OF classified order_trans[OF union closed]])
qed


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_acceptance_eq:
  assumes nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      =
      wp_event
        (ro_absorb_checked_staged_security_experiment A)
        accepted adversary_initial_state"
proof -
  let ?project =
    "\<lambda>(((prefix_with_state, data, query_start, raws, query_states),
          attacker_state), result).
      (((data, query_start, raws, query_states), attacker_state), result)"
  have event_map:
      "(\<lambda>out. case out of
        None \<Rightarrow> accepted None
      | Some (x, t) \<Rightarrow> accepted (Some (?project x, t))) = accepted"
    unfolding accepted_def
    by (rule ext) (auto split: option.splits prod.splits)
  have mapped:
      "wp_event
          (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A \<bind>
            (\<lambda>x. return (?project x)))
          accepted adversary_initial_state
        =
        wp_event
          (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A)
          accepted adversary_initial_state"
    by (subst wp_event_bind_return_map) (simp only: event_map)
  have projection:
      "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A \<bind>
          (\<lambda>x. return (?project x))
        =
        ro_absorb_checked_staged_security_experiment_with_query_witnesses A"
    using
      ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection[
        OF nonempty, of A]
    by (simp add: split_def)
  have first_eq:
      "wp_event
          (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A)
          accepted adversary_initial_state
        =
        wp_event
          (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
          accepted adversary_initial_state"
    using mapped unfolding projection by simp
  have witnesses_eq:
      "wp_event
          (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
          accepted adversary_initial_state
        =
        wp_event
          (ro_absorb_checked_staged_security_experiment_with_data_state A)
          accepted adversary_initial_state"
    by (rule
      ro_absorb_checked_staged_security_experiment_with_query_witnesses_acceptance_eq_data_state)
  have data_eq:
      "wp_event
          (ro_absorb_checked_staged_security_experiment A)
          accepted adversary_initial_state
        =
        wp_event
          (ro_absorb_checked_staged_security_experiment_with_data_state A)
          accepted adversary_initial_state"
    by (rule
      ro_absorb_checked_staged_security_experiment_acceptance_with_data_state)
  show ?thesis
    using first_eq witnesses_eq data_eq by simp
qed

theorem ro_absorb_stark_soundness_nonempty:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A
      \<le> ro_absorb_checked_staged_trace_composition_parameter_error budgets"
proof -
  have bound:
      "wp_event
          (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A)
          accepted adversary_initial_state
        \<le> ro_absorb_checked_staged_trace_composition_parameter_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_acceptance_alpha_pivot_parameter_bound[
        OF false_statement wf controlled nonempty])
  have projection:
      "wp_event
          (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A)
          accepted adversary_initial_state
        =
        wp_event
          (ro_absorb_checked_staged_security_experiment A)
          accepted adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_acceptance_eq[
        OF nonempty])
  show ?thesis
    using bound projection
    unfolding ro_absorb_checked_staged_adversary_acceptance_probability_def
      accepted_def
    by simp
qed

end
end
