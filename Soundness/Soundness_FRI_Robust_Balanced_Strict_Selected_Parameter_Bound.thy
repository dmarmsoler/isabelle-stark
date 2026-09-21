theory Soundness_FRI_Robust_Balanced_Strict_Selected_Parameter_Bound
  imports
    Stark.Soundness_FRI_Robust_Balanced_Parameter_Bound
    Stark.Soundness_FRI_Robust_Balanced_Strict_Selected_Security_Classification
    Stark.Soundness_FRI_Robust_Balanced_Strict_Selected_Actual_Query
begin

context soundness
begin

definition ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error
  :: "nat \<Rightarrow> staged_budgets \<Rightarrow> prob"
where
  "ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets =
    hash_collision_budget_value 0
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
    ro_checked_staged_balanced_decoded_semantic_rectangle_error_adaptive
      C budgets +
    ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
    ro_absorb_checked_staged_trace_composition_prefix_target_error budgets +
    ro_absorb_checked_staged_fri_builder_merkle_target_error budgets +
    ro_checked_staged_conditioned_initial_target_error budgets +
    ro_checked_staged_balanced_trace_challenge_error C budgets +
    ro_checked_staged_balanced_composition_challenge_error C budgets +
    ro_checked_staged_balanced_strict_selected_combined_actual_residual_rectangle_error_adaptive
      C budgets +
    ro_checked_staged_conditioned_residual_query_phase_target_error budgets +
    ro_checked_staged_first_root_robust_alpha_pivot_error budgets"

lemma
  wp_ro_absorb_checked_staged_security_combined_balanced_strict_selected_residual_actual_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        (fri_balanced_strict_selected_combined_query_head_lists C))
      adversary_initial_state
    \<le> ro_checked_staged_balanced_strict_selected_combined_actual_residual_rectangle_error_adaptive
      C budgets"
  by (rule order_trans[
      OF
        wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
        wp_ro_checked_staged_combined_balanced_strict_selected_residual_actual_rectangle_bound_adaptive[
          OF wf controlled eval_power trace_rounds_fit
            composition_rounds_fit]])

lemma
  wp_ro_absorb_checked_staged_security_acceptance_balanced_strict_selected_nonempty_parameter_bound_exact_two:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and trace_exact:
      "fri_balanced_exact_list_cap
        (clength - 1) (ceil_log clength) C 2"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_balanced_exact_list_cap d (ceil_log (Suc d)) C 2"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets"
proof -
  let ?M =
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      A"
  let ?Collision = "final_hash_collision_event"
  let ?Query =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      (ro_balanced_decoded_semantic_query_lists C)"
  let ?TraceTarget =
    "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit"
  let ?CompositionTarget =
    "ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit"
  let ?BuilderTarget =
    "ro_absorb_checked_staged_security_clean_builder_merkle_target_hit"
  let ?Initial =
    "ro_absorb_checked_staged_security_builder_initial_target_hit"
  let ?TraceChallenge =
    "ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        (balanced_conditioned_trace_fri_bad_challenge_relation C))"
  let ?CompositionChallenge =
    "ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        (balanced_conditioned_composition_fri_bad_challenge_relation C))"
  let ?ActualResidual =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      (fri_balanced_strict_selected_combined_query_head_lists C)"
  let ?QueryPhaseTarget =
    "ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit"
  let ?Alpha =
    "ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent"

  have classified:
      "wp_event ?M accepted adversary_initial_state \<le>
        wp_event ?M
          (ro_absorb_checked_staged_balanced_strict_selected_obstruction_union C budgets)
          adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_le_robust_obstruction_union_balanced_strict_selected_exact_two[
        OF wf controlled nonempty eval_power trace_rounds_fit
          composition_rounds_fit trace_exact composition_exact])

  have union:
      "wp_event ?M
          (ro_absorb_checked_staged_balanced_strict_selected_obstruction_union C budgets)
          adversary_initial_state
        \<le>
        wp_event ?M ?Collision adversary_initial_state +

        wp_event ?M ?Query adversary_initial_state +
        wp_event ?M ?TraceTarget adversary_initial_state +
        wp_event ?M ?CompositionTarget adversary_initial_state +
        wp_event ?M ?BuilderTarget adversary_initial_state +
        wp_event ?M ?Initial adversary_initial_state +
        wp_event ?M ?TraceChallenge adversary_initial_state +
        wp_event ?M ?CompositionChallenge adversary_initial_state +
        wp_event ?M ?ActualResidual adversary_initial_state +
        wp_event ?M ?QueryPhaseTarget adversary_initial_state +
        wp_event ?M ?Alpha adversary_initial_state"
  proof -
    have
        "wp_event ?M
            (\<lambda>out.
              ?Collision out \<or>
              ?Query out \<or>
              ?TraceTarget out \<or>
              (?CompositionTarget out \<or>
               ?BuilderTarget out \<or>
               ?Initial out \<or>
               ?TraceChallenge out \<or>
               ?CompositionChallenge out \<or>
               ?ActualResidual out \<or>
               ?QueryPhaseTarget out \<or>
               ?Alpha out))
            adversary_initial_state
          \<le>
          wp_event ?M ?Collision adversary_initial_state +
          wp_event ?M ?Query adversary_initial_state +
          wp_event ?M ?TraceTarget adversary_initial_state +
          wp_event ?M
            (\<lambda>out.
              ?CompositionTarget out \<or>
              ?BuilderTarget out \<or>
              ?Initial out \<or>
              ?TraceChallenge out \<or>
              ?CompositionChallenge out \<or>
              ?ActualResidual out \<or>
              ?QueryPhaseTarget out \<or>
              ?Alpha out)
            adversary_initial_state"
      by (rule wp_event_union_bound4)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Query adversary_initial_state +
        wp_event ?M ?TraceTarget adversary_initial_state +
        (wp_event ?M ?CompositionTarget adversary_initial_state +
         wp_event ?M ?BuilderTarget adversary_initial_state +
         wp_event ?M ?Initial adversary_initial_state +
         wp_event ?M
           (\<lambda>out.
             ?TraceChallenge out \<or>
             ?CompositionChallenge out \<or>
             ?ActualResidual out \<or>
             ?QueryPhaseTarget out \<or>
             ?Alpha out)
           adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound4)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Query adversary_initial_state +
        wp_event ?M ?TraceTarget adversary_initial_state +
        (wp_event ?M ?CompositionTarget adversary_initial_state +
         wp_event ?M ?BuilderTarget adversary_initial_state +
         wp_event ?M ?Initial adversary_initial_state +
         (wp_event ?M ?TraceChallenge adversary_initial_state +
          wp_event ?M ?CompositionChallenge adversary_initial_state +
          wp_event ?M ?ActualResidual adversary_initial_state +
          wp_event ?M
            (\<lambda>out. ?QueryPhaseTarget out \<or> ?Alpha out)
            adversary_initial_state))"
      by (intro add_mono order_refl wp_event_union_bound4)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Query adversary_initial_state +
        wp_event ?M ?TraceTarget adversary_initial_state +
        (wp_event ?M ?CompositionTarget adversary_initial_state +
         wp_event ?M ?BuilderTarget adversary_initial_state +
         wp_event ?M ?Initial adversary_initial_state +
         (wp_event ?M ?TraceChallenge adversary_initial_state +
          wp_event ?M ?CompositionChallenge adversary_initial_state +
          wp_event ?M ?ActualResidual adversary_initial_state +
          (wp_event ?M ?QueryPhaseTarget adversary_initial_state +
           wp_event ?M ?Alpha adversary_initial_state)))"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis
      unfolding ro_absorb_checked_staged_balanced_strict_selected_obstruction_union_def
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
        ro_checked_staged_balanced_decoded_semantic_rectangle_error_adaptive
          C budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_balanced_decoded_semantic_rectangle_bound_adaptive[
        OF wf controlled])
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
  have builder_target:
      "wp_event ?M ?BuilderTarget adversary_initial_state \<le>
        ro_absorb_checked_staged_fri_builder_merkle_target_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_clean_builder_merkle_target_hit_bound[
        OF wf controlled])
  have initial:
      "wp_event ?M ?Initial adversary_initial_state \<le>
        ro_checked_staged_conditioned_initial_target_error budgets"
    unfolding ro_checked_staged_conditioned_initial_target_error_def
    by (rule
      wp_ro_absorb_checked_staged_security_builder_initial_target_hit_bound[
        OF wf controlled])
  have trace_challenge:

      "wp_event ?M ?TraceChallenge adversary_initial_state \<le>
        ro_checked_staged_balanced_trace_challenge_error C budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_balanced_trace_challenge_transition_bound_exact_two[
        OF wf controlled eval_power trace_rounds_fit trace_exact])
  have composition_challenge:
      "wp_event ?M ?CompositionChallenge adversary_initial_state \<le>
        ro_checked_staged_balanced_composition_challenge_error C budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_balanced_composition_challenge_transition_bound_exact_two[
        OF wf controlled eval_power composition_rounds_fit
          composition_exact])
  have actual_residual:
      "wp_event ?M ?ActualResidual adversary_initial_state \<le>
        ro_checked_staged_balanced_strict_selected_combined_actual_residual_rectangle_error_adaptive
          C budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_combined_balanced_strict_selected_residual_actual_rectangle_bound_adaptive[
        OF wf controlled eval_power trace_rounds_fit
          composition_rounds_fit])
  have query_phase_target:
      "wp_event ?M ?QueryPhaseTarget adversary_initial_state \<le>
        ro_checked_staged_conditioned_residual_query_phase_target_error budgets"
    unfolding
      ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit_def
    by (rule order_trans[
      OF
        wp_ro_absorb_checked_staged_security_builder_head_event_le
        wp_ro_checked_staged_query_phase_builder_merkle_target_hit_bound[
          OF wf controlled]])
  have alpha:
      "wp_event ?M ?Alpha adversary_initial_state \<le>
        ro_checked_staged_first_root_robust_alpha_pivot_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent_bound[
        OF false_statement wf controlled nonempty])

  have closed:
      "wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Query adversary_initial_state +
        wp_event ?M ?TraceTarget adversary_initial_state +
        wp_event ?M ?CompositionTarget adversary_initial_state +
        wp_event ?M ?BuilderTarget adversary_initial_state +
        wp_event ?M ?Initial adversary_initial_state +
        wp_event ?M ?TraceChallenge adversary_initial_state +
        wp_event ?M ?CompositionChallenge adversary_initial_state +
        wp_event ?M ?ActualResidual adversary_initial_state +
        wp_event ?M ?QueryPhaseTarget adversary_initial_state +
        wp_event ?M ?Alpha adversary_initial_state
      \<le> ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets"
  proof -
    have summed:
        "wp_event ?M ?Collision adversary_initial_state +
          wp_event ?M ?Query adversary_initial_state +
          wp_event ?M ?TraceTarget adversary_initial_state +
          wp_event ?M ?CompositionTarget adversary_initial_state +
          wp_event ?M ?BuilderTarget adversary_initial_state +
          wp_event ?M ?Initial adversary_initial_state +
          wp_event ?M ?TraceChallenge adversary_initial_state +
          wp_event ?M ?CompositionChallenge adversary_initial_state +
          wp_event ?M ?ActualResidual adversary_initial_state +
          wp_event ?M ?QueryPhaseTarget adversary_initial_state +
          wp_event ?M ?Alpha adversary_initial_state
        \<le>
          hash_collision_budget_value 0
            (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
          ro_checked_staged_balanced_decoded_semantic_rectangle_error_adaptive
            C budgets +
          ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
          ro_absorb_checked_staged_trace_composition_prefix_target_error budgets +
          ro_absorb_checked_staged_fri_builder_merkle_target_error budgets +
          ro_checked_staged_conditioned_initial_target_error budgets +
          ro_checked_staged_balanced_trace_challenge_error C budgets +
          ro_checked_staged_balanced_composition_challenge_error C budgets +
          ro_checked_staged_balanced_strict_selected_combined_actual_residual_rectangle_error_adaptive
            C budgets +
          ro_checked_staged_conditioned_residual_query_phase_target_error budgets +
          ro_checked_staged_first_root_robust_alpha_pivot_error budgets"
      by (intro add_mono collision query trace_target composition_target
          builder_target initial trace_challenge composition_challenge
          actual_residual query_phase_target alpha)
    show ?thesis
      using summed
      unfolding ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error_def
      by (simp add: add.assoc)
  qed
  show ?thesis
    by (rule order_trans[OF classified order_trans[OF union closed]])
qed


lemma ro_absorb_stark_soundness_balanced_strict_selected_nonempty_exact_two:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and trace_exact:
      "fri_balanced_exact_list_cap
        (clength - 1) (ceil_log clength) C 2"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_balanced_exact_list_cap d (ceil_log (Suc d)) C 2"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A
      \<le> ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets"
proof -
  have bound:
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_balanced_strict_selected_nonempty_parameter_bound_exact_two[
        OF false_statement wf controlled nonempty eval_power
          trace_rounds_fit composition_rounds_fit trace_exact
          composition_exact])
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


definition
  ro_absorb_checked_staged_balanced_strict_selected_tightened_nonempty_parameter_error
    :: "nat \<Rightarrow> staged_budgets \<Rightarrow> prob"
where
  "ro_absorb_checked_staged_balanced_strict_selected_tightened_nonempty_parameter_error C budgets =
    min
      (ro_absorb_checked_staged_balanced_tightened_nonempty_parameter_error
        C budgets)
      (ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets)"

lemma
  ro_absorb_checked_staged_balanced_strict_selected_tightened_nonempty_parameter_error_le_previous:
  "ro_absorb_checked_staged_balanced_strict_selected_tightened_nonempty_parameter_error C budgets
    \<le>
    ro_absorb_checked_staged_balanced_tightened_nonempty_parameter_error
      C budgets"
  unfolding
    ro_absorb_checked_staged_balanced_strict_selected_tightened_nonempty_parameter_error_def
  by simp

lemma
  wp_ro_absorb_checked_staged_security_acceptance_balanced_strict_selected_tightened_nonempty_parameter_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and trace_exact:
      "fri_balanced_exact_list_cap
        (clength - 1) (ceil_log clength) C 2"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_balanced_exact_list_cap d (ceil_log (Suc d)) C 2"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      accepted adversary_initial_state
    \<le>
    ro_absorb_checked_staged_balanced_strict_selected_tightened_nonempty_parameter_error
      C budgets"
proof -
  have previous:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      accepted adversary_initial_state
    \<le>
    ro_absorb_checked_staged_balanced_tightened_nonempty_parameter_error
      C budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_balanced_tightened_nonempty_parameter_bound[
        OF false_statement wf controlled nonempty eval_power
          trace_rounds_fit composition_rounds_fit trace_exact
          composition_exact])
  have robust:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      accepted adversary_initial_state
    \<le> ro_absorb_checked_staged_balanced_strict_selected_nonempty_parameter_error C budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_balanced_strict_selected_nonempty_parameter_bound_exact_two[
        OF false_statement wf controlled nonempty eval_power
          trace_rounds_fit composition_rounds_fit trace_exact
          composition_exact])
  show ?thesis
    unfolding
      ro_absorb_checked_staged_balanced_strict_selected_tightened_nonempty_parameter_error_def
    by (rule min.boundedI[OF previous robust])
qed

lemma ro_absorb_stark_soundness_balanced_strict_selected_tightened_nonempty:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and trace_exact:
      "fri_balanced_exact_list_cap
        (clength - 1) (ceil_log clength) C 2"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_balanced_exact_list_cap d (ceil_log (Suc d)) C 2"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A
      \<le>
      ro_absorb_checked_staged_balanced_strict_selected_tightened_nonempty_parameter_error
        C budgets"
proof -
  have bound:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      accepted adversary_initial_state
    \<le>
    ro_absorb_checked_staged_balanced_strict_selected_tightened_nonempty_parameter_error
      C budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_balanced_strict_selected_tightened_nonempty_parameter_bound[
        OF false_statement wf controlled nonempty eval_power
          trace_rounds_fit composition_rounds_fit trace_exact
          composition_exact])
  have projection:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      accepted adversary_initial_state =
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
