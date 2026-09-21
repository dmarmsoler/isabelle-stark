theory Soundness_FRI_Robust_Exact_Rate_Parameter_Bound
  imports
    Soundness_FRI_Robust_Parameter_Bound
    Soundness_FRI_Robust_Exact_Rate_Security_Classification
    Soundness_FRI_Robust_Exact_Rate_Challenge_Relation
begin

context soundness
begin

lemma
  wp_ro_absorb_checked_staged_security_builder_robust_trace_challenge_transition_bound_exact_two:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_exponent_fit: "ceil_log clength + K \<le> N"
    and K_pos: "0 < K"
    and trace_exact:
      "fri_linear_exact_list_cap
        (clength - 1) (ceil_log clength) K 2"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          (robust_conditioned_trace_fri_bad_challenge_relation K)))
      adversary_initial_state
    \<le> ro_checked_staged_robust_trace_challenge_error K budgets"
  unfolding ro_checked_staged_robust_trace_challenge_error_def Let_def
  by (rule order_trans[
      OF
        wp_ro_absorb_checked_staged_security_builder_relation_transition_le
        wp_ro_checked_staged_transcript_with_query_witnesses_robust_conditioned_trace_fri_relation_exact_two[
          OF wf controlled eval_power trace_exponent_fit K_pos trace_exact]])

lemma
  wp_ro_absorb_checked_staged_security_builder_robust_composition_challenge_transition_bound_exact_two:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and composition_exponent_fit:
      "ceil_log (Suc maxDegree) + K \<le> N"
    and K_pos: "0 < K"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_linear_exact_list_cap d (ceil_log (Suc d)) K 2"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_builder_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          (robust_conditioned_composition_fri_bad_challenge_relation K)))
      adversary_initial_state
    \<le> ro_checked_staged_robust_composition_challenge_error K budgets"
  unfolding ro_checked_staged_robust_composition_challenge_error_def Let_def
  by (rule order_trans[
      OF
        wp_ro_absorb_checked_staged_security_builder_relation_transition_le
        wp_ro_checked_staged_transcript_with_query_witnesses_robust_conditioned_composition_fri_relation_exact_two[
          OF wf controlled eval_power composition_exponent_fit
            K_pos composition_exact]])


lemma
  wp_ro_absorb_checked_staged_security_acceptance_robust_nonempty_parameter_bound_exact_two:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_exponent_fit: "ceil_log clength + K \<le> N"
    and composition_exponent_fit:
      "ceil_log (Suc maxDegree) + K \<le> N"
    and K_pos: "0 < K"
    and trace_exact:
      "fri_linear_exact_list_cap
        (clength - 1) (ceil_log clength) K 2"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_linear_exact_list_cap d (ceil_log (Suc d)) K 2"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> ro_absorb_checked_staged_robust_nonempty_parameter_error K budgets"
proof -
  let ?M =
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      A"
  let ?Collision = "final_hash_collision_event"
  let ?Query =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      (ro_robust_decoded_semantic_query_lists K)"
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
        (robust_conditioned_trace_fri_bad_challenge_relation K))"
  let ?CompositionChallenge =
    "ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        (robust_conditioned_composition_fri_bad_challenge_relation K))"
  let ?ActualResidual =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      (fri_robust_combined_query_head_lists K)"
  let ?QueryPhaseTarget =
    "ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit"
  let ?Alpha =
    "ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent"

  have classified:
      "wp_event ?M accepted adversary_initial_state \<le>
        wp_event ?M
          (ro_absorb_checked_staged_robust_obstruction_union K budgets)
          adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_le_robust_obstruction_union_exact_two[
        OF wf controlled nonempty eval_power trace_exponent_fit
          composition_exponent_fit K_pos trace_exact composition_exact])

  have union:
      "wp_event ?M
          (ro_absorb_checked_staged_robust_obstruction_union K budgets)
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
      unfolding ro_absorb_checked_staged_robust_obstruction_union_def
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
        ro_checked_staged_robust_decoded_semantic_rectangle_error_adaptive
          K budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_robust_decoded_semantic_rectangle_bound_adaptive[
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
        ro_checked_staged_robust_trace_challenge_error K budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_robust_trace_challenge_transition_bound_exact_two[
        OF wf controlled eval_power trace_exponent_fit K_pos trace_exact])
  have composition_challenge:
      "wp_event ?M ?CompositionChallenge adversary_initial_state \<le>
        ro_checked_staged_robust_composition_challenge_error K budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_robust_composition_challenge_transition_bound_exact_two[
        OF wf controlled eval_power composition_exponent_fit
          K_pos composition_exact])
  have actual_residual:
      "wp_event ?M ?ActualResidual adversary_initial_state \<le>
        ro_checked_staged_robust_combined_actual_residual_rectangle_error_adaptive
          K budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_combined_robust_residual_actual_rectangle_bound_adaptive[
        OF wf controlled eval_power trace_exponent_fit
          composition_exponent_fit])
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
      \<le> ro_absorb_checked_staged_robust_nonempty_parameter_error K budgets"
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
          ro_checked_staged_robust_decoded_semantic_rectangle_error_adaptive
            K budgets +
          ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
          ro_absorb_checked_staged_trace_composition_prefix_target_error budgets +
          ro_absorb_checked_staged_fri_builder_merkle_target_error budgets +
          ro_checked_staged_conditioned_initial_target_error budgets +
          ro_checked_staged_robust_trace_challenge_error K budgets +
          ro_checked_staged_robust_composition_challenge_error K budgets +
          ro_checked_staged_robust_combined_actual_residual_rectangle_error_adaptive
            K budgets +
          ro_checked_staged_conditioned_residual_query_phase_target_error budgets +
          ro_checked_staged_first_root_robust_alpha_pivot_error budgets"
      by (intro add_mono collision query trace_target composition_target
          builder_target initial trace_challenge composition_challenge
          actual_residual query_phase_target alpha)
    show ?thesis
      using summed
      unfolding ro_absorb_checked_staged_robust_nonempty_parameter_error_def
      by (simp add: add.assoc)
  qed
  show ?thesis
    by (rule order_trans[OF classified order_trans[OF union closed]])
qed


lemma ro_absorb_stark_soundness_robust_nonempty_exact_two:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_exponent_fit: "ceil_log clength + K \<le> N"
    and composition_exponent_fit:
      "ceil_log (Suc maxDegree) + K \<le> N"
    and K_pos: "0 < K"
    and trace_exact:
      "fri_linear_exact_list_cap
        (clength - 1) (ceil_log clength) K 2"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_linear_exact_list_cap d (ceil_log (Suc d)) K 2"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A
      \<le> ro_absorb_checked_staged_robust_nonempty_parameter_error K budgets"
proof -
  have bound:
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> ro_absorb_checked_staged_robust_nonempty_parameter_error K budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_robust_nonempty_parameter_bound_exact_two[
        OF false_statement wf controlled nonempty eval_power
          trace_exponent_fit composition_exponent_fit K_pos trace_exact
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
  ro_absorb_checked_staged_robust_exact_rate_tightened_nonempty_parameter_error
    :: "nat \<Rightarrow> staged_budgets \<Rightarrow> prob"
where
  "ro_absorb_checked_staged_robust_exact_rate_tightened_nonempty_parameter_error K budgets =
    min
      (ro_absorb_checked_staged_conditioned_explicit_complete_list_adaptive_rectangle_tightened_nonempty_parameter_error
        budgets)
      (ro_absorb_checked_staged_robust_nonempty_parameter_error K budgets)"

lemma
  ro_absorb_checked_staged_robust_exact_rate_tightened_nonempty_parameter_error_le_previous:
  "ro_absorb_checked_staged_robust_exact_rate_tightened_nonempty_parameter_error K budgets
    \<le>
    ro_absorb_checked_staged_conditioned_explicit_complete_list_adaptive_rectangle_tightened_nonempty_parameter_error
      budgets"
  unfolding
    ro_absorb_checked_staged_robust_exact_rate_tightened_nonempty_parameter_error_def
  by simp

lemma
  wp_ro_absorb_checked_staged_security_acceptance_robust_exact_rate_tightened_nonempty_parameter_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_exponent_fit: "ceil_log clength + K \<le> N"
    and composition_exponent_fit:
      "ceil_log (Suc maxDegree) + K \<le> N"
    and K_pos: "0 < K"
    and trace_exact:
      "fri_linear_exact_list_cap
        (clength - 1) (ceil_log clength) K 2"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_linear_exact_list_cap d (ceil_log (Suc d)) K 2"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      accepted adversary_initial_state
    \<le>
    ro_absorb_checked_staged_robust_exact_rate_tightened_nonempty_parameter_error
      K budgets"
proof -
  have previous:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      accepted adversary_initial_state
    \<le>
    ro_absorb_checked_staged_conditioned_explicit_complete_list_adaptive_rectangle_tightened_nonempty_parameter_error
      budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_conditioned_explicit_complete_list_adaptive_rectangle_tightened_nonempty_parameter_bound[
        OF false_statement wf controlled nonempty])
  have robust:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      accepted adversary_initial_state
    \<le> ro_absorb_checked_staged_robust_nonempty_parameter_error K budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_robust_nonempty_parameter_bound_exact_two[
        OF false_statement wf controlled nonempty eval_power
          trace_exponent_fit composition_exponent_fit K_pos trace_exact
          composition_exact])
  show ?thesis
    unfolding
      ro_absorb_checked_staged_robust_exact_rate_tightened_nonempty_parameter_error_def
    by (rule min.boundedI[OF previous robust])
qed

lemma ro_absorb_stark_soundness_robust_exact_rate_tightened_nonempty:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_exponent_fit: "ceil_log clength + K \<le> N"
    and composition_exponent_fit:
      "ceil_log (Suc maxDegree) + K \<le> N"
    and K_pos: "0 < K"
    and trace_exact:
      "fri_linear_exact_list_cap
        (clength - 1) (ceil_log clength) K 2"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_linear_exact_list_cap d (ceil_log (Suc d)) K 2"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A
      \<le>
      ro_absorb_checked_staged_robust_exact_rate_tightened_nonempty_parameter_error
        K budgets"
proof -
  have bound:
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      accepted adversary_initial_state
    \<le>
    ro_absorb_checked_staged_robust_exact_rate_tightened_nonempty_parameter_error
      K budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_robust_exact_rate_tightened_nonempty_parameter_bound[
        OF false_statement wf controlled nonempty eval_power
          trace_exponent_fit composition_exponent_fit K_pos trace_exact
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
