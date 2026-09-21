theory Soundness_FRI_Conditioned_Explicit_Complete_List_Parameter_Bound
  imports
    Stark.Soundness_FRI_Conditioned_Explicit_Parameter_Bound
    Stark.Soundness_FRI_Conditioned_Explicit_Complete_List_Security_Classification
    Stark.Soundness_FRI_Conditioned_Explicit_Complete_List_Good_Query_Zero
begin

context soundness
begin

definition ro_checked_staged_conditioned_complete_list_actual_residual_error
  :: "prob"
where
  "ro_checked_staged_conditioned_complete_list_actual_residual_error =
    nnreal
      (fri_conditioned_residual_query_list_card_bound (clength - 1) +
       fri_conditioned_residual_query_list_card_bound maxDegree) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"

definition
  ro_absorb_checked_staged_conditioned_explicit_complete_list_nonempty_parameter_error
    :: "staged_budgets \<Rightarrow> prob"
where
  "ro_absorb_checked_staged_conditioned_explicit_complete_list_nonempty_parameter_error
      budgets =
    hash_collision_budget_value 0
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
    ro_checked_staged_trace_composition_complete_list_good_actual_query_error +
    ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
    ro_absorb_checked_staged_trace_composition_prefix_target_error budgets +
    ro_absorb_checked_staged_fri_builder_merkle_target_error budgets +
    ro_checked_staged_conditioned_initial_target_error budgets +
    ro_checked_staged_conditioned_trace_challenge_error budgets +
    ro_checked_staged_conditioned_composition_challenge_error budgets +
    ro_checked_staged_conditioned_complete_list_actual_residual_error +
    ro_checked_staged_conditioned_residual_query_phase_target_error budgets +
    ro_checked_staged_trace_composition_complete_list_padding_error +
    ro_checked_staged_first_root_alpha_pivot_error budgets"

lemma
  wp_ro_absorb_checked_staged_security_acceptance_conditioned_explicit_complete_list_nonempty_parameter_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> ro_absorb_checked_staged_conditioned_explicit_complete_list_nonempty_parameter_error
          budgets"
proof -
  let ?M =
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      A"
  let ?Collision = "final_hash_collision_event"
  let ?Query =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      ro_actual_query_trace_composition_good_query_lists"
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
        conditioned_trace_fri_bad_challenge_relation)"
  let ?CompositionChallenge =
    "ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        conditioned_composition_fri_bad_challenge_relation)"
  let ?ActualResidual =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      fri_conditioned_combined_query_head_lists"
  let ?QueryPhaseTarget =
    "ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit"
  let ?Padding =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      ro_trace_composition_padding_query_head_lists"
  let ?Alpha =
    "ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent"

  have classified:
      "wp_event ?M accepted adversary_initial_state \<le>
        wp_event ?M
          (ro_absorb_checked_staged_conditioned_explicit_complete_list_obstruction_union
            budgets)
          adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_le_conditioned_explicit_complete_list_obstruction_union[
        OF wf controlled nonempty])

  have union:
      "wp_event ?M
          (ro_absorb_checked_staged_conditioned_explicit_complete_list_obstruction_union
            budgets)
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
        wp_event ?M ?Padding adversary_initial_state +
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
               ?Padding out \<or>
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
              ?Padding out \<or>
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
             ?Padding out \<or>
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
            (\<lambda>out.
              ?QueryPhaseTarget out \<or> ?Padding out \<or> ?Alpha out)
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
           wp_event ?M
             (\<lambda>out. ?Padding out \<or> ?Alpha out)
             adversary_initial_state)))"
      by (intro add_mono order_refl wp_event_union_bound)
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
           (wp_event ?M ?Padding adversary_initial_state +
            wp_event ?M ?Alpha adversary_initial_state))))"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis
      unfolding
        ro_absorb_checked_staged_conditioned_explicit_complete_list_obstruction_union_def
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
        ro_checked_staged_trace_composition_complete_list_good_actual_query_error"
    by (rule
      wp_ro_absorb_checked_staged_security_trace_composition_complete_list_good_actual_query_bound_zero[
        OF wf controlled zero])  have trace_target:
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
        ro_checked_staged_conditioned_trace_challenge_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_trace_challenge_transition_bound[
        OF wf controlled])
  have composition_challenge:
      "wp_event ?M ?CompositionChallenge adversary_initial_state \<le>
        ro_checked_staged_conditioned_composition_challenge_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_composition_challenge_transition_bound[
        OF wf controlled])
  have actual_residual:
      "wp_event ?M ?ActualResidual adversary_initial_state \<le>
        ro_checked_staged_conditioned_complete_list_actual_residual_error"
    unfolding ro_checked_staged_conditioned_complete_list_actual_residual_error_def
    by (rule order_trans[
      OF
        wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
        wp_ro_checked_staged_combined_conditioned_residual_actual_bound_zero[
          OF wf controlled zero]])
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
  have padding:
      "wp_event ?M ?Padding adversary_initial_state \<le>
        ro_checked_staged_trace_composition_complete_list_padding_error"
    by (rule
      wp_ro_absorb_checked_staged_security_trace_composition_complete_list_padding_bound_zero[
        OF wf controlled zero])  have alpha:
      "wp_event ?M ?Alpha adversary_initial_state \<le>
        ro_checked_staged_first_root_alpha_pivot_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_trace_composition_all_queries_consistent_bound[
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
        wp_event ?M ?Padding adversary_initial_state +
        wp_event ?M ?Alpha adversary_initial_state
      \<le> ro_absorb_checked_staged_conditioned_explicit_complete_list_nonempty_parameter_error
          budgets"
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
          wp_event ?M ?Padding adversary_initial_state +
          wp_event ?M ?Alpha adversary_initial_state
        \<le>
          hash_collision_budget_value 0
            (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
          ro_checked_staged_trace_composition_complete_list_good_actual_query_error +
          ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
          ro_absorb_checked_staged_trace_composition_prefix_target_error budgets +
          ro_absorb_checked_staged_fri_builder_merkle_target_error budgets +
          ro_checked_staged_conditioned_initial_target_error budgets +
          ro_checked_staged_conditioned_trace_challenge_error budgets +
          ro_checked_staged_conditioned_composition_challenge_error budgets +
          ro_checked_staged_conditioned_complete_list_actual_residual_error +
          ro_checked_staged_conditioned_residual_query_phase_target_error budgets +
          ro_checked_staged_trace_composition_complete_list_padding_error +
          ro_checked_staged_first_root_alpha_pivot_error budgets"
      by (intro add_mono collision query trace_target composition_target
          builder_target initial trace_challenge composition_challenge
          actual_residual query_phase_target padding alpha)
    show ?thesis
      using summed
      unfolding
        ro_absorb_checked_staged_conditioned_explicit_complete_list_nonempty_parameter_error_def
      by (simp add: add.assoc)
  qed
  show ?thesis
    by (rule order_trans[OF classified order_trans[OF union closed]])
qed


definition
  ro_absorb_checked_staged_conditioned_explicit_tightened_nonempty_parameter_error
    :: "staged_budgets \<Rightarrow> prob"
where
  "ro_absorb_checked_staged_conditioned_explicit_tightened_nonempty_parameter_error
      budgets =
    min
      (ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
        budgets)
      (ro_absorb_checked_staged_conditioned_explicit_complete_list_nonempty_parameter_error
        budgets)"

lemma
  ro_absorb_checked_staged_conditioned_explicit_tightened_nonempty_parameter_error_le_old:
  "ro_absorb_checked_staged_conditioned_explicit_tightened_nonempty_parameter_error
      budgets
    \<le> ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
        budgets"
  unfolding
    ro_absorb_checked_staged_conditioned_explicit_tightened_nonempty_parameter_error_def
  by simp

lemma
  wp_ro_absorb_checked_staged_security_acceptance_conditioned_explicit_tightened_nonempty_parameter_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> ro_absorb_checked_staged_conditioned_explicit_tightened_nonempty_parameter_error
          budgets"
proof -
  have old:
      "wp_event
          (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A)
          accepted adversary_initial_state
        \<le> ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
            budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_conditioned_explicit_nonempty_parameter_bound[
        OF false_statement wf controlled nonempty])
  have complete_list:
      "wp_event
          (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A)
          accepted adversary_initial_state
        \<le> ro_absorb_checked_staged_conditioned_explicit_complete_list_nonempty_parameter_error
            budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_conditioned_explicit_complete_list_nonempty_parameter_bound[
        OF false_statement wf controlled zero nonempty])
  show ?thesis
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_tightened_nonempty_parameter_error_def
    by (rule min.boundedI[OF old complete_list])
qed

lemma ro_absorb_stark_soundness_conditioned_explicit_complete_list_nonempty:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
    and nonempty: "0 < ceil_log clength"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A
      \<le> ro_absorb_checked_staged_conditioned_explicit_complete_list_nonempty_parameter_error
          budgets"
proof -
  have bound:
      "wp_event
          (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A)
          accepted adversary_initial_state
        \<le> ro_absorb_checked_staged_conditioned_explicit_complete_list_nonempty_parameter_error
            budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_conditioned_explicit_complete_list_nonempty_parameter_bound[
        OF false_statement wf controlled zero nonempty])
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



lemma ro_absorb_stark_soundness_conditioned_explicit_tightened_nonempty:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
    and nonempty: "0 < ceil_log clength"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A
      \<le> ro_absorb_checked_staged_conditioned_explicit_tightened_nonempty_parameter_error
          budgets"
proof -
  have old:
      "ro_absorb_checked_staged_adversary_acceptance_probability A
        \<le> ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
            budgets"
    by (rule ro_absorb_stark_soundness_conditioned_explicit_nonempty[
      OF false_statement wf controlled nonempty])
  have complete_list:
      "ro_absorb_checked_staged_adversary_acceptance_probability A
        \<le> ro_absorb_checked_staged_conditioned_explicit_complete_list_nonempty_parameter_error
            budgets"
    by (rule
      ro_absorb_stark_soundness_conditioned_explicit_complete_list_nonempty[
        OF false_statement wf controlled zero nonempty])
  show ?thesis
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_tightened_nonempty_parameter_error_def
    by (rule min.boundedI[OF old complete_list])
qed


end
end
