theory Soundness_FRI_Conditioned_Explicit_Zero_Round_Parameter_Bound
  imports
    Stark.Soundness_FRI_Conditioned_Zero_Round_Security
    Stark.Soundness_FRI_Conditioned_Explicit_Parameter_Bound
begin

context soundness
begin

definition ro_checked_staged_conditioned_zero_round_joint_sampled_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_zero_round_joint_sampled_error budgets =
    ro_checked_staged_conditioned_composition_challenge_error budgets +
    ro_checked_staged_conditioned_residual_query_error budgets +
    ro_checked_staged_conditioned_zero_round_composition_padding_error budgets"

definition
  ro_absorb_checked_staged_conditioned_explicit_zero_round_obstruction_union
where
  "ro_absorb_checked_staged_conditioned_explicit_zero_round_obstruction_union
      budgets out \<longleftrightarrow>
    final_hash_collision_event out \<or>
    ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      ro_actual_query_zero_round_bad_query_lists out \<or>
    ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit out \<or>
    ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      ro_actual_query_zero_round_trace_composition_good_query_lists_for out \<or>
    ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit
      out \<or>
    ro_absorb_checked_staged_security_clean_builder_merkle_target_hit out \<or>
    ro_absorb_checked_staged_security_builder_initial_target_hit out \<or>
    ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        conditioned_composition_fri_bad_challenge_relation) out \<or>
    ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        ro_conditioned_augmented_absorbed_query_relation) out \<or>
    ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        composition_padding_absorbed_query_relation) out \<or>
    ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent
      out"

lemma
  wp_ro_absorb_checked_staged_security_zero_round_acceptance_le_conditioned_explicit_obstruction_union:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le>
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        (ro_absorb_checked_staged_conditioned_explicit_zero_round_obstruction_union
          budgets)
        adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and accepted_out: "accepted out"
  show
      "ro_absorb_checked_staged_conditioned_explicit_zero_round_obstruction_union
        budgets out"
  proof (cases "final_hash_collision_event out")
    case True
    then show ?thesis
      unfolding
        ro_absorb_checked_staged_conditioned_explicit_zero_round_obstruction_union_def
      by simp
  next
    case False
    from
      ro_absorb_checked_staged_security_clean_conditioned_explicit_zero_round_classification[
        OF zero wf controlled accepted_out support False]
    show ?thesis
      unfolding
        ro_absorb_checked_staged_conditioned_explicit_zero_round_obstruction_union_def
      by blast
  qed
qed

definition
  ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
      budgets =
    hash_collision_budget_value 0
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
    ro_checked_staged_zero_round_bad_actual_query_error budgets +
    ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
      budgets +
    ro_checked_staged_zero_round_trace_composition_good_actual_query_error
      budgets +
    ro_absorb_checked_staged_trace_composition_prefix_target_error budgets +
    ro_absorb_checked_staged_fri_builder_merkle_target_error budgets +
    ro_checked_staged_conditioned_initial_target_error budgets +
    ro_checked_staged_conditioned_zero_round_joint_sampled_error budgets +
    ro_checked_staged_zero_round_alpha_pivot_error budgets"

lemma
  wp_ro_absorb_checked_staged_security_acceptance_conditioned_explicit_zero_round_parameter_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
          budgets"
proof -
  let ?M =
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      A"
  let ?Collision = "final_hash_collision_event"
  let ?Bad =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      ro_actual_query_zero_round_bad_query_lists"
  let ?TraceTarget =
    "ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit"
  let ?Query =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      ro_actual_query_zero_round_trace_composition_good_query_lists_for"
  let ?CompositionTarget =
    "ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit"
  let ?BuilderTarget =
    "ro_absorb_checked_staged_security_clean_builder_merkle_target_hit"
  let ?Initial =
    "ro_absorb_checked_staged_security_builder_initial_target_hit"
  let ?CompositionChallenge =
    "ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        conditioned_composition_fri_bad_challenge_relation)"
  let ?Residual =
    "ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        ro_conditioned_augmented_absorbed_query_relation)"
  let ?Padding =
    "ro_absorb_checked_staged_security_builder_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        composition_padding_absorbed_query_relation)"
  let ?Alpha =
    "ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent"

  have classified:
      "wp_event ?M accepted adversary_initial_state \<le>
        wp_event ?M
          (ro_absorb_checked_staged_conditioned_explicit_zero_round_obstruction_union
            budgets)
          adversary_initial_state"
    by (rule
      wp_ro_absorb_checked_staged_security_zero_round_acceptance_le_conditioned_explicit_obstruction_union[
        OF zero wf controlled])

  have union:
      "wp_event ?M
          (ro_absorb_checked_staged_conditioned_explicit_zero_round_obstruction_union
            budgets)
          adversary_initial_state
        \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Bad adversary_initial_state +
        wp_event ?M ?TraceTarget adversary_initial_state +
        wp_event ?M ?Query adversary_initial_state +
        wp_event ?M ?CompositionTarget adversary_initial_state +
        wp_event ?M ?BuilderTarget adversary_initial_state +
        wp_event ?M ?Initial adversary_initial_state +
        wp_event ?M ?CompositionChallenge adversary_initial_state +
        wp_event ?M ?Residual adversary_initial_state +
        wp_event ?M ?Padding adversary_initial_state +
        wp_event ?M ?Alpha adversary_initial_state"
  proof -
    have
        "wp_event ?M
            (\<lambda>out.
              ?Collision out \<or>
              ?Bad out \<or>
              ?TraceTarget out \<or>
              (?Query out \<or>
               ?CompositionTarget out \<or>
               ?BuilderTarget out \<or>
               ?Initial out \<or>
               ?CompositionChallenge out \<or>
               ?Residual out \<or>
               ?Padding out \<or>
               ?Alpha out))
            adversary_initial_state
          \<le>
          wp_event ?M ?Collision adversary_initial_state +
          wp_event ?M ?Bad adversary_initial_state +
          wp_event ?M ?TraceTarget adversary_initial_state +
          wp_event ?M
            (\<lambda>out.
              ?Query out \<or>
              ?CompositionTarget out \<or>
              ?BuilderTarget out \<or>
              ?Initial out \<or>
              ?CompositionChallenge out \<or>
              ?Residual out \<or>
              ?Padding out \<or>
              ?Alpha out)
            adversary_initial_state"
      by (rule wp_event_union_bound4)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Bad adversary_initial_state +
        wp_event ?M ?TraceTarget adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         wp_event ?M ?CompositionTarget adversary_initial_state +
         wp_event ?M ?BuilderTarget adversary_initial_state +
         wp_event ?M
           (\<lambda>out.
             ?Initial out \<or>
             ?CompositionChallenge out \<or>
             ?Residual out \<or>
             ?Padding out \<or>
             ?Alpha out)
           adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound4)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Bad adversary_initial_state +
        wp_event ?M ?TraceTarget adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         wp_event ?M ?CompositionTarget adversary_initial_state +
         wp_event ?M ?BuilderTarget adversary_initial_state +
         (wp_event ?M ?Initial adversary_initial_state +
          wp_event ?M ?CompositionChallenge adversary_initial_state +
          wp_event ?M ?Residual adversary_initial_state +
          wp_event ?M
            (\<lambda>out. ?Padding out \<or> ?Alpha out)
            adversary_initial_state))"
      by (intro add_mono order_refl wp_event_union_bound4)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Bad adversary_initial_state +
        wp_event ?M ?TraceTarget adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         wp_event ?M ?CompositionTarget adversary_initial_state +
         wp_event ?M ?BuilderTarget adversary_initial_state +
         (wp_event ?M ?Initial adversary_initial_state +
          wp_event ?M ?CompositionChallenge adversary_initial_state +
          wp_event ?M ?Residual adversary_initial_state +
          (wp_event ?M ?Padding adversary_initial_state +
           wp_event ?M ?Alpha adversary_initial_state)))"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis
      unfolding
        ro_absorb_checked_staged_conditioned_explicit_zero_round_obstruction_union_def
      by (simp add: add.assoc)
  qed

  have collision:
      "wp_event ?M ?Collision adversary_initial_state \<le>
        hash_collision_budget_value 0
          (ro_absorb_checked_staged_security_hash_query_budget_for budgets)"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_final_hash_collision_bound_all_rounds[
        OF wf controlled])
  have bad:
      "wp_event ?M ?Bad adversary_initial_state \<le>
        ro_checked_staged_zero_round_bad_actual_query_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_zero_round_bad_actual_query_bound[
        OF zero wf controlled])
  have trace_target:
      "wp_event ?M ?TraceTarget adversary_initial_state \<le>
        ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
          budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit_bound[
        OF zero wf controlled])
  have query:
      "wp_event ?M ?Query adversary_initial_state \<le>
        ro_checked_staged_zero_round_trace_composition_good_actual_query_error
          budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_zero_round_trace_composition_good_actual_query_bound[
        OF zero wf controlled])
  have composition_target:
      "wp_event ?M ?CompositionTarget adversary_initial_state \<le>
        ro_absorb_checked_staged_trace_composition_prefix_target_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit_bound_all_rounds[
        OF wf controlled])
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
  have composition_challenge:
      "wp_event ?M ?CompositionChallenge adversary_initial_state \<le>
        ro_checked_staged_conditioned_composition_challenge_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_composition_challenge_transition_bound[
        OF wf controlled])
  have residual:
      "wp_event ?M ?Residual adversary_initial_state \<le>
        ro_checked_staged_conditioned_residual_query_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_residual_query_transition_bound[
        OF wf controlled])
  have padding:
      "wp_event ?M ?Padding adversary_initial_state \<le>
        ro_checked_staged_conditioned_zero_round_composition_padding_error
          budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_builder_zero_round_composition_padding_transition_bound[
        OF wf controlled])
  have alpha:
      "wp_event ?M ?Alpha adversary_initial_state \<le>
        ro_checked_staged_zero_round_alpha_pivot_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent_bound[
        OF false_statement zero wf controlled])

  have closed:
      "wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Bad adversary_initial_state +
        wp_event ?M ?TraceTarget adversary_initial_state +
        wp_event ?M ?Query adversary_initial_state +
        wp_event ?M ?CompositionTarget adversary_initial_state +
        wp_event ?M ?BuilderTarget adversary_initial_state +
        wp_event ?M ?Initial adversary_initial_state +
        wp_event ?M ?CompositionChallenge adversary_initial_state +
        wp_event ?M ?Residual adversary_initial_state +
        wp_event ?M ?Padding adversary_initial_state +
        wp_event ?M ?Alpha adversary_initial_state
      \<le> ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
          budgets"
  proof -
    have summed:
        "wp_event ?M ?Collision adversary_initial_state +
          wp_event ?M ?Bad adversary_initial_state +
          wp_event ?M ?TraceTarget adversary_initial_state +
          wp_event ?M ?Query adversary_initial_state +
          wp_event ?M ?CompositionTarget adversary_initial_state +
          wp_event ?M ?BuilderTarget adversary_initial_state +
          wp_event ?M ?Initial adversary_initial_state +
          wp_event ?M ?CompositionChallenge adversary_initial_state +
          wp_event ?M ?Residual adversary_initial_state +
          wp_event ?M ?Padding adversary_initial_state +
          wp_event ?M ?Alpha adversary_initial_state
        \<le>
          hash_collision_budget_value 0
            (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
          ro_checked_staged_zero_round_bad_actual_query_error budgets +
          ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
            budgets +
          ro_checked_staged_zero_round_trace_composition_good_actual_query_error
            budgets +
          ro_absorb_checked_staged_trace_composition_prefix_target_error budgets +
          ro_absorb_checked_staged_fri_builder_merkle_target_error budgets +
          ro_checked_staged_conditioned_initial_target_error budgets +
          ro_checked_staged_conditioned_composition_challenge_error budgets +
          ro_checked_staged_conditioned_residual_query_error budgets +
          ro_checked_staged_conditioned_zero_round_composition_padding_error
            budgets +
          ro_checked_staged_zero_round_alpha_pivot_error budgets"
      by (intro add_mono collision bad trace_target query composition_target
          builder_target initial composition_challenge residual padding alpha)
    show ?thesis
      using summed
      unfolding
        ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error_def
        ro_checked_staged_conditioned_zero_round_joint_sampled_error_def
      by (simp add: add.assoc)
  qed
  show ?thesis
    by (rule order_trans[OF classified order_trans[OF union closed]])
qed

theorem ro_absorb_stark_soundness_conditioned_explicit_zero_round:
  assumes false_statement: "\<not> exists_valid_trace"
    and zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A
      \<le> ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
          budgets"
proof -
  have bound:
      "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
          budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_acceptance_conditioned_explicit_zero_round_parameter_bound[
        OF false_statement zero wf controlled])
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
      wp_ro_absorb_checked_staged_security_with_first_root_acceptance_eq_all_rounds)
  show ?thesis
    using bound projection
    unfolding ro_absorb_checked_staged_adversary_acceptance_probability_def
      accepted_def
    by simp
qed

end
end
