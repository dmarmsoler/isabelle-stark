theory Soundness_FRI_Correlated_Agreement_Parameter_Bound
 imports Stark.Soundness_FRI_Correlated_Agreement_Security_Classification
   Stark.Soundness_FRI_Conditioned_Explicit_All_Rounds_Bound
   Stark.Soundness_FRI_Robust_Parameter_Bound
   Stark.Soundness_FRI_Prefix_Local_Target_Bounds
begin
section \<open>Correlated-agreement public parameter bound\<close>
text \<open>
  The auxiliary nonempty bound retains every collision, target and decoded-alpha
  charge. The public endpoint has exactly the existing three soundness premises.
  Arithmetic eligibility is tested inside the error definition. Outside that
  regime the existing all-round bound is retained; inside it the minimum is used.
  The two query-head-fixed targets use prefix-local range bounds; no event is
  removed. Older independently proved bounds remain available. No concrete security profile
  or unconditional numerical improvement is asserted.
\<close>

context soundness
begin

definition ro_mca_challenge_error :: "staged_budgets \<Rightarrow> prob" where
 "ro_mca_challenge_error budgets =
   (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
    in nnreal (q*(fri_mca_direct_cap+(7*q+2))) / nnreal size)"

lemma wp_ro_mca_trace_security_bad:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and ep: "clength*scale=2^N"
   and fit: "Suc (ceil_log clength) \<le> N"
   and rate: "4*fri_padded_degree_bound (clength-1) \<le> clength*scale"
 shows "wp_event
   (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
   (ro_mca_security_bad True) adversary_initial_state \<le> ro_mca_challenge_error budgets"
 unfolding ro_mca_security_bad_def
proof (rule order_trans[OF wp_ro_absorb_checked_staged_security_builder_head_event_le])
 show "wp_event (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
     (ro_mca_builder_bad True) adversary_initial_state \<le> ro_mca_challenge_error budgets"
   using wp_ro_checked_staged_transcript_trace_mca_bad[OF wf controlled ep fit rate]
   unfolding ro_mca_builder_bad_def ro_mca_challenge_error_def Let_def by simp
qed

lemma wp_ro_mca_composition_security_bad:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and ep: "clength*scale=2^N"
   and fit: "Suc (ceil_log (Suc maxDegree)) \<le> N"
   and rate: "4*fri_padded_degree_bound maxDegree \<le> clength*scale"
 shows "wp_event
   (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
   (ro_mca_security_bad False) adversary_initial_state \<le> ro_mca_challenge_error budgets"
 unfolding ro_mca_security_bad_def
proof (rule order_trans[OF wp_ro_absorb_checked_staged_security_builder_head_event_le])
 show "wp_event (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
     (ro_mca_builder_bad False) adversary_initial_state \<le> ro_mca_challenge_error budgets"
   using wp_ro_checked_staged_transcript_composition_mca_bad[OF wf controlled ep fit rate]
   unfolding ro_mca_builder_bad_def ro_mca_challenge_error_def Let_def by simp
qed

definition ro_mca_nonempty_parameter_error
  :: "nat \<Rightarrow> nat \<Rightarrow> staged_budgets \<Rightarrow> prob"
where
  "ro_mca_nonempty_parameter_error rT rC budgets =
    hash_collision_budget_value 0
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
    ro_mca_rectangle_error (mca_decoded_semantic_query_index_bound rT rC) budgets +
    ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
    ro_absorb_checked_staged_local_composition_prefix_target_error budgets +
    ro_absorb_checked_staged_fri_builder_merkle_target_error budgets +
    ro_checked_staged_conditioned_initial_target_error budgets +
    ro_mca_challenge_error budgets +
    ro_mca_challenge_error budgets +
    ro_mca_combined_rectangle_error rT rC budgets +
    ro_checked_staged_local_query_phase_target_error budgets +
    ro_checked_staged_first_root_robust_alpha_pivot_error budgets"

lemma
  wp_ro_mca_nonempty_parameter_bound:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and trace_rate: "4*fri_padded_degree_bound (clength-1) \<le> clength*scale"
    and composition_rate: "4*fri_padded_degree_bound maxDegree \<le> clength*scale"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> ro_mca_nonempty_parameter_error rT rC budgets"
proof -
  let ?M =
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      A"
  let ?Collision = "final_hash_collision_event"
  let ?Query =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      (ro_mca_decoded_semantic_query_lists rT rC)"
  let ?TraceTarget =
    "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit"
  let ?CompositionTarget =
    "ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit"
  let ?BuilderTarget =
    "ro_absorb_checked_staged_security_clean_builder_merkle_target_hit"
  let ?Initial =
    "ro_absorb_checked_staged_security_builder_initial_target_hit"
  let ?TraceChallenge = "ro_mca_security_bad True"
  let ?CompositionChallenge = "ro_mca_security_bad False"
  let ?ActualResidual =
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
      (fri_mca_combined_query_lists N rT rC)"
  let ?QueryPhaseTarget =
    "ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit"
  let ?Alpha =
    "ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent"

  have classified:
      "wp_event ?M accepted adversary_initial_state \<le>
        wp_event ?M
          (ro_mca_obstruction_union N rT rC)
          adversary_initial_state"
    by (rule
      wp_ro_mca_acceptance_classification[
        OF wf controlled nonempty eval_power trace_rounds_fit composition_rounds_fit])

  have union:
      "wp_event ?M
          (ro_mca_obstruction_union N rT rC)
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
      unfolding ro_mca_obstruction_union_def
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
        ro_mca_rectangle_error (mca_decoded_semantic_query_index_bound rT rC) budgets"
    by (rule order_trans[OF
      wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
      wp_ro_mca_decoded_semantic_rectangle[OF wf controlled]])
  have trace_target:
      "wp_event ?M ?TraceTarget adversary_initial_state \<le>
        ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_bound[
        OF nonempty wf controlled])
  have composition_target:
      "wp_event ?M ?CompositionTarget adversary_initial_state \<le>
        ro_absorb_checked_staged_local_composition_prefix_target_error budgets"
    by (rule
      wp_ro_absorb_checked_staged_clean_composition_prefix_target_hit_local_bound[
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
        ro_mca_challenge_error budgets"
    by (rule wp_ro_mca_trace_security_bad[OF wf controlled eval_power trace_rounds_fit trace_rate])
  have composition_challenge:
      "wp_event ?M ?CompositionChallenge adversary_initial_state \<le>
        ro_mca_challenge_error budgets"
    by (rule wp_ro_mca_composition_security_bad[OF wf controlled eval_power composition_rounds_fit composition_rate])
  have actual_residual:
      "wp_event ?M ?ActualResidual adversary_initial_state \<le>
        ro_mca_combined_rectangle_error rT rC budgets"
    by (rule order_trans[OF
      wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
      wp_ro_mca_combined_rectangle[OF wf controlled]])
  have query_phase_target:
      "wp_event ?M ?QueryPhaseTarget adversary_initial_state \<le>
        ro_checked_staged_local_query_phase_target_error budgets"
    unfolding
      ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit_def
    by (rule order_trans[
      OF
        wp_ro_absorb_checked_staged_security_builder_head_event_le
        wp_ro_checked_staged_query_phase_builder_merkle_target_hit_local_bound[
          OF nonempty wf controlled]])
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
      \<le> ro_mca_nonempty_parameter_error rT rC budgets"
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
          ro_mca_rectangle_error (mca_decoded_semantic_query_index_bound rT rC) budgets +
          ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
          ro_absorb_checked_staged_local_composition_prefix_target_error budgets +
          ro_absorb_checked_staged_fri_builder_merkle_target_error budgets +
          ro_checked_staged_conditioned_initial_target_error budgets +
          ro_mca_challenge_error budgets +
          ro_mca_challenge_error budgets +
          ro_mca_combined_rectangle_error rT rC budgets +
          ro_checked_staged_local_query_phase_target_error budgets +
          ro_checked_staged_first_root_robust_alpha_pivot_error budgets"
      by (intro add_mono collision query trace_target composition_target
          builder_target initial trace_challenge composition_challenge
          actual_residual query_phase_target alpha)
    show ?thesis
      using summed
      unfolding ro_mca_nonempty_parameter_error_def
      by (simp add: add.assoc)
  qed
  show ?thesis
    by (rule order_trans[OF classified order_trans[OF union closed]])
qed


lemma ro_absorb_stark_soundness_mca_nonempty:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and trace_rate: "4*fri_padded_degree_bound (clength-1) \<le> clength*scale"
    and composition_rate: "4*fri_padded_degree_bound maxDegree \<le> clength*scale"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A
      \<le> ro_mca_nonempty_parameter_error rT rC budgets"
proof -
  have bound:
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> ro_mca_nonempty_parameter_error rT rC budgets"
    by (rule
      wp_ro_mca_nonempty_parameter_bound[
        OF false_statement wf controlled nonempty eval_power
          trace_rounds_fit composition_rounds_fit trace_rate
          composition_rate])
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


definition ro_mca_parameter_regime :: "nat \<Rightarrow> bool" where
 "ro_mca_parameter_regime N \<longleftrightarrow> 0 < ceil_log clength \<and> clength*scale=2^N \<and>
   Suc (ceil_log clength) \<le> N \<and> Suc (ceil_log (Suc maxDegree)) \<le> N \<and>
   4*fri_padded_degree_bound (clength-1) \<le> clength*scale \<and>
   4*fri_padded_degree_bound maxDegree \<le> clength*scale"

definition ro_mca_parameter_error :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> staged_budgets \<Rightarrow> prob" where
 "ro_mca_parameter_error N rT rC budgets =
   (if ro_mca_parameter_regime N
    then min (ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets)
      (ro_mca_nonempty_parameter_error rT rC budgets)
    else ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets)"

lemma ro_mca_parameter_error_le_previous:
 "ro_mca_parameter_error N rT rC budgets \<le>
   ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets"
 unfolding ro_mca_parameter_error_def by simp

lemma ro_mca_parameter_error_outside_regime:
 "\<not> ro_mca_parameter_regime N \<Longrightarrow> ro_mca_parameter_error N rT rC budgets =
   ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets"
 unfolding ro_mca_parameter_error_def by simp

lemma ro_mca_parameter_error_zero_rounds:
 "ceil_log clength = 0 \<Longrightarrow> ro_mca_parameter_error N rT rC budgets =
   ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error budgets"
 unfolding ro_mca_parameter_error_def ro_mca_parameter_regime_def
   ro_absorb_checked_staged_conditioned_explicit_parameter_error_def by simp

theorem ro_absorb_stark_soundness_mca:
 assumes false_statement: "\<not> exists_valid_trace"
   and wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
 shows "ro_absorb_checked_staged_adversary_acceptance_probability A \<le>
   ro_mca_parameter_error N rT rC budgets"
proof -
 have previous: "ro_absorb_checked_staged_adversary_acceptance_probability A \<le>
     ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets"
   by (rule ro_absorb_stark_soundness_conditioned_explicit[OF false_statement wf controlled])
 show ?thesis
 proof (cases "ro_mca_parameter_regime N")
   case True
   then have conditions: "0 < ceil_log clength" "clength*scale=2^N"
     "Suc (ceil_log clength) \<le> N" "Suc (ceil_log (Suc maxDegree)) \<le> N"
     "4*fri_padded_degree_bound (clength-1) \<le> clength*scale"
     "4*fri_padded_degree_bound maxDegree \<le> clength*scale"
     unfolding ro_mca_parameter_regime_def by blast+
   have refined: "ro_absorb_checked_staged_adversary_acceptance_probability A \<le>
       ro_mca_nonempty_parameter_error rT rC budgets"
     by (rule ro_absorb_stark_soundness_mca_nonempty[OF false_statement wf controlled conditions])
   show ?thesis using previous refined True unfolding ro_mca_parameter_error_def by simp
 next
   case False
   show ?thesis using previous False unfolding ro_mca_parameter_error_def by simp
 qed
qed

end
end
