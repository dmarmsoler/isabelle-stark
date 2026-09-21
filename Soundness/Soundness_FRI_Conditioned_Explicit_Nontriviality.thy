theory Soundness_FRI_Conditioned_Explicit_Nontriviality
  imports Stark.Soundness_FRI_Conditioned_Explicit_All_Rounds_Bound
begin

context soundness
begin

lemma nnreal_eleven_twelfths:
  "(1 / 12 :: nnreal) + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 +
      1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 < 1"
proof -
  have
      "nn2real
        ((1 / 12 :: nnreal) + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 +
          1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12) <
       nn2real 1"
    by simp
  then show ?thesis by (subst (asm) nn2real_less_iff)
qed

definition
  ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_nontrivial
where
  "ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_nontrivial
      budgets \<longleftrightarrow>
    hash_collision_budget_value 0
        (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      \<le> 1 / 12 \<and>
    ro_checked_staged_trace_composition_good_actual_query_error budgets
      \<le> 1 / 12 \<and>
    ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets
      \<le> 1 / 12 \<and>
    ro_absorb_checked_staged_trace_composition_prefix_target_error budgets
      \<le> 1 / 12 \<and>
    ro_absorb_checked_staged_fri_builder_merkle_target_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_conditioned_initial_target_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_conditioned_trace_challenge_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_conditioned_composition_challenge_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_conditioned_residual_query_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_conditioned_composition_padding_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_first_root_alpha_pivot_error budgets
      \<le> 1 / 12"

definition
  ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_nontrivial
where
  "ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_nontrivial
      budgets \<longleftrightarrow>
    hash_collision_budget_value 0
        (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
      \<le> 1 / 12 \<and>
    ro_checked_staged_zero_round_bad_actual_query_error budgets
      \<le> 1 / 12 \<and>
    ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
        budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_zero_round_trace_composition_good_actual_query_error
        budgets
      \<le> 1 / 12 \<and>
    ro_absorb_checked_staged_trace_composition_prefix_target_error budgets
      \<le> 1 / 12 \<and>
    ro_absorb_checked_staged_fri_builder_merkle_target_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_conditioned_initial_target_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_conditioned_composition_challenge_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_conditioned_residual_query_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_conditioned_zero_round_composition_padding_error budgets
      \<le> 1 / 12 \<and>
    ro_checked_staged_zero_round_alpha_pivot_error budgets
      \<le> 1 / 12"

definition
  ro_absorb_checked_staged_conditioned_explicit_parameter_nontrivial
where
  "ro_absorb_checked_staged_conditioned_explicit_parameter_nontrivial
      budgets \<longleftrightarrow>
    (if ceil_log clength = 0
     then
       ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_nontrivial
         budgets
     else
       ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_nontrivial
         budgets)"

lemma
  ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error_lt_one:
  assumes conditions:
    "ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_nontrivial
      budgets"
  shows
    "ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
      budgets < 1"
proof -
  have collision:
      "hash_collision_budget_value 0
          (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
        \<le> 1 / 12"
    and query:
      "ro_checked_staged_trace_composition_good_actual_query_error budgets
        \<le> 1 / 12"
    and trace_target:
      "ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets
        \<le> 1 / 12"
    and composition_target:
      "ro_absorb_checked_staged_trace_composition_prefix_target_error budgets
        \<le> 1 / 12"
    and builder_target:
      "ro_absorb_checked_staged_fri_builder_merkle_target_error budgets
        \<le> 1 / 12"
    and initial:
      "ro_checked_staged_conditioned_initial_target_error budgets \<le> 1 / 12"
    and trace_challenge:
      "ro_checked_staged_conditioned_trace_challenge_error budgets \<le> 1 / 12"
    and composition_challenge:
      "ro_checked_staged_conditioned_composition_challenge_error budgets
        \<le> 1 / 12"
    and residual:
      "ro_checked_staged_conditioned_residual_query_error budgets \<le> 1 / 12"
    and padding:
      "ro_checked_staged_conditioned_composition_padding_error budgets
        \<le> 1 / 12"
    and alpha:
      "ro_checked_staged_first_root_alpha_pivot_error budgets \<le> 1 / 12"
    using conditions
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_nontrivial_def
    by blast+
  have sum_le:
      "hash_collision_budget_value 0
          (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
       ro_checked_staged_trace_composition_good_actual_query_error budgets +
       ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
       ro_absorb_checked_staged_trace_composition_prefix_target_error budgets +
       ro_absorb_checked_staged_fri_builder_merkle_target_error budgets +
       ro_checked_staged_conditioned_initial_target_error budgets +
       ro_checked_staged_conditioned_trace_challenge_error budgets +
       ro_checked_staged_conditioned_composition_challenge_error budgets +
       ro_checked_staged_conditioned_residual_query_error budgets +
       ro_checked_staged_conditioned_composition_padding_error budgets +
       ro_checked_staged_first_root_alpha_pivot_error budgets
      \<le> (1 / 12 :: nnreal) + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 +
          1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12"
    by (intro add_mono collision query trace_target composition_target
        builder_target initial trace_challenge composition_challenge residual
        padding alpha)
  have error_le:
      "ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
          budgets
        \<le> (1 / 12 :: nnreal) + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 +
            1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12"
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error_def
      ro_checked_staged_conditioned_joint_sampled_error_def
    using sum_le by (simp add: add.assoc)
  show ?thesis
    by (rule le_less_trans[OF error_le nnreal_eleven_twelfths])
qed

lemma
  ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error_lt_one:
  assumes conditions:
    "ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_nontrivial
      budgets"
  shows
    "ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
      budgets < 1"
proof -
  have collision:
      "hash_collision_budget_value 0
          (ro_absorb_checked_staged_security_hash_query_budget_for budgets)
        \<le> 1 / 12"
    and bad:
      "ro_checked_staged_zero_round_bad_actual_query_error budgets \<le> 1 / 12"
    and trace_target:
      "ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_error
          budgets
        \<le> 1 / 12"
    and query:
      "ro_checked_staged_zero_round_trace_composition_good_actual_query_error
          budgets
        \<le> 1 / 12"
    and composition_target:
      "ro_absorb_checked_staged_trace_composition_prefix_target_error budgets
        \<le> 1 / 12"
    and builder_target:
      "ro_absorb_checked_staged_fri_builder_merkle_target_error budgets
        \<le> 1 / 12"
    and initial:
      "ro_checked_staged_conditioned_initial_target_error budgets \<le> 1 / 12"
    and composition_challenge:
      "ro_checked_staged_conditioned_composition_challenge_error budgets
        \<le> 1 / 12"
    and residual:
      "ro_checked_staged_conditioned_residual_query_error budgets \<le> 1 / 12"
    and padding:
      "ro_checked_staged_conditioned_zero_round_composition_padding_error
          budgets
        \<le> 1 / 12"
    and alpha:
      "ro_checked_staged_zero_round_alpha_pivot_error budgets \<le> 1 / 12"
    using conditions
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_nontrivial_def
    by blast+
  have sum_le:
      "hash_collision_budget_value 0
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
       ro_checked_staged_zero_round_alpha_pivot_error budgets
      \<le> (1 / 12 :: nnreal) + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 +
          1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12"
    by (intro add_mono collision bad trace_target query composition_target
        builder_target initial composition_challenge residual padding alpha)
  have error_le:
      "ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
          budgets
        \<le> (1 / 12 :: nnreal) + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 +
            1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12 + 1 / 12"
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error_def
      ro_checked_staged_conditioned_zero_round_joint_sampled_error_def
    using sum_le
    by (simp add: add.assoc)
  show ?thesis
    by (rule le_less_trans[OF error_le nnreal_eleven_twelfths])
qed

lemma ro_absorb_checked_staged_conditioned_explicit_parameter_error_lt_one:
  assumes conditions:
    "ro_absorb_checked_staged_conditioned_explicit_parameter_nontrivial budgets"
  shows
    "ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets < 1"
proof (cases "ceil_log clength = 0")
  case True
  have zero_conditions:
      "ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_nontrivial
        budgets"
    using conditions True
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_parameter_nontrivial_def
    by simp
  have zero_bound:
      "ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
        budgets < 1"
    by (rule
      ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error_lt_one[
        OF zero_conditions])
  show ?thesis
    using True zero_bound
    unfolding ro_absorb_checked_staged_conditioned_explicit_parameter_error_def
    by simp
next
  case False
  have nonempty_conditions:
      "ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_nontrivial
        budgets"
    using conditions False
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_parameter_nontrivial_def
    by simp
  have nonempty_bound:
      "ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
        budgets < 1"
    by (rule
      ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error_lt_one[
        OF nonempty_conditions])
  show ?thesis
    using False nonempty_bound
    unfolding ro_absorb_checked_staged_conditioned_explicit_parameter_error_def
    by simp
qed

corollary ro_absorb_stark_soundness_conditioned_explicit_nontrivial:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and parameter_conditions:
      "ro_absorb_checked_staged_conditioned_explicit_parameter_nontrivial budgets"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A < 1"
proof -
  have soundness:
      "ro_absorb_checked_staged_adversary_acceptance_probability A
        \<le> ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets"
    by (rule ro_absorb_stark_soundness_conditioned_explicit[
      OF false_statement wf controlled])
  have nontrivial:
      "ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets < 1"
    by (rule
      ro_absorb_checked_staged_conditioned_explicit_parameter_error_lt_one[
        OF parameter_conditions])
  show ?thesis
    by (rule le_less_trans[OF soundness nontrivial])
qed

end
end
