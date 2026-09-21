theory Soundness_FRI_Conditioned_Explicit_Security_Target
  imports Stark.Soundness_FRI_Conditioned_Explicit_Residual_Projection_Obstruction
begin

section \<open>Generic component allocations for a bit-security target\<close>

text \<open>
  A component allocation is only a proof interface for the existing exact sum:
  it does not change or tighten the parameter error.  The all-round list selects
  the same zero or nonempty branch as the public endpoint.
\<close>

lemma list_all2_le_imp_sum_list_le:
  fixes xs ys :: "prob list"
  assumes "list_all2 (\<le>) xs ys"
  shows "sum_list xs \<le> sum_list ys"
  using assms
  by (induction rule: list_all2_induct) (simp_all add: add_mono)

context soundness
begin

definition all_round_parameter_error_components
  :: "staged_budgets \<Rightarrow> prob list"
where
  "all_round_parameter_error_components budgets =
    (if ceil_log clength = 0
     then zero_round_parameter_error_components budgets
     else nonempty_parameter_error_components budgets)"

lemma all_round_parameter_error_eq_sum_list:
  "ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets =
    sum_list (all_round_parameter_error_components budgets)"
  unfolding
    ro_absorb_checked_staged_conditioned_explicit_parameter_error_def
    all_round_parameter_error_components_def
  by (cases "ceil_log clength = 0")
    (simp_all add: zero_round_parameter_error_eq_sum_list
      nonempty_parameter_error_eq_sum_list)

lemma all_round_parameter_error_le_security_target_from_components:
  assumes components:
      "list_all2 (\<le>)
        (all_round_parameter_error_components budgets) component_caps"
    and caps:
      "sum_list component_caps \<le>
        soundness_security_target security_bits"
  shows
    "ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets \<le>
      soundness_security_target security_bits"
proof -
  have
      "sum_list (all_round_parameter_error_components budgets) \<le>
        sum_list component_caps"
    by (rule list_all2_le_imp_sum_list_le[OF components])
  also have "... \<le> soundness_security_target security_bits"
    by (rule caps)
  finally show ?thesis
    unfolding all_round_parameter_error_eq_sum_list .
qed

lemma all_round_parameter_error_le_security_target_from_branches:
  assumes zero:
      "ceil_log clength = 0 \<Longrightarrow>
        ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
          budgets
        \<le> soundness_security_target security_bits"
    and nonempty:
      "0 < ceil_log clength \<Longrightarrow>
        ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
          budgets
        \<le> soundness_security_target security_bits"
  shows
    "ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets \<le>
      soundness_security_target security_bits"
proof (cases "ceil_log clength = 0")
  case True
  then show ?thesis
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_parameter_error_def
    using zero by simp
next
  case False
  then have positive: "0 < ceil_log clength"
    by simp
  then show ?thesis
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_parameter_error_def
    using False nonempty by simp
qed

theorem ro_absorb_stark_soundness_conditioned_explicit_security_target:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and components:
      "list_all2 (\<le>)
        (all_round_parameter_error_components budgets) component_caps"
    and caps:
      "sum_list component_caps \<le>
        soundness_security_target security_bits"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A \<le>
      soundness_security_target security_bits"
proof -
  have soundness:
      "ro_absorb_checked_staged_adversary_acceptance_probability A \<le>
        ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets"
    by (rule ro_absorb_stark_soundness_conditioned_explicit[
      OF false_statement wf controlled])
  have arithmetic:
      "ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets \<le>
        soundness_security_target security_bits"
    by (rule
      all_round_parameter_error_le_security_target_from_components[
        OF components caps])
  show ?thesis
    by (rule order_trans[OF soundness arithmetic])
qed

end

end
