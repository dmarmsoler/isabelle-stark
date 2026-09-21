theory Soundness_FRI_Conditioned_Explicit_All_Rounds_Bound
  imports Stark.Soundness_FRI_Conditioned_Explicit_Zero_Round_Parameter_Bound
begin

context soundness
begin

definition ro_absorb_checked_staged_conditioned_explicit_parameter_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets =
    (if ceil_log clength = 0
     then
       ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
         budgets
     else
       ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
         budgets)"

theorem ro_absorb_stark_soundness_conditioned_explicit:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "ro_absorb_checked_staged_adversary_acceptance_probability A
      \<le> ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets"
proof (cases "ceil_log clength = 0")
  case True
  have
      "ro_absorb_checked_staged_adversary_acceptance_probability A
        \<le>
        ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error
          budgets"
    by (rule
      ro_absorb_stark_soundness_conditioned_explicit_zero_round[
        OF false_statement True wf controlled])
  then show ?thesis
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_parameter_error_def
    using True by simp
next
  case False
  have nonempty: "0 < ceil_log clength"
    using False by simp
  have
      "ro_absorb_checked_staged_adversary_acceptance_probability A
        \<le>
        ro_absorb_checked_staged_conditioned_explicit_nonempty_parameter_error
          budgets"
    by (rule
      ro_absorb_stark_soundness_conditioned_explicit_nonempty[
        OF false_statement wf controlled nonempty])
  then show ?thesis
    unfolding
      ro_absorb_checked_staged_conditioned_explicit_parameter_error_def
    using False by simp
qed

end
end
