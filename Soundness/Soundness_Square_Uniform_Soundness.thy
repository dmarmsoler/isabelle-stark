(* Title: Stark/Soundness_Square_Uniform_Soundness.thy
   License: BSD-3-Clause *)

theory Soundness_Square_Uniform_Soundness
  imports Soundness_Square_Allocation_Bound
begin

section \<open>Square-workload soundness under a total staged budget cap\<close>

text \<open>This is a corollary of the unchanged public theorem. The displayed
  schema and geometry specialize existing parameters, and the cap bounds the
  total declared staged allowance. Wellformedness and adversary control are
  retained; actual executions may spend less. No premise is added to the
  existing locale or public theorem. No model change, target level or concrete
  profile is introduced.
  The result is an upper bound, not an assertion that an execution attains it.\<close>

context soundness
begin

lemma square_public_error_at_most_budget:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
    and wf: "staged_budget_wellformed budgets"
    and cap: "staged_attacker_query_budget budgets \<le> Q"
  shows "nn2real (ro_mca_weighted_parameter_error 16 10581 10581 budgets) \<le>
    square_uniform_ledger size rounds Q"
proof -
  have total: "square_early_budget budgets + square_middle_budget budgets +
      square_opening_budget budgets \<le> Q"
    using square_budget_partition[of budgets] cap by simp
  show ?thesis
    by (rule order_trans[OF square_public_error_le_ledger[OF schema geometry wf]
      square_weighted_ledger_at_most_budget[OF total]])
qed

theorem square_soundness_at_most_budget:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
    and false_statement: "\<not>exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cap: "staged_attacker_query_budget budgets \<le> Q"
  shows "nn2real (ro_absorb_checked_staged_adversary_acceptance_probability A) \<le>
    square_uniform_ledger size rounds Q"
proof -
  have acceptance: "nn2real (ro_absorb_checked_staged_adversary_acceptance_probability A) \<le>
      nn2real (ro_mca_weighted_parameter_error 16 10581 10581 budgets)"
    using ro_absorb_stark_soundness_mca_weighted[OF false_statement wf controlled,
      of 16 10581 10581] by simp
  show ?thesis
    by (rule order_trans[OF acceptance
      square_public_error_at_most_budget[OF schema geometry wf cap]])
qed

end

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then writeln ("Checked source comparison, displayed premises: " ^
      string_of_int (Thm.nprems_of th))
    else error "Unexpected source comparison dependency")
    @{thms soundness.square_public_error_at_most_budget
      soundness.square_soundness_at_most_budget};
\<close>

end
