(* Title: Stark/Soundness_Square_Prefix_Budgets.thy
   License: BSD-3-Clause *)

theory Soundness_Square_Prefix_Budgets
  imports Soundness_Square_Budget_Counts
    Stark.Soundness_FRI_Query_Head_Range
begin

section \<open>Exact prefix budgets for the reference square workload\<close>

text \<open>The existing staged wellformedness premise identifies the first
  trace-FRI stage. The identities preserve every later attacker allocation and
  every builder/verifier budget charge. The subtraction formula is accompanied
  by its nonnegativity proof; it is not a truncated-budget approximation.\<close>

context soundness
begin
lemma square_prefix_budgets:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
    and wf: "staged_budget_wellformed budgets"
  shows "staged_trace_fri_search_queries budgets 0 = square_early_budget budgets"
    "ro_checked_staged_query_head_hash_query_budget_for budgets =
      square_early_budget budgets + square_middle_budget budgets + 50"
    "ro_checked_staged_after_first_root_hash_query_budget_for budgets =
      square_middle_budget budgets + 48"
    "ro_checked_staged_after_first_root_with_query_hash_query_budget_for budgets =
      square_middle_budget budgets + square_opening_budget budgets + 48 + 535*rounds"
proof -
  note md=square_budget_metadata[OF schema geometry]
  note rb=square_round_budget[OF schema geometry]
  show early: "staged_trace_fri_search_queries budgets 0 = square_early_budget budgets"
    by (simp add: staged_trace_fri_search_queries_def square_early_budget_def)
  show head: "ro_checked_staged_query_head_hash_query_budget_for budgets =
      square_early_budget budgets + square_middle_budget budgets + 50"
    using ro_checked_staged_query_head_plus_opening_budget[of budgets]
      square_budget_partition[of budgets] md
    unfolding square_opening_budget_def[symmetric] by arith
  have nonempty: "0<ceil_log clength" using md by simp
  note split=ro_checked_staged_query_head_budget_split[OF nonempty wf]
  show after: "ro_checked_staged_after_first_root_hash_query_budget_for budgets =
      square_middle_budget budgets + 48"
    using split head early by arith
  show "ro_checked_staged_after_first_root_with_query_hash_query_budget_for budgets =
      square_middle_budget budgets + square_opening_budget budgets + 48 + 535*rounds"
    unfolding ro_checked_staged_after_first_root_with_query_hash_query_budget_for_def
      square_opening_budget_def
    by (simp add: after rb algebra_simps)
qed

lemma square_after_root_budget_exact_subtraction:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
    and wf: "staged_budget_wellformed budgets"
  shows "square_early_budget budgets + 2 \<le>
      ro_checked_staged_transcript_hash_query_budget_for budgets"
    "ro_checked_staged_after_first_root_with_query_hash_query_budget_for budgets =
      ro_checked_staged_transcript_hash_query_budget_for budgets -
        square_early_budget budgets - 2"
proof -
  have exact: "square_early_budget budgets + 2 +
      ro_checked_staged_after_first_root_with_query_hash_query_budget_for budgets =
      ro_checked_staged_transcript_hash_query_budget_for budgets"
    using square_prefix_budgets(4)[OF schema geometry wf]
      square_total_budget(1)[OF schema geometry]
      square_budget_partition[of budgets] by arith
  show "square_early_budget budgets + 2 \<le>
      ro_checked_staged_transcript_hash_query_budget_for budgets"
    using exact by arith
  show "ro_checked_staged_after_first_root_with_query_hash_query_budget_for budgets =
      ro_checked_staged_transcript_hash_query_budget_for budgets -
        square_early_budget budgets - 2"
    using exact by arith
qed

end

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then writeln ("Checked prefix theorem, displayed premises: " ^
      string_of_int (Thm.nprems_of th))
    else error "Unexpected prefix proof dependency")
    @{thms soundness.square_prefix_budgets
      soundness.square_after_root_budget_exact_subtraction};
\<close>
end
