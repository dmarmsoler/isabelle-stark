theory FS_Square_Prefix_Ledger
 imports FS_Prefix_Soundness FS_Square_Refined_Ledger
begin

section \<open>Source-connected prefix-refined conventional FS square ledger\<close>

text \<open>Expand the complete weighted alternative, not acceptance or the public
  minimum. An additive balance replaces exactly the two saved-query-prefix
  charges and keeps every other term, including the exact modulo powers.
  Q still counts original adaptive producer calls; operational allowances
  and the old certificates are unchanged.\<close>

definition square_fs_prefix_ledger :: "nat \<Rightarrow> nat \<Rightarrow> real" where
 "square_fs_prefix_ledger F Q =
   real(10613*Q^2+2470872425*Q+8773058386762)/(2*real F) +
   (real Q+914610)*(square_modulo_base F 54953^640 + 2*square_modulo_base F 54954^640)"

context soundness
begin

lemma prefix_nonempty_balance:
 "fs_prefix_nonempty_error rT rC Q +
   (ro_absorb_checked_staged_local_composition_prefix_target_error (fs_replay_budgets Q) +
    ro_checked_staged_local_query_phase_target_error (fs_replay_budgets Q)) =
  fs_refined_nonempty_error rT rC Q +
   (fs_composition_prefix_error Q + fs_query_phase_error Q)"
 by (simp add: fs_prefix_nonempty_error_def fs_refined_nonempty_error_def
   fs_prefix_common_error_def fs_refined_common_error_def algebra_simps)

lemma square_fs_prefix_budgets:
 assumes schema: "spec=square_workload_spec clength a z"
   and geometry: "clength=1024" "scale=64" "powers=2"
   and repetitions: "rounds=640"
 shows "fs_prefix_head_budget Q=Q+50"
   "fs_prefix_tail_budget=342400"
   "ro_checked_staged_query_head_hash_query_budget_for (fs_replay_budgets Q)=24*Q+50"
   "sum_list(query_opening_budgets (fs_replay_budgets Q))=640*Q"
   "ro_verifier_hash_query_budget=914610"
proof -
 have head: "ro_checked_staged_query_head_hash_query_budget_for (fs_replay_budgets q)=24*q+50"
   for q
   using square_prefix_budgets(2)[OF schema geometry fs_replay_budgets_wellformed[of q]]
   by (simp add: square_fs_replay_allocation[OF schema geometry] algebra_simps)
 show "fs_prefix_head_budget Q=Q+50"
   by (simp add: fs_prefix_head_budget_def head)
 show "fs_prefix_tail_budget=342400"
   unfolding fs_prefix_tail_budget_def
   using repetitions square_round_budget(1)[OF schema geometry]
   by simp
 show "ro_checked_staged_query_head_hash_query_budget_for (fs_replay_budgets Q)=24*Q+50"
   by (rule head)
 show "sum_list(query_opening_budgets (fs_replay_budgets Q))=640*Q"
   using square_fs_replay_allocation(3)[OF schema geometry, of Q]
   by (simp add: square_opening_budget_def repetitions)
 show "ro_verifier_hash_query_budget=914610"
   unfolding square_round_budget(4)[OF schema geometry]
   using repetitions by simp
qed

lemma square_fs_prefix_error_ledger:
 assumes schema: "spec=square_workload_spec clength a z"
   and geometry: "clength=1024" "scale=64" "powers=2"
   and repetitions: "rounds=640"
 shows "nn2real(fs_prefix_nonempty_error 10581 10581 Q)=square_fs_prefix_ledger size Q"
proof -
 note budgets=square_fs_prefix_budgets[OF schema geometry repetitions]
 note rb=square_round_budget[OF schema geometry]
 note md=square_budget_metadata[OF schema geometry]
 have balance:
  "nn2real(fs_prefix_nonempty_error 10581 10581 Q) +
   ((640*real Q+1257010)*(1+2*(24*real Q+50)) +
     (640*real Q+342400)*(20+2*(24*real Q+50)))/real size =
   square_fs_refined_ledger size Q +
   (1257010*(1+2*(real Q+50)) + 342400*(20+2*(real Q+50)))/real size"
  using arg_cong[OF prefix_nonempty_balance[of 10581 10581 Q], where f=nn2real]
  apply (simp only: nn2real_add square_fs_refined_error_ledger[OF schema geometry repetitions]
    ro_absorb_checked_staged_local_composition_prefix_target_error_def
    ro_checked_staged_local_query_phase_target_error_def
    fs_composition_prefix_error_def fs_query_phase_error_def
    budgets rb(1) md(3,4) Let_def)
  apply (simp add: repetitions square_nn2real_of_nat algebra_simps)
  by (simp add: add_divide_distrib algebra_simps)
 show ?thesis
  unfolding square_fs_prefix_ledger_def
  using balance unfolding square_fs_refined_ledger_def
  by (simp add: add_divide_distrib algebra_simps power2_eq_square)
qed

lemma square_fs_prefix_soundness:
 assumes schema: "spec=square_workload_spec clength a z"
   and geometry: "clength=1024" "scale=64" "powers=2"
   and repetitions: "rounds=640"
   and bound: "fs_query_bound Q P" and false_statement: "\<not>exists_valid_trace"
 shows "nn2real(fs_acceptance_probability P)\<le>square_fs_prefix_ledger size Q"
proof -
 have alternative: "fs_prefix_parameter_error 16 10581 10581 Q \<le>
     fs_prefix_nonempty_error 10581 10581 Q"
  unfolding fs_prefix_parameter_error_def
  using square_weighted_regime[OF schema geometry] by simp
 have source: "fs_acceptance_probability P\<le>fs_prefix_nonempty_error 10581 10581 Q"
  by (rule order_trans[OF fs_prefix_soundness[OF bound false_statement] alternative])
 show ?thesis
  unfolding square_fs_prefix_error_ledger[OF schema geometry repetitions, of Q, symmetric]
  using source by simp
qed

end

lemma square_fs_prefix_ledger_balance:
 "square_fs_prefix_ledger F Q + real(61440*Q^2+73714300*Q)/real F =
   square_fs_refined_ledger F Q"
 by (simp add: square_fs_prefix_ledger_def square_fs_refined_ledger_def
   add_divide_distrib algebra_simps power2_eq_square)

ML \<open>
 List.app (fn th =>
   if null(Thm.hyps_of th) andalso null(Thm_Deps.all_oracles [th])
   then () else error "Unexpected prefix source ledger dependency")
   @{thms soundness.prefix_nonempty_balance soundness.square_fs_prefix_budgets
     soundness.square_fs_prefix_error_ledger soundness.square_fs_prefix_soundness
     square_fs_prefix_ledger_balance};
\<close>

end
