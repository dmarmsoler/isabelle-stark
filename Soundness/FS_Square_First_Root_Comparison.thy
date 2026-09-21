theory FS_Square_First_Root_Comparison
 imports "Stark.FS_Square_First_Root_Ledger" "Stark.FS_Square_Prefix_Ledger"
begin

section \<open>Exact comparison of the first-root and prefix ledgers\<close>

text \<open>Keep this closed algebra outside the large concrete soundness context.
  It compares sufficient ledgers, not actual acceptance probabilities.\<close>

lemma square_fs_first_root_ledger_balance:
 "square_fs_first_root_ledger F Q + real(5296*Q^2+3206956*Q)/real F =
   square_fs_prefix_ledger F Q"
 by (simp add: square_fs_first_root_ledger_def square_fs_prefix_ledger_def
   add_divide_distrib algebra_simps power2_eq_square)

lemma square_fs_first_root_ledger_le_prefix:
 "square_fs_first_root_ledger F Q \<le> square_fs_prefix_ledger F Q"
 proof -
 have nonnegative: "0\<le>real(5296*Q^2+3206956*Q)/real F"
  by (rule divide_nonneg_nonneg) simp_all
 show ?thesis using square_fs_first_root_ledger_balance[of F Q] nonnegative
  by linarith
qed

ML \<open>
 List.app (fn th => if null(Thm.hyps_of th) andalso Thm.nprems_of th=0
   andalso null(Thm_Deps.all_oracles [th]) then ()
   else error "Unexpected first-root comparison dependency")
   @{thms square_fs_first_root_ledger_balance square_fs_first_root_ledger_le_prefix};
\<close>
end
