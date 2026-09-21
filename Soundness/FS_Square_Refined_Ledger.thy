theory FS_Square_Refined_Ledger
 imports FS_Refined_Soundness FS_Square_Accounted_Ledger
begin

section \<open>Source-connected refined conventional FS square ledger\<close>

text \<open>This equality expands the complete refined weighted alternative, not
  acceptance or the public minimum. The two MCA charges and eligible alpha
  charges use the proved builder envelope; every saved-prefix exception and
  the exact modulo sampling terms remain. Q counts original adaptive producer
  calls, including cached calls. The operational replay allowance is unchanged.\<close>

definition square_fs_refined_ledger :: "nat \<Rightarrow> nat \<Rightarrow> real" where
 "square_fs_refined_ledger F Q =
   real(133493*Q^2+2618301025*Q+8773058386762)/(2*real F) +
   (real Q+914610)*(square_modulo_base F 54953^640 + 2*square_modulo_base F 54954^640)"

context soundness
begin

lemma refined_nonempty_balance:
 "fs_refined_nonempty_error rT rC Q +
   (ro_mca_challenge_error (fs_replay_budgets Q) +
    ro_mca_challenge_error (fs_replay_budgets Q) +
    ro_checked_staged_first_root_robust_alpha_pivot_error (fs_replay_budgets Q)) =
  fs_accounted_nonempty_error rT rC Q + (fs_mca_error Q + fs_mca_error Q + fs_alpha_error Q)"
 by (simp add: fs_refined_nonempty_error_def fs_accounted_nonempty_error_def
   fs_refined_common_error_def fs_accounted_common_error_def algebra_simps)

lemma square_fs_refined_error_ledger:
 assumes schema: "spec=square_workload_spec clength a z"
   and geometry: "clength=1024" "scale=64" "powers=2"
   and repetitions: "rounds=640"
 shows "nn2real(fs_refined_nonempty_error 10581 10581 Q)=square_fs_refined_ledger size Q"
proof -
 have cap: "fri_mca_direct_cap=16384"
  unfolding fri_mca_direct_cap_def fri_mca_quarter_radii_def fri_canonical_domain_at_length
  using geometry by simp
 note budgets=fs_square_builder_budgets[OF schema geometry repetitions, of Q]
 have balance:
  "nn2real(fs_refined_nonempty_error 10581 10581 Q) +
    (21*(664*real Q+342450)^2+32776*(664*real Q+342450))/real size =
   square_fs_accounted_ledger size Q +
    (7*(real Q+342450)^2+32776*(real Q+342450))/real size"
  using arg_cong[OF refined_nonempty_balance[of 10581 10581 Q], where f=nn2real]
  apply (simp add: square_fs_accounted_error_ledger[OF schema geometry repetitions]
    ro_mca_challenge_error_def ro_checked_staged_first_root_robust_alpha_pivot_error_def
    fs_mca_error_def fs_alpha_error_def hash_collision_budget_value_def
    budgets cap square_nn2real_of_nat square_nnreal_power Let_def algebra_simps power2_eq_square)
  by (simp add: add_divide_distrib algebra_simps)
 show ?thesis
  unfolding square_fs_refined_ledger_def
  using balance unfolding square_fs_accounted_ledger_def
  by (simp add: add_divide_distrib algebra_simps power2_eq_square)
qed

lemma square_fs_refined_soundness:
 assumes schema: "spec=square_workload_spec clength a z"
   and geometry: "clength=1024" "scale=64" "powers=2"
   and repetitions: "rounds=640"
   and bound: "fs_query_bound Q P" and false_statement: "\<not>exists_valid_trace"
 shows "nn2real(fs_acceptance_probability P)\<le>square_fs_refined_ledger size Q"
proof -
 have alternative: "fs_refined_parameter_error 16 10581 10581 Q \<le>
     fs_refined_nonempty_error 10581 10581 Q"
  unfolding fs_refined_parameter_error_def
  using square_weighted_regime[OF schema geometry] by simp
 have source: "fs_acceptance_probability P\<le>fs_refined_nonempty_error 10581 10581 Q"
  by (rule order_trans[OF fs_refined_soundness[OF bound false_statement] alternative])
 show ?thesis
  unfolding square_fs_refined_error_ledger[OF schema geometry repetitions, of Q, symmetric]
  using source by simp
qed

end

ML \<open>
 List.app (fn th =>
   if null(Thm.hyps_of th) andalso null(Thm_Deps.all_oracles [th])
   then () else error "Unexpected refined source ledger dependency")
   @{thms soundness.refined_nonempty_balance
     soundness.square_fs_refined_error_ledger soundness.square_fs_refined_soundness};
\<close>
end
