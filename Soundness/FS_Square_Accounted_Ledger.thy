(* Title: Stark/FS_Square_Accounted_Ledger.thy
   License: BSD-3-Clause *)

theory FS_Square_Accounted_Ledger
  imports FS_Accounted_Soundness FS_Square_Replay_Soundness
begin

section \<open>Source-connected conventional FS square ledger\<close>

text \<open>This is the weighted alternative of the replay-aware public minimum,
  not an equality for acceptance or for the complete public bound. Every
  unchanged prefix, MCA and decoded-alpha charge is retained at its existing
  replay budget. The three eligible direct-experiment charges use one producer
  run plus the verifier. The exact modulo sampler and the sufficient 664Q
  operational allowance are unchanged. Q bounds calls of the original adaptive,
  privately randomized FS program; cached calls count again.\<close>

definition square_fs_accounted_ledger :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "square_fs_accounted_ledger F Q =
    real (18651111*Q^2 + 21752664601*Q + 12056674456762)/(2*real F) +
    (real Q+914610) *
      (square_modulo_base F 54953^640 + 2*square_modulo_base F 54954^640)"

context soundness
begin

lemma fs_accounted_common_balance:
  "fs_accounted_common_error Q +
      hash_collision_budget_value 0
        (ro_absorb_checked_staged_security_hash_query_budget_for (fs_replay_budgets Q)) =
    ro_mca_weighted_common_error (fs_replay_budgets Q) +
      hash_collision_budget_value 0 (fs_direct_hash_budget Q)"
  by (simp add: fs_accounted_common_error_def ro_mca_weighted_common_error_def
    algebra_simps)

lemma square_fs_accounted_error_ledger:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
    and repetitions: "rounds=640"
  shows "nn2real (fs_accounted_nonempty_error 10581 10581 Q) =
    square_fs_accounted_ledger size Q"
proof -
  note wf=fs_replay_budgets_wellformed[of Q]
  have direct: "fs_direct_hash_budget Q=Q+914610"
    unfolding fs_direct_hash_budget_def square_round_budget(4)[OF schema geometry]
    using repetitions by simp
  have replay: "ro_absorb_checked_staged_security_hash_query_budget_for
      (fs_replay_budgets Q)=664*Q+1257060"
    unfolding square_fs_replay_experiment_envelopes(2)[OF schema geometry]
    using repetitions by simp
  have common: "nn2real (ro_mca_weighted_common_error (fs_replay_budgets Q)) =
      real (9766448*Q^2 + 12539305712*Q + 4680748361546)/real size"
    unfolding square_common_error_ledger[OF schema geometry wf]
      square_fs_replay_allocation[OF schema geometry]
    by (simp add: repetitions square_fs_replay_common_polynomial square_nn2real_of_nat square_nnreal_power)
  have balance: "nn2real (fs_accounted_common_error Q) +
      (664*real Q+1257060)^2/real size =
    real (9766448*Q^2 + 12539305712*Q + 4680748361546)/real size +
      (real Q+914610)^2/real size"
    using arg_cong[OF fs_accounted_common_balance[of Q], where f=nn2real]
    by (simp add: common hash_collision_budget_value_def direct replay
      square_nn2real_of_nat algebra_simps power2_eq_square)
  have expanded:
    "nn2real (fs_accounted_nonempty_error 10581 10581 Q) =
      nn2real (fs_accounted_common_error Q) + (real Q+914610)/real size +
      (real Q+914610)*(square_modulo_base size 54953^640 +
        2*square_modulo_base size 54954^640) +
      5*(real Q+914610)*(real Q+914610-1)/(2*real size)"
    unfolding fs_accounted_nonempty_error_def fs_accounted_sampling_error_def
    by (simp add: direct square_nn2real_of_nat
      square_weighted_residual_ledger[OF schema geometry]
      ro_mca_weighted_connection_charge_real;
      simp add: repetitions add.assoc)
  show ?thesis
    unfolding expanded square_fs_accounted_ledger_def
    using balance
    by (simp add: add_divide_distrib algebra_simps power2_eq_square)
qed

lemma square_fs_accounted_soundness:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
    and repetitions: "rounds=640"
    and bound: "fs_query_bound Q P"
    and false_statement: "\<not>exists_valid_trace"
  shows "nn2real (fs_acceptance_probability P) \<le> square_fs_accounted_ledger size Q"
proof -
  have alternative: "fs_accounted_parameter_error 16 10581 10581 Q \<le>
      fs_accounted_nonempty_error 10581 10581 Q"
    unfolding fs_accounted_parameter_error_def
    using square_weighted_regime[OF schema geometry] by simp
  have source: "fs_acceptance_probability P \<le>
      fs_accounted_nonempty_error 10581 10581 Q"
    by (rule order_trans[OF fs_accounted_soundness[OF bound false_statement] alternative])
  show ?thesis
    unfolding square_fs_accounted_error_ledger[OF schema geometry repetitions, of Q, symmetric]
    using source by simp
qed

end

ML \<open>
  val checked = @{thms soundness.fs_accounted_common_balance
    soundness.square_fs_accounted_error_ledger soundness.square_fs_accounted_soundness};
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then writeln "Checked source ledger fact: no hidden hypotheses or proof oracles"
    else error "Unexpected source ledger proof dependency") checked;
\<close>
end
