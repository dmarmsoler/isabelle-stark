theory FS_Square_First_Root_Ledger
 imports "Stark.FS_First_Root_Soundness"
begin

section \<open>Source-connected square ledger with first-root accounting\<close>

text \<open>Expand the complete error from generic budget facts, without importing
  concrete locale interpretations. Exact modulo sampling and all other charges
  remain unchanged. This is a symbolic source equality, not a new bit target.\<close>

definition square_fs_first_root_ledger :: "nat \<Rightarrow> nat \<Rightarrow> real" where
 "square_fs_first_root_ledger F Q =
   real(21*Q^2+2464458513*Q+8773058386762)/(2*real F) +
   (real Q+914610)*(square_modulo_base F 54953^640 + 2*square_modulo_base F 54954^640)"

context soundness
begin

lemma first_root_nonempty_balance:
 "fs_first_root_nonempty_error rT rC Q +
   (ro_absorb_checked_staged_first_root_prefix_merkle_target_error (fs_replay_budgets Q) +
    ro_checked_staged_first_root_prefix_merkle_target_error (fs_replay_budgets Q)) =
  fs_prefix_nonempty_error rT rC Q +
   (fs_first_root_security_error Q + fs_first_root_builder_error Q)"
 by (simp add: fs_first_root_nonempty_error_def fs_prefix_nonempty_error_def
   fs_first_root_common_error_def fs_prefix_common_error_def
   fs_first_root_alpha_error_def fs_alpha_error_def algebra_simps)

lemma square_fs_first_root_budgets:
 assumes schema: "spec=square_workload_spec clength a z"
   and geometry: "clength=1024" "scale=64" "powers=2"
   and repetitions: "rounds=640"
 shows "fs_first_root_tail=342448"
   "ro_checked_staged_after_first_root_with_query_hash_query_budget_for (fs_replay_budgets Q)=662*Q+342448"
   "staged_trace_fri_search_queries (fs_replay_budgets Q)0=2*Q"
   "ro_verifier_hash_query_budget=914610"
   "fs_prefix_head_budget Q=Q+50"
   "fs_prefix_tail_budget=342400"
proof -
 have tail: "ro_checked_staged_after_first_root_with_query_hash_query_budget_for
    (fs_replay_budgets q)=662*q+342448" for q
  using square_prefix_budgets(4)[OF schema geometry fs_replay_budgets_wellformed[of q]]
  apply (simp only: square_fs_replay_allocation[OF schema geometry])
  using repetitions by (simp add: algebra_simps)
 show "fs_first_root_tail=342448" by (simp add: fs_first_root_tail_def tail)
 show "ro_checked_staged_after_first_root_with_query_hash_query_budget_for
    (fs_replay_budgets Q)=662*Q+342448" by (rule tail)
 show "staged_trace_fri_search_queries (fs_replay_budgets Q)0=2*Q"
  using square_prefix_budgets(1)[OF schema geometry fs_replay_budgets_wellformed[of Q]]
  by (simp add: square_fs_replay_allocation[OF schema geometry])
 show "ro_verifier_hash_query_budget=914610"
  unfolding square_round_budget(4)[OF schema geometry] using repetitions by simp
 show "fs_prefix_head_budget Q=Q+50"
  unfolding fs_prefix_head_budget_def
  using square_prefix_budgets(2)[OF schema geometry fs_replay_budgets_wellformed[of 0]]
  by (simp add: square_fs_replay_allocation[OF schema geometry])
 show "fs_prefix_tail_budget=342400"
  unfolding fs_prefix_tail_budget_def square_round_budget(1)[OF schema geometry]
  using repetitions by simp
qed

lemma square_fs_first_root_error_ledger:
 assumes schema: "spec=square_workload_spec clength a z"
   and geometry: "clength=1024" "scale=64" "powers=2"
   and repetitions: "rounds=640"
 shows "nn2real(fs_first_root_nonempty_error 10581 10581 Q)=square_fs_first_root_ledger size Q"
proof -
 note budgets=square_fs_first_root_budgets[OF schema geometry repetitions]
 note builder=fs_square_builder_budgets[OF schema geometry repetitions]
 note md=square_budget_metadata[OF schema geometry]
 have direct: "fs_direct_hash_budget Q=Q+914610"
  by (simp add: fs_direct_hash_budget_def budgets)
 have cap: "fri_mca_direct_cap=16384"
  unfolding fri_mca_direct_cap_def fri_mca_quarter_radii_def fri_canonical_domain_at_length
  using geometry by simp
 show ?thesis
  unfolding fs_first_root_nonempty_error_def fs_first_root_common_error_def
    fs_first_root_security_error_def fs_first_root_builder_error_def
    fs_composition_prefix_error_def fs_query_phase_error_def
    fs_first_root_alpha_error_def fs_mca_error_def
    ro_absorb_checked_staged_fri_builder_merkle_target_error_def
    hash_collision_budget_value_def fs_accounted_sampling_error_def Let_def
  apply (simp only: budgets builder md direct cap fs_first_root_builder_error_def)
  apply (simp add: square_nn2real_of_nat square_nnreal_power
    square_weighted_residual_ledger[OF schema geometry]
    ro_mca_weighted_connection_charge_real)
  using repetitions
  by (simp add: square_fs_first_root_ledger_def add_divide_distrib algebra_simps power2_eq_square)
qed

lemma square_fs_first_root_soundness:
 assumes schema: "spec=square_workload_spec clength a z"
   and geometry: "clength=1024" "scale=64" "powers=2"
   and repetitions: "rounds=640"
   and bound: "fs_query_bound Q P" and false_statement: "\<not>exists_valid_trace"
 shows "nn2real(fs_acceptance_probability P)\<le>square_fs_first_root_ledger size Q"
proof -
 have alternative: "fs_first_root_parameter_error 16 10581 10581 Q \<le>
     fs_first_root_nonempty_error 10581 10581 Q"
  unfolding fs_first_root_parameter_error_def
  using square_weighted_regime[OF schema geometry] by simp
 have source: "fs_acceptance_probability P\<le>fs_first_root_nonempty_error 10581 10581 Q"
  by (rule order_trans[OF fs_first_root_soundness[OF bound false_statement] alternative])
 show ?thesis
  unfolding square_fs_first_root_error_ledger[OF schema geometry repetitions, of Q, symmetric]
  using source by simp
qed

end

ML \<open>
 List.app (fn th =>
   if null(Thm.hyps_of th) andalso null(Thm_Deps.all_oracles [th])
   then () else error "Unexpected first-root source ledger dependency")
   @{thms soundness.first_root_nonempty_balance soundness.square_fs_first_root_budgets
     soundness.square_fs_first_root_error_ledger soundness.square_fs_first_root_soundness};
\<close>
end
