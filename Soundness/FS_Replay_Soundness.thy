(* Title: Stark/FS_Replay_Soundness.thy
   License: BSD-3-Clause *)

theory FS_Replay_Soundness
  imports FS_Replay_Allowance Soundness_Square_Uniform_Soundness
begin

section \<open>Conventional Fiat--Shamir soundness through adaptive replay\<close>

text \<open>The original query-bounded producer is connected to the unchanged
  public staged theorem through its oracle-independent private-program mixture.
  Staged wellformedness and all-state control follow from the actual compiler.
  No valid-transcript, successful-run, freshness or completed-map premise is
  added. This uses the existing terminating finite-support classical syntax.

  For the square workload, retain the compiler's actual early, middle and
  opening allocation. The source ledger already has a joint-allocation maximum;
  using this specific vector avoids that relaxation without changing its
  definitions. The total and experiment formulas below are declared allowance
  and hash envelopes, not equalities for all actual execution call counts.
  No numerical security target is certified here.\<close>

context soundness
begin

theorem fs_replay_soundness:
  assumes bound: "fs_query_bound Q P" and false_statement: "\<not>exists_valid_trace"
  shows "fs_acceptance_probability P \<le>
    ro_mca_weighted_parameter_error N rT rC (fs_replay_budgets Q)"
proof (rule fs_compiled_staged_bound_suffices[OF bound, where A=A])
  fix T :: "('f,'f list) fs_program"
  assume fixed: "fs_fixed T" and capped: "fs_query_bound Q T"
  have "ro_absorb_checked_staged_adversary_acceptance_probability
      (fs_compile_replay A T) \<le>
    ro_mca_weighted_parameter_error N rT rC (fs_replay_budgets Q)"
    by (rule ro_absorb_stark_soundness_mca_weighted[OF false_statement
      fs_replay_budgets_wellformed fs_compile_replay_controlled[OF capped fixed]])
  then show "wp_event (ro_absorb_checked_staged_security_experiment (fs_compile_replay A T))
      accepted adversary_initial_state \<le>
      ro_mca_weighted_parameter_error N rT rC (fs_replay_budgets Q)"
    unfolding ro_absorb_checked_staged_adversary_acceptance_probability_def
    by (simp add: wp_event_def accepted_def)
qed

subsection \<open>Actual square allocation and experiment envelopes\<close>

lemma square_fs_replay_allocation:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
  shows "square_early_budget (fs_replay_budgets Q) = 2*Q"
    "square_middle_budget (fs_replay_budgets Q) = 22*Q"
    "square_opening_budget (fs_replay_budgets Q) = rounds*Q"
    "staged_attacker_query_budget (fs_replay_budgets Q) = (rounds+24)*Q"
  using square_budget_metadata[OF schema geometry]
  by (simp_all add: square_early_budget_def square_middle_budget_def
    square_opening_budget_def fs_replay_budgets_def staged_attacker_query_budget_def
    sum_list_replicate algebra_simps)

lemma square_fs_replay_experiment_envelopes:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
  shows "ro_checked_staged_transcript_hash_query_budget_for (fs_replay_budgets Q) =
      (rounds+24)*Q+50+535*rounds"
    "ro_absorb_checked_staged_security_hash_query_budget_for (fs_replay_budgets Q) =
      (rounds+24)*Q+100+1964*rounds"
  using square_total_budget[OF schema geometry, of "fs_replay_budgets Q"]
  by (simp_all only: square_fs_replay_allocation(4)[OF schema geometry])

theorem square_fs_replay_soundness:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
    and false_statement: "\<not>exists_valid_trace"
    and bound: "fs_query_bound Q P"
  shows "nn2real (fs_acceptance_probability P) \<le>
    square_weighted_ledger size rounds (2*Q) (22*Q) (rounds*Q)"
proof -
  have source: "nn2real (fs_acceptance_probability P) \<le>
    nn2real (ro_mca_weighted_parameter_error 16 10581 10581 (fs_replay_budgets Q))"
    using fs_replay_soundness[OF bound false_statement, where N=16 and rT=10581 and rC=10581]
    by simp
  have ledger: "nn2real (ro_mca_weighted_parameter_error 16 10581 10581
      (fs_replay_budgets Q)) \<le>
    square_weighted_ledger size rounds (2*Q) (22*Q) (rounds*Q)"
    using square_public_error_le_ledger[OF schema geometry fs_replay_budgets_wellformed]
    by (simp only: square_fs_replay_allocation[OF schema geometry])
  show ?thesis by (rule order_trans[OF source ledger])
qed

corollary square_fs_replay_uniform_soundness:
  assumes schema: "spec=square_workload_spec clength a z"
    and geometry: "clength=1024" "scale=64" "powers=2"
    and false_statement: "\<not>exists_valid_trace"
    and bound: "fs_query_bound Q P"
  shows "nn2real (fs_acceptance_probability P) \<le>
    square_uniform_ledger size rounds ((rounds+24)*Q)"
  by (rule order_trans[OF square_fs_replay_soundness[OF assms]
    square_weighted_ledger_allocation_bound]) (simp add: algebra_simps)

end

ML \<open>
  val checked = @{thms soundness.fs_replay_soundness soundness.square_fs_replay_allocation
    soundness.square_fs_replay_experiment_envelopes soundness.square_fs_replay_soundness
    soundness.square_fs_replay_uniform_soundness};
  List.app (fn th =>
    if null(Thm.hyps_of th) andalso null(Thm_Deps.all_oracles [th])
    then () else error "Unexpected conventional FS soundness dependency") checked;
  writeln ("Conventional FS checked conclusions: " ^ Int.toString(length checked));
  if Thm.nprems_of @{thm soundness.fs_replay_soundness}=3
  then () else error "Unexpected conventional FS premise count";
\<close>
end
