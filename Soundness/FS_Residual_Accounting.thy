(* Title: Stark/FS_Residual_Accounting.thy
   License: BSD-3-Clause *)

theory FS_Residual_Accounting
  imports "FS_Probability_Accounting"
    "Soundness_FRI_Weighted_Residual_Union"
    "Soundness_FRI_Weighted_Verifier_Logging"
begin

section \<open>Replay-aware accounting for the weighted clean residual\<close>

text \<open>The path-union event is a final-map observation. Its direct experiment
  budget counts one producer run and the verifier, while the support bridge
  still uses the unchanged staged compiler allowances. No saved-prefix
  exception is removed from the complete classification.\<close>

context soundness
begin

lemma fs_accounting_logged:
  assumes "fs_query_bound Q P"
  shows "lc_program (fs_direct_hash_budget Q) (fs_security_experiment P)"
  unfolding fs_direct_hash_budget_def fs_security_experiment_def
  by (rule lc_bind)
    (rule lc_controlled[OF fs_run_controlled[OF assms]],
     rule lc_program_ro_verifier_after_adversary)

lemma fs_accounting_weighted_residual:
  assumes "fs_query_bound Q P"
  shows "wp_event (fs_security_experiment P) (jrp_event N rT rC n j)
      adversary_initial_state \<le>
    nnreal (fs_direct_hash_budget Q)*ro_mca_weighted_residual_power_sum rT rC n +
      fc_charge ({}::'f set) (fs_direct_hash_budget Q) 0"
  by (rule jrp_program_bound[OF fs_accounting_logged[OF assms]]) simp

lemma fs_accounting_jrp_ignores:
  "fs_ignores_transcript (\<lambda>out. if jrp_event N rT rC n j out then 1 else 0)"
  by (simp add: fs_ignores_transcript_def jrp_event_def lpu_event_def cau_event_def)

lemma fs_accounting_jrp_compile:
  assumes "fs_fixed P" "fs_query_bound Q P"
  shows "wp_event (ro_absorb_checked_staged_security_experiment (fs_compile_replay A P))
      (jrp_event N rT rC n j) adversary_initial_state =
    wp_event (fs_security_experiment P) (jrp_event N rT rC n j) adversary_initial_state"
  using fs_compile_replay_wp[OF assms,
    where A=A and base=adversary_initial_state
      and F="\<lambda>out. if jrp_event N rT rC n j out then 1 else 0"]
  by (simp add: fs_accounting_jrp_ignores wp_event_def
      verifier_state_from_adversary_def adversary_initial_state_def)


lemma fs_accounting_jrp_mixture:
  assumes "fs_query_bound Q P"
  shows "wp_event (fs_compiled_mixture A P) (jrp_event N rT rC n j) adversary_initial_state =
    wp_event (fs_security_experiment P) (jrp_event N rT rC n j) adversary_initial_state"
  using fs_compiled_mixture_wp[OF assms,
    where A=A and base=adversary_initial_state
      and F="\<lambda>out. if jrp_event N rT rC n j out then 1 else 0"]
  by (simp add: fs_accounting_jrp_ignores wp_event_def
      verifier_state_from_adversary_def adversary_initial_state_def)

lemma fs_accounting_mixture_residual:
  assumes "fs_query_bound Q P"
  shows "wp_event (fs_compiled_mixture A P) (jrp_event N rT rC n j)
      adversary_initial_state \<le>
    nnreal (fs_direct_hash_budget Q)*ro_mca_weighted_residual_power_sum rT rC n +
      fc_charge ({}::'f set) (fs_direct_hash_budget Q) 0"
  unfolding fs_accounting_jrp_mixture[OF assms]
  by (rule fs_accounting_weighted_residual[OF assms])

lemma fs_accounting_jrp_witness_erase:
  "wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
      (jrp_event N rT rC n j) s =
    wp_event (ro_absorb_checked_staged_security_experiment A)
      (jrp_event N rT rC n j) s"
  unfolding jre_witness_path_probability
  using jre_path_map[where m="ro_absorb_checked_staged_security_experiment_with_data_state A"
    and f=snd and N=N and rT=rT and rC=rC and n=n and j=j and s=s]
  by (simp only: ro_absorb_checked_staged_security_experiment_with_data_state_projection)

lemma fs_accounting_compiled_clean_residual:
  assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
    and nonempty: "0<ceil_log clength" and positive: "0<rounds"
    and power: "clength*scale=2^N"
    and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log(maxDegree+1)\<le>N"
  shows "wp_event
    (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      (fs_compile_replay A P))
    (jre_event N rT rC) adversary_initial_state \<le>
    nnreal (fs_direct_hash_budget Q)*ro_mca_weighted_residual_power_sum rT rC rounds +
      fc_charge ({}::'f set) (fs_direct_hash_budget Q) 0"
proof -
  let ?run="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
    (fs_compile_replay A P)"
  have wf: "staged_budget_wellformed (fs_replay_budgets Q)"
    by (rule fs_replay_budgets_wellformed)
  have controlled: "staged_adversary_controlled (fs_replay_budgets Q) (fs_compile_replay A P)"
    by (rule fs_compile_replay_controlled[OF bound fixed])
  have "wp_event ?run (jre_event N rT rC) adversary_initial_state \<le>
    wp_event ?run (jrp_event N rT rC rounds 0) adversary_initial_state"
    unfolding wp_event_def
    by (rule wp_mono_on_support)
      (use jre_on_support[OF wf controlled nonempty positive power lenf lenc] in auto)
  also have "... = wp_event (fs_security_experiment P)
    (jrp_event N rT rC rounds 0) adversary_initial_state"
    by (simp only: fs_accounting_jrp_witness_erase fs_accounting_jrp_compile[OF fixed bound])
  also have "... \<le>
    nnreal (fs_direct_hash_budget Q)*ro_mca_weighted_residual_power_sum rT rC rounds +
      fc_charge ({}::'f set) (fs_direct_hash_budget Q) 0"
    by (rule fs_accounting_weighted_residual[OF bound])
  finally show ?thesis .
qed

lemma fs_accounting_private_clean_residual:
  assumes bound: "fs_query_bound Q P"
    and nonempty: "0<ceil_log clength" and positive: "0<rounds"
    and power: "clength*scale=2^N"
    and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log(maxDegree+1)\<le>N"
  shows "dist_expect (fs_normalize P)
    (\<lambda>T. wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        (fs_compile_replay A T))
      (jre_event N rT rC) adversary_initial_state) \<le>
    nnreal (fs_direct_hash_budget Q)*ro_mca_weighted_residual_power_sum rT rC rounds +
      fc_charge ({}::'f set) (fs_direct_hash_budget Q) 0"
proof (rule fs_expect_le_const)
  fix T assume member: "T\<in>set_dist(fs_normalize P)"
  have fixed: "fs_fixed T" by (rule fs_normalize_fixed[OF member])
  have queries: "fs_query_bound Q T" by (rule fs_normalize_bound[OF bound member])
  show "wp_event
    (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      (fs_compile_replay A T))
    (jre_event N rT rC) adversary_initial_state \<le>
    nnreal (fs_direct_hash_budget Q)*ro_mca_weighted_residual_power_sum rT rC rounds +
      fc_charge ({}::'f set) (fs_direct_hash_budget Q) 0"
    by (rule fs_accounting_compiled_clean_residual[OF fixed queries nonempty positive power lenf lenc])
qed

end

end
