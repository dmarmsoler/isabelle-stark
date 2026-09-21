
theory FS_Refined_Soundness
 imports FS_Alpha_Accounting FS_Accounted_Soundness
begin

section \<open>Complete conventional FS soundness with refined builder charges\<close>

text \<open>The existing ten-event classification is unchanged. Two MCA charges
  and the eligible parts of decoded-alpha now use the single-run builder budget
  and constructor-aware drift bounds. Four outer prefix/target charges and the
  saved-first-root alpha exception retain their prior charges. The earlier
  complete bound remains available as a minimum and outside-regime fallback.
  The public theorem has the same two premises and covers the existing adaptive
  private-randomness model. No new concrete security profile is asserted.\<close>

context soundness
begin

definition fs_mca_error where
 "fs_mca_error Q = nnreal(fs_builder_fresh_budget Q*
   (fri_mca_direct_cap+(2*fs_builder_fresh_budget Q+2)))/nnreal size"

lemma fs_compiled_trace_security_bad:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and ep: "clength*scale=2^N" and fit: "Suc(ceil_log clength)\<le>N"
   and rate: "4*fri_padded_degree_bound(clength-1)\<le>clength*scale"
 shows "wp_event
   (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses(fs_compile_replay A P))
   (ro_mca_security_bad True) adversary_initial_state \<le> fs_mca_error Q"
 unfolding ro_mca_security_bad_def
proof (rule order_trans[OF wp_ro_absorb_checked_staged_security_builder_head_event_le])
 show "wp_event (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses(fs_compile_replay A P))
   (ro_mca_builder_bad True) adversary_initial_state \<le> fs_mca_error Q"
   using fs_compiled_trace_mca_bad[OF fixed bound ep fit rate, where A=A]
   unfolding ro_mca_builder_bad_def fs_mca_error_def by simp
qed

lemma fs_compiled_composition_security_bad:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and ep: "clength*scale=2^N" and fit: "Suc(ceil_log(Suc maxDegree))\<le>N"
   and rate: "4*fri_padded_degree_bound maxDegree\<le>clength*scale"
 shows "wp_event
   (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses(fs_compile_replay A P))
   (ro_mca_security_bad False) adversary_initial_state \<le> fs_mca_error Q"
 unfolding ro_mca_security_bad_def
proof (rule order_trans[OF wp_ro_absorb_checked_staged_security_builder_head_event_le])
 show "wp_event (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses(fs_compile_replay A P))
   (ro_mca_builder_bad False) adversary_initial_state \<le> fs_mca_error Q"
   using fs_compiled_composition_mca_bad[OF fixed bound ep fit rate, where A=A]
   unfolding ro_mca_builder_bad_def fs_mca_error_def by simp
qed

lemma fs_compiled_alpha_security:
 assumes false_statement: "\<not>exists_valid_trace"
   and fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and nonempty: "0<ceil_log clength"
 shows "wp_event
   (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses(fs_compile_replay A P))
   ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent
   adversary_initial_state \<le> fs_alpha_error Q"
 unfolding ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent_def
 by (rule order_trans[OF wp_ro_absorb_checked_staged_security_builder_head_event_le
   fs_compiled_alpha_bound[OF false_statement fixed bound nonempty]])

definition fs_refined_common_error where
  "fs_refined_common_error Q =
    hash_collision_budget_value 0 (fs_direct_hash_budget Q) +
    ro_absorb_checked_staged_first_root_prefix_merkle_target_error (fs_replay_budgets Q) +
    ro_absorb_checked_staged_local_composition_prefix_target_error (fs_replay_budgets Q) +
    ro_absorb_checked_staged_fri_builder_merkle_target_error (fs_replay_budgets Q) +
    fs_mca_error Q +
    fs_mca_error Q +
    ro_checked_staged_local_query_phase_target_error (fs_replay_budgets Q) +
    fs_alpha_error Q"

definition fs_refined_nonempty_error where
  "fs_refined_nonempty_error rT rC Q = fs_refined_common_error Q +
    nnreal (fs_direct_hash_budget Q)/nnreal size +
    fs_accounted_sampling_error rT rC Q"

lemma fs_compiled_refined_nonempty_bound:
 assumes false_statement: "\<not>exists_valid_trace"
   and fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and nonempty: "0<ceil_log clength" and positive: "0<rounds"
   and eval_power: "clength*scale=2^N"
   and trace_rounds_fit: "Suc(ceil_log clength)\<le>N"
   and composition_rounds_fit: "Suc(ceil_log(Suc maxDegree))\<le>N"
   and trace_rate: "4*fri_padded_degree_bound (clength-1)\<le>clength*scale"
   and composition_rate: "4*fri_padded_degree_bound maxDegree\<le>clength*scale"
 shows "wp_event
   (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses (fs_compile_replay A P))
     accepted adversary_initial_state \<le> fs_refined_nonempty_error rT rC Q"
proof -
  have wf: "staged_budget_wellformed (fs_replay_budgets Q)"
    by (rule fs_replay_budgets_wellformed)
  have controlled: "staged_adversary_controlled (fs_replay_budgets Q) (fs_compile_replay A P)"
    by (rule fs_compile_replay_controlled[OF bound fixed])
 let ?M="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses (fs_compile_replay A P)"
 let ?Collision="final_hash_collision_event"
 let ?TraceTarget="ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit"
 let ?CompositionTarget="ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit"
 let ?BuilderTarget="ro_absorb_checked_staged_security_clean_builder_merkle_target_hit"
 let ?TraceChallenge="ro_mca_security_bad True"
 let ?CompositionChallenge="ro_mca_security_bad False"
 let ?QueryPhaseTarget="ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit"
 let ?Alpha="ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent"
 let ?Initial="hash_new_output_hit_event {PState adversary_initial_state} adversary_initial_state"
 let ?Joint="jre_event N rT rC"
 let ?Es="[?Collision,?TraceTarget,?CompositionTarget,?BuilderTarget,?TraceChallenge,?CompositionChallenge,?QueryPhaseTarget,?Alpha,?Initial,?Joint]"
 have lenf: "ceil_log clength\<le>N" using trace_rounds_fit by simp
 have lenc: "ceil_log(maxDegree+1)\<le>N" using composition_rounds_fit by simp
 have classified: "wp_event ?M accepted adversary_initial_state\<le>
     wp_event ?M (jgc_union N rT rC) adversary_initial_state"
   unfolding wp_event_def
   by (rule wp_mono_on_support)
      (use jgc_classification[OF wf controlled nonempty eval_power trace_rounds_fit composition_rounds_fit]
       in auto)
 have same: "jgc_union N rT rC = (\<lambda>out. \<exists>E\<in>set ?Es. E out)"
   unfolding jgc_union_def by auto
 have union: "wp_event ?M (jgc_union N rT rC) adversary_initial_state\<le>
     sum_list(map (\<lambda>E. wp_event ?M E adversary_initial_state) ?Es)"
   unfolding same by (rule jcb_list_union_bound)
 have Collision: "wp_event ?M ?Collision adversary_initial_state\<le>hash_collision_budget_value 0 (fs_direct_hash_budget Q)"
   by (rule fs_compiled_final_collision[OF fixed bound])
 have TraceTarget: "wp_event ?M ?TraceTarget adversary_initial_state\<le>ro_absorb_checked_staged_first_root_prefix_merkle_target_error (fs_replay_budgets Q)"
   by (rule wp_ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_bound[OF nonempty wf controlled])
 have CompositionTarget: "wp_event ?M ?CompositionTarget adversary_initial_state\<le>ro_absorb_checked_staged_local_composition_prefix_target_error (fs_replay_budgets Q)"
   by (rule wp_ro_absorb_checked_staged_clean_composition_prefix_target_hit_local_bound[OF nonempty wf controlled])
 have BuilderTarget: "wp_event ?M ?BuilderTarget adversary_initial_state\<le>ro_absorb_checked_staged_fri_builder_merkle_target_error (fs_replay_budgets Q)"
   by (rule wp_ro_absorb_checked_staged_security_clean_builder_merkle_target_hit_bound[OF wf controlled])
 have TraceChallenge: "wp_event ?M ?TraceChallenge adversary_initial_state\<le>fs_mca_error Q"
   by (rule fs_compiled_trace_security_bad[OF fixed bound eval_power trace_rounds_fit trace_rate])
 have CompositionChallenge: "wp_event ?M ?CompositionChallenge adversary_initial_state\<le>fs_mca_error Q"
   by (rule fs_compiled_composition_security_bad[OF fixed bound eval_power composition_rounds_fit composition_rate])
 have QueryPhaseTarget: "wp_event ?M ?QueryPhaseTarget adversary_initial_state\<le>ro_checked_staged_local_query_phase_target_error (fs_replay_budgets Q)"
   unfolding ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit_def
   by (rule order_trans[OF wp_ro_absorb_checked_staged_security_builder_head_event_le
     wp_ro_checked_staged_query_phase_builder_merkle_target_hit_local_bound[OF nonempty wf controlled]])
 have Alpha: "wp_event ?M ?Alpha adversary_initial_state\<le>fs_alpha_error Q"
   by (rule fs_compiled_alpha_security[OF false_statement fixed bound nonempty])
 have Initial: "wp_event ?M ?Initial adversary_initial_state\<le>nnreal (fs_direct_hash_budget Q)/nnreal size"
   using fs_compiled_initial_target[OF fixed bound, where A=A and B="{PState adversary_initial_state}"]
    by (simp add: hash_target_budget_value_def)
 have Joint: "wp_event ?M ?Joint adversary_initial_state\<le>fs_accounted_sampling_error rT rC Q"
   unfolding fs_accounted_sampling_error_def
   by (rule fs_accounting_compiled_clean_residual[OF fixed bound nonempty positive eval_power lenf lenc])
 have closed: "sum_list(map (\<lambda>E. wp_event ?M E adversary_initial_state) ?Es)\<le>
     fs_refined_nonempty_error rT rC Q"
   unfolding fs_refined_nonempty_error_def fs_refined_common_error_def
   apply (simp only: list.map sum_list.Cons sum_list.Nil add.assoc add.right_neutral)
   by (intro add_mono Collision TraceTarget CompositionTarget BuilderTarget TraceChallenge CompositionChallenge QueryPhaseTarget Alpha Initial Joint)
 show ?thesis by (rule order_trans[OF classified order_trans[OF union closed]])
qed


lemma fs_refined_nonempty_soundness:
  assumes bound: "fs_query_bound Q P" and false_statement: "\<not>exists_valid_trace"
    and nonempty: "0<ceil_log clength" and positive: "0<rounds"
    and eval_power: "clength*scale=2^N"
    and trace_rounds_fit: "Suc(ceil_log clength)\<le>N"
    and composition_rounds_fit: "Suc(ceil_log(Suc maxDegree))\<le>N"
    and trace_rate: "4*fri_padded_degree_bound (clength-1)\<le>clength*scale"
    and composition_rate: "4*fri_padded_degree_bound maxDegree\<le>clength*scale"
  shows "fs_acceptance_probability P \<le> fs_refined_nonempty_error rT rC Q"
proof (rule fs_compiled_staged_bound_suffices[OF bound, where A=A])
  fix T :: "('f,'f list) fs_program"
  assume fixed: "fs_fixed T" and capped: "fs_query_bound Q T"
  have witnessed: "wp_event
    (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      (fs_compile_replay A T))
    accepted adversary_initial_state \<le> fs_refined_nonempty_error rT rC Q"
    by (rule fs_compiled_refined_nonempty_bound[OF false_statement fixed capped
      nonempty positive eval_power trace_rounds_fit composition_rounds_fit trace_rate composition_rate])
  show "wp_event (ro_absorb_checked_staged_security_experiment (fs_compile_replay A T))
    accepted adversary_initial_state \<le> fs_refined_nonempty_error rT rC Q"
    using witnessed wp_ro_absorb_checked_staged_security_with_first_root_acceptance_eq
      [OF nonempty, of "fs_compile_replay A T"]
    unfolding accepted_def by simp
qed

definition fs_refined_parameter_error where
  "fs_refined_parameter_error N rT rC Q =
    (if ro_mca_weighted_parameter_regime N then
      min (fs_accounted_parameter_error N rT rC Q)
        (fs_refined_nonempty_error rT rC Q)
    else fs_accounted_parameter_error N rT rC Q)"

lemma fs_refined_parameter_error_le_accounted:
  "fs_refined_parameter_error N rT rC Q \<le>
    fs_accounted_parameter_error N rT rC Q"
  unfolding fs_refined_parameter_error_def by simp

lemma fs_refined_parameter_error_outside_regime:
  "\<not>ro_mca_weighted_parameter_regime N \<Longrightarrow>
    fs_refined_parameter_error N rT rC Q =
      fs_accounted_parameter_error N rT rC Q"
  unfolding fs_refined_parameter_error_def by simp

theorem fs_refined_soundness:
  assumes bound: "fs_query_bound Q P" and false_statement: "\<not>exists_valid_trace"
  shows "fs_acceptance_probability P \<le> fs_refined_parameter_error N rT rC Q"
proof -
  have current: "fs_acceptance_probability P \<le>
    fs_accounted_parameter_error N rT rC Q"
    by (rule fs_accounted_soundness[OF bound false_statement])
  show ?thesis
  proof (cases "ro_mca_weighted_parameter_regime N")
    case True
    then have conditions: "0<ceil_log clength" "0<rounds" "clength*scale=2^N"
      "Suc(ceil_log clength)\<le>N" "Suc(ceil_log(Suc maxDegree))\<le>N"
      "4*fri_padded_degree_bound (clength-1)\<le>clength*scale"
      "4*fri_padded_degree_bound maxDegree\<le>clength*scale"
      unfolding ro_mca_weighted_parameter_regime_def ro_mca_parameter_regime_def by blast+
    have refined: "fs_acceptance_probability P \<le> fs_refined_nonempty_error rT rC Q"
      by (rule fs_refined_nonempty_soundness[OF bound false_statement conditions])
    show ?thesis using current refined True unfolding fs_refined_parameter_error_def by simp
  next
    case False
    show ?thesis using current False unfolding fs_refined_parameter_error_def by simp
  qed
qed

lemma fs_square_builder_budgets:
 assumes schema: "spec=square_workload_spec clength a z"
   and geometry: "clength=1024" "scale=64" "powers=2"
   and reps: "rounds=640"
 shows "fs_builder_fresh_budget Q=Q+342450"
   "ro_checked_staged_transcript_hash_query_budget_for (fs_replay_budgets Q)=664*Q+342450"
 using square_fs_replay_experiment_envelopes(1)[OF schema geometry, where Q=0]
   square_fs_replay_experiment_envelopes(1)[OF schema geometry, where Q=Q]
   reps unfolding fs_builder_fresh_budget_def by simp_all

lemma fs_mca_error_le_staged:
 "fs_mca_error Q \<le> ro_mca_challenge_error (fs_replay_budgets Q)"
proof -
 have bq: "fs_builder_fresh_budget Q \<le>
   ro_checked_staged_transcript_hash_query_budget_for (fs_replay_budgets Q)"
   by (rule fs_builder_fresh_budget_le_replay)
 show ?thesis unfolding fs_mca_error_def ro_mca_challenge_error_def Let_def
   apply (rule nnreal_nat_divide_right_mono)
   apply (rule mult_le_mono[OF bq])
   using bq by linarith
qed

lemma fs_alpha_error_le_staged:
 "fs_alpha_error Q \<le> ro_checked_staged_first_root_robust_alpha_pivot_error (fs_replay_budgets Q)"
proof -
 let ?b = "fs_builder_fresh_budget Q"
 let ?q = "ro_checked_staged_transcript_hash_query_budget_for (fs_replay_budgets Q)"
 have bq: "?b\<le>?q" by (rule fs_builder_fresh_budget_le_replay)
 have relation: "nnreal(?b*(1+(2*?b+2)))/nnreal size \<le>
   nnreal(?q*(1+(6*?q+2)))/nnreal size"
   apply (rule nnreal_nat_divide_right_mono)
   apply (rule mult_le_mono[OF bq])
   using bq by linarith
 show ?thesis unfolding fs_alpha_error_def
   ro_checked_staged_first_root_robust_alpha_pivot_error_def Let_def
   by (intro add_mono hash_collision_budget_value_mono_right[OF bq]
     nnreal_nat_divide_right_mono[OF bq] order_refl relation)
qed

lemma fs_refined_nonempty_error_le_accounted:
 "fs_refined_nonempty_error rT rC Q \<le> fs_accounted_nonempty_error rT rC Q"
 unfolding fs_refined_nonempty_error_def fs_refined_common_error_def
   fs_accounted_nonempty_error_def fs_accounted_common_error_def
 by (intro add_mono order_refl fs_mca_error_le_staged fs_alpha_error_le_staged)

end

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then () else error "Unexpected refined FS soundness dependency")
    @{thms soundness.fs_refined_soundness
      soundness.fs_refined_parameter_error_le_accounted
      soundness.fs_refined_nonempty_error_le_accounted
      soundness.fs_square_builder_budgets};
\<close>
end
