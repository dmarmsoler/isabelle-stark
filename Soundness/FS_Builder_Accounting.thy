theory FS_Builder_Accounting
 imports FS_Replay_Allowance
   Staged_Security_Experiment_RO_Transcript_Adaptive_State_Relation
   Staged_Security_Experiment_RO_Transcript_Collision_Budgets
begin

section \<open>Replay-aware checked-builder accounting\<close>

text \<open>The equality is at the builder boundary, before verifier replay.
  It preserves the complete builder result and state for arbitrary fixed adaptive
  producers. Private randomness remains handled by the existing normalization.
  These probability budgets do not reduce the compiler's operational callback
  allowances. Saved-prefix observations require their own witness argument.\<close>

context soundness
begin

lemma fs_fixed_selectors_zero:
 "staged_adversary_controlled (fs_replay_budgets 0)
   (fs_fixed_transcript_staged_adversary A source)"
 unfolding staged_adversary_controlled_def fs_replay_budgets_def
 by (auto intro: fs_fixed_transcript_callbacks_controlled)

lemma fs_replay_builder_first:
 "ro_checked_staged_transcript_program (fs_replay_staged P family) =
   (fs_run P \<bind> (\<lambda>x. ro_checked_staged_transcript_program
     ((fs_replay_staged P family)\<lparr>trace_root_stage:=trace_root_stage(family x)\<rparr>)))"
proof -
 have root: "trace_root_stage(fs_replay_staged P family) =
   (fs_run P \<bind> (\<lambda>x. trace_root_stage(family x)))"
   by (simp add: fs_replay_staged_def)
 show ?thesis
   by (simp add: ro_checked_staged_transcript_program_def root sm_bind_assoc
     fs_trace_loop_root_update fs_composition_loop_root_update fs_queries_root_update)
qed

lemma fs_replay_builder_elimination:
 assumes fixed: "fs_fixed P" and ext: "\<And>x. fs_callbacks_extend(family x)"
 shows "wp(ro_checked_staged_transcript_program(fs_replay_staged P family)) F s =
   wp(fs_run P \<bind> (\<lambda>x. ro_checked_staged_transcript_program(family x))) F s"
proof -
 have point: "wp(ro_checked_staged_transcript_program
     ((fs_replay_staged P family)\<lparr>trace_root_stage:=trace_root_stage(family x)\<rparr>)) F t =
   wp(ro_checked_staged_transcript_program(family x)) F t"
   if out: "Some(x,t)\<in>set_dist(execute(fs_run P)s)" for x t
   by (rule fs_above_eqD[OF _ hash_ext_refl],
       rule fs_builder_above_eq[OF _ ext])
     (rule fs_callbacks_above_eq_root[OF fs_replay_staged_above_eq[OF fixed out]])
 show ?thesis
   apply (subst fs_replay_builder_first)
   apply (simp only: wp_bind)
   apply (rule fs_wp_cong_on_support)
   using point by (auto split: option.splits prod.splits)
qed

lemma fs_compiled_builder_elimination:
 assumes "fs_fixed P"
 shows "ro_checked_staged_transcript_program(fs_compile_replay A P) =
   (fs_run P \<bind> (\<lambda>source. ro_checked_staged_transcript_program
     (fs_fixed_transcript_staged_adversary A source)))"
 unfolding fs_compile_replay_def
 by (rule fs_wp_ext, rule fs_replay_builder_elimination[OF assms])
   (rule fs_fixed_callbacks_extend)

definition fs_builder_fresh_budget where
 "fs_builder_fresh_budget Q =
   Q+ro_checked_staged_transcript_hash_query_budget_for (fs_replay_budgets 0)"

lemma fs_compiled_builder_adaptive:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
 shows "adaptive_hash_query_budget (fs_builder_fresh_budget Q)
   (ro_checked_staged_transcript_program(fs_compile_replay A P))"
 unfolding fs_compiled_builder_elimination[OF fixed] fs_builder_fresh_budget_def
 by (rule adaptive_hash_query_budget_bind)
   (rule controlled_ro_program_adaptive_hash_query_budget[OF fs_run_controlled[OF bound]],
    rule adaptive_hash_query_budget_ro_checked_staged_transcript_program
      [OF fs_replay_budgets_wellformed fs_fixed_selectors_zero])

lemma fs_compiled_builder_range:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
 shows "hash_range_budget (fs_builder_fresh_budget Q)
   (ro_checked_staged_transcript_program(fs_compile_replay A P))"
 unfolding fs_compiled_builder_elimination[OF fixed] fs_builder_fresh_budget_def
 by (rule hash_range_budget_bind)
   (rule controlled_ro_program_range[OF fs_run_controlled[OF bound]],
    rule hash_range_budget_ro_checked_staged_transcript_program
      [OF fs_replay_budgets_wellformed fs_fixed_selectors_zero])

lemma fs_compiled_builder_collision:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
 shows "hash_collision_budget (fs_builder_fresh_budget Q)
   (ro_checked_staged_transcript_program(fs_compile_replay A P))"
 unfolding fs_compiled_builder_elimination[OF fixed] fs_builder_fresh_budget_def
 by (rule hash_collision_budget_bind)
   (rule controlled_ro_program_range[OF fs_run_controlled[OF bound]],
    rule controlled_ro_program_collision[OF fs_run_controlled[OF bound]],
    rule hash_range_budget_ro_checked_staged_transcript_program
      [OF fs_replay_budgets_wellformed fs_fixed_selectors_zero],
    rule hash_collision_budget_ro_checked_staged_transcript_program
      [OF fs_replay_budgets_wellformed fs_fixed_selectors_zero])

lemma fs_compiled_builder_target:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
 shows "hash_target_program B (fs_builder_fresh_budget Q)
   (ro_checked_staged_transcript_program(fs_compile_replay A P))"
 unfolding fs_compiled_builder_elimination[OF fixed] fs_builder_fresh_budget_def
 by (rule hash_target_program_bind)
   (rule controlled_ro_program_target[OF fs_run_controlled[OF bound]],
    rule hash_target_program_ro_checked_staged_transcript_program
      [OF fs_replay_budgets_wellformed fs_fixed_selectors_zero])

lemma fs_builder_fresh_budget_le_replay:
 "fs_builder_fresh_budget Q \<le>
   ro_checked_staged_transcript_hash_query_budget_for (fs_replay_budgets Q)"
 unfolding fs_builder_fresh_budget_def ro_checked_staged_transcript_hash_query_budget_for_def
   fs_replay_budgets_def
 by (simp add: sum_list_replicate; arith)

end

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then () else error "Unexpected builder accounting dependency")
    @{thms soundness.fs_compiled_builder_elimination
      soundness.fs_compiled_builder_adaptive soundness.fs_compiled_builder_range
      soundness.fs_compiled_builder_collision soundness.fs_compiled_builder_target};
\<close>
end
