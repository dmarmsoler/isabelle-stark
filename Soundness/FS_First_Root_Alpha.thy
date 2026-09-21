theory FS_First_Root_Alpha
 imports "Stark.FS_First_Root_Accounting" "Stark.FS_Alpha_Accounting"
   "Stark.Soundness_FRI_Robust_Security_Classification"
begin

section \<open>First-root refinement of the decoded-alpha exception\<close>

text \<open>Reuse the original side-event recap and union. Only its saved-first-root
  target estimate changes; collision, initial-target and relation terms remain.
  Builder-to-security transport keeps possible verifier failure explicit.\<close>

context soundness
begin

definition fs_first_root_alpha_error where
 "fs_first_root_alpha_error Q =
   hash_collision_budget_value 0 (fs_builder_fresh_budget Q) +
   nnreal(fs_builder_fresh_budget Q)/nnreal size +
   fs_first_root_builder_error Q +
   nnreal(fs_builder_fresh_budget Q*(1+(2*fs_builder_fresh_budget Q+2)))/nnreal size"

lemma fs_compiled_first_root_alpha_bound:
 assumes false_statement: "\<not>exists_valid_trace"
   and fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and nonempty: "0<ceil_log clength"
 shows "wp_event
   (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
     (fs_compile_replay A P))
   ro_checked_staged_first_root_robust_decoded_all_queries_consistent
   adversary_initial_state \<le> fs_first_root_alpha_error Q"
proof -
 have wf: "staged_budget_wellformed(fs_replay_budgets Q)"
   by (rule fs_replay_budgets_wellformed)
 have controlled: "staged_adversary_controlled(fs_replay_budgets Q) (fs_compile_replay A P)"
   by (rule fs_compile_replay_controlled[OF bound fixed])
 let ?M = "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses(fs_compile_replay A P)"
 let ?Collision = "final_hash_collision_event"
 let ?Initial = "hash_new_output_hit_event {PState adversary_initial_state} adversary_initial_state"
 let ?Merkle = "ro_checked_staged_first_root_prefix_merkle_target_hit"
 let ?Relation = "hash_state_relation_transition_event
   (conditioned_fri_relation_bounded (fs_builder_fresh_budget Q)
     robust_alpha_pivot_absorbed_query_relation) (HashMap adversary_initial_state)"
 have event_le: "wp_event ?M ro_checked_staged_first_root_robust_decoded_all_queries_consistent
     adversary_initial_state \<le> wp_event ?M (fs_alpha_side_event Q) adversary_initial_state"
   proof (rule wp_event_mono_on_support)
   fix out
   assume support: "out\<in>set_dist(execute ?M adversary_initial_state)"
     and all: "ro_checked_staged_first_root_robust_decoded_all_queries_consistent out"
   have side: "ro_checked_staged_first_root_robust_alpha_pivot_side_event (fs_replay_budgets Q) out"
     by (rule ro_checked_staged_first_root_robust_decoded_all_queries_consistent_imp_alpha_pivot_side_event
       [OF false_statement wf controlled nonempty support all])
   show "fs_alpha_side_event Q out" by (rule fs_alpha_side_recap[OF fixed bound support side])
 qed
 have union: "wp_event ?M (fs_alpha_side_event Q) adversary_initial_state \<le>
   wp_event ?M ?Collision adversary_initial_state +
   wp_event ?M ?Initial adversary_initial_state +
   wp_event ?M ?Merkle adversary_initial_state +
   wp_event ?M ?Relation adversary_initial_state"
   unfolding fs_alpha_side_event_def by (rule wp_event_union_bound4)
 have collision: "wp_event ?M ?Collision adversary_initial_state \<le>
   hash_collision_budget_value 0 (fs_builder_fresh_budget Q)"
   by (rule fs_builder_witness_collision[OF fixed bound])
 have initial: "wp_event ?M ?Initial adversary_initial_state \<le>
   nnreal(fs_builder_fresh_budget Q)/nnreal size"
   using fs_builder_witness_target[OF fixed bound, where A=A
     and B="{PState adversary_initial_state}"]
   by (simp add: hash_target_budget_value_def)
 have merkle: "wp_event ?M ?Merkle adversary_initial_state \<le>
   fs_first_root_builder_error Q"
   unfolding fs_first_root_builder_error_def
   by (rule fs_first_root_builder_bound[OF fixed bound nonempty])
 have relation: "wp_event ?M ?Relation adversary_initial_state \<le>
   nnreal(fs_builder_fresh_budget Q*(1+(2*fs_builder_fresh_budget Q+2)))/nnreal size"
   by (rule fs_compiled_alpha_relation[OF fixed bound])
 show ?thesis
   by (rule order_trans[OF event_le order_trans[OF union]],
     unfold fs_first_root_alpha_error_def,
     intro add_mono collision initial merkle relation)
qed
lemma fs_compiled_first_root_alpha_security:
 assumes false_statement: "\<not>exists_valid_trace"
   and fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and nonempty: "0<ceil_log clength"
 shows "wp_event
   (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses(fs_compile_replay A P))
   ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent
   adversary_initial_state \<le> fs_first_root_alpha_error Q"
 unfolding ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent_def
 by (rule order_trans[OF wp_ro_absorb_checked_staged_security_builder_head_event_le
   fs_compiled_first_root_alpha_bound[OF false_statement fixed bound nonempty]])

lemma fs_first_root_alpha_error_le_prefix:
 "fs_first_root_alpha_error Q \<le> fs_alpha_error Q"
 unfolding fs_first_root_alpha_error_def fs_alpha_error_def
 by (intro add_mono order_refl fs_first_root_builder_error_le_replay)

end
ML \<open>
 List.app (fn th => if null(Thm.hyps_of th) andalso null(Thm_Deps.all_oracles [th])
   then () else error "Unexpected first-root alpha dependency")
   @{thms soundness.fs_compiled_first_root_alpha_bound
     soundness.fs_compiled_first_root_alpha_security soundness.fs_first_root_alpha_error_le_prefix};
\<close>
end
