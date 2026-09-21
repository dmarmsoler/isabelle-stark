
theory FS_Alpha_Accounting
 imports FS_Challenge_Accounting
begin

section \<open>Replay-aware decoded-alpha accounting with the prefix exception retained\<close>

text \<open>The collision, initial-target and alpha-relation branches use the
  single-run builder budget. The saved-first-root Merkle-target branch retains
  the existing staged charge. No final-map equality is used to move that event
  to a different prefix.\<close>

context soundness
begin

definition fs_alpha_side_event where
 "fs_alpha_side_event Q out \<longleftrightarrow>
   final_hash_collision_event out \<or>
   hash_new_output_hit_event {PState adversary_initial_state} adversary_initial_state out \<or>
   ro_checked_staged_first_root_prefix_merkle_target_hit out \<or>
   hash_state_relation_transition_event
     (conditioned_fri_relation_bounded (fs_builder_fresh_budget Q)
       robust_alpha_pivot_absorbed_query_relation)
     (HashMap adversary_initial_state) out"

definition fs_alpha_error where
 "fs_alpha_error Q =
   hash_collision_budget_value 0 (fs_builder_fresh_budget Q) +
   nnreal(fs_builder_fresh_budget Q)/nnreal size +
   ro_checked_staged_first_root_prefix_merkle_target_error (fs_replay_budgets Q) +
   nnreal(fs_builder_fresh_budget Q*(1+(2*fs_builder_fresh_budget Q+2)))/nnreal size"

lemma fs_alpha_side_recap:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and support: "out\<in>set_dist(execute
     (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
       (fs_compile_replay A P)) adversary_initial_state)"
   and old: "ro_checked_staged_first_root_robust_alpha_pivot_side_event (fs_replay_budgets Q) out"
 shows "fs_alpha_side_event Q out"
proof (cases out)
 case None
 then show ?thesis using old
   unfolding ro_checked_staged_first_root_robust_alpha_pivot_side_event_def
     final_hash_collision_event_def hash_new_output_hit_event_def
     ro_checked_staged_first_root_prefix_merkle_target_hit_def
     hash_state_relation_transition_event_def by simp
next
 case (Some packed)
 obtain prefix prefix_state data query_start raws query_states t where packed:
   "packed=(((prefix,prefix_state),data,query_start,raws,query_states),t)"
   by (cases packed) (auto split: prod.splits)
 have outcome: "Some (((prefix,prefix_state),data,query_start,raws,query_states),t)
   \<in>set_dist(execute
     (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
       (fs_compile_replay A P)) adversary_initial_state)"
   using support unfolding Some packed .
 show ?thesis
 proof (cases "hash_map_output_collision t")
   case True
   then show ?thesis unfolding Some packed fs_alpha_side_event_def
     final_hash_collision_event_def by simp
 next
   case False
   have recap:
     "hash_state_relation_transition
       (conditioned_fri_relation_bounded (fs_builder_fresh_budget Q)
         robust_alpha_pivot_absorbed_query_relation)
       (HashMap adversary_initial_state) (HashMap t)"
     if rel: "hash_state_relation_transition
       (conditioned_fri_relation_bounded
         (ro_checked_staged_transcript_hash_query_budget_for (fs_replay_budgets Q))
         robust_alpha_pivot_absorbed_query_relation)
       (HashMap adversary_initial_state) (HashMap t)"
     by (rule fs_builder_bounded_recap[OF fixed bound outcome False rel])
   show ?thesis using old recap
     unfolding Some packed fs_alpha_side_event_def
       ro_checked_staged_first_root_robust_alpha_pivot_side_event_def
       robust_alpha_pivot_absorbed_query_relation_bounded_eq
       hash_state_relation_transition_event_def by auto
 qed
qed

lemma fs_compiled_alpha_bound:
 assumes false_statement: "\<not>exists_valid_trace"
   and fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and nonempty: "0<ceil_log clength"
 shows "wp_event
   (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
     (fs_compile_replay A P))
   ro_checked_staged_first_root_robust_decoded_all_queries_consistent
   adversary_initial_state \<le> fs_alpha_error Q"
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
   ro_checked_staged_first_root_prefix_merkle_target_error (fs_replay_budgets Q)"
   by (rule wp_ro_checked_staged_first_root_prefix_merkle_target_hit_bound[OF nonempty wf controlled])
 have relation: "wp_event ?M ?Relation adversary_initial_state \<le>
   nnreal(fs_builder_fresh_budget Q*(1+(2*fs_builder_fresh_budget Q+2)))/nnreal size"
   by (rule fs_compiled_alpha_relation[OF fixed bound])
 show ?thesis
   by (rule order_trans[OF event_le order_trans[OF union]],
     unfold fs_alpha_error_def,
     intro add_mono collision initial merkle relation)
qed

end

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then () else error "Unexpected alpha accounting dependency")
    @{thms soundness.fs_alpha_side_recap soundness.fs_compiled_alpha_bound};
\<close>
end
