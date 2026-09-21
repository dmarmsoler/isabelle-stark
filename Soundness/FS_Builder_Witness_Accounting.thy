
theory FS_Builder_Witness_Accounting
 imports FS_Builder_Accounting
   Soundness_FRI_First_Root_RO_Adaptive_Query_Budget
   Soundness_FRI_First_Root_RO_Prequery_Bridge
begin

section \<open>Builder-final observations through exact witness erasure\<close>

text \<open>These projections preserve builder data and state. They do not erase
  or identify saved-prefix events. The domain bound is required only on clean
  supported outcomes, matching the existing MCA branch.\<close>

context soundness
begin

lemma fs_builder_witness_projection:
 "(ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A
   \<bind> (\<lambda>(_,data,query_start,raws,query_states). return data)) =
  ro_checked_staged_transcript_program A"
proof -
 have first:
  "(ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A
   \<bind> (\<lambda>(_,data,query_start,raws,query_states).
     return (data,query_start,raws,query_states))) =
    ro_checked_staged_transcript_program_with_query_witnesses A"
   by (rule ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_projection_all_rounds)
 have queries:
  "(ro_checked_staged_transcript_program_with_query_witnesses A
    \<bind> (\<lambda>(data,query_start,raws,query_states). return data)) =
    ro_checked_staged_transcript_program A"
   by (rule ro_checked_staged_transcript_program_with_query_witnesses_projection)
 show ?thesis using queries[folded first]
   by (simp add: sm_bind_assoc split_def)
qed

lemma fs_builder_witness_adaptive:
 assumes "fs_fixed P" "fs_query_bound Q P"
 shows "adaptive_hash_query_budget (fs_builder_fresh_budget Q)
   (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
     (fs_compile_replay A P))"
 by (rule adaptive_hash_query_budget_of_projection[OF
   fs_builder_witness_projection[unfolded split_def] fs_compiled_builder_adaptive[OF assms]])

lemma fs_builder_witness_domain:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and outcome: "Some (((prefix,prefix_state),data,query_start,raws,query_states),t)
     \<in>set_dist(execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
       (fs_compile_replay A P)) adversary_initial_state)"
   and clean: "\<not>hash_map_output_collision t"
 shows "card(fmdom'(HashMap t))\<le>fs_builder_fresh_budget Q"
proof -
 have original: "Some(data,t)\<in>set_dist(execute
   (ro_checked_staged_transcript_program(fs_compile_replay A P)) adversary_initial_state)"
   by (rule ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[OF outcome])
 have range: "card(hash_map_output_values t) \<le>
   card(hash_map_output_values adversary_initial_state)+fs_builder_fresh_budget Q"
   using fs_compiled_builder_range[OF fixed bound] original
   unfolding hash_range_budget_def by blast
 have "hash_map_output_values adversary_initial_state = {}"
   unfolding adversary_initial_state_def hash_map_output_values_def by simp
 then show ?thesis using range
   card_fmdom_le_hash_map_output_values_if_no_collision[OF clean] by simp
qed

lemma fs_builder_witness_relation:
 assumes "fs_fixed P" "fs_query_bound Q P"
   and steps: "\<And>M x. fmlookup M x=None \<Longrightarrow>
     card {y. hash_state_relation_transition R M (fmupd x y M)} \<le> b"
 shows "wp_event
   (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
     (fs_compile_replay A P))
   (hash_state_relation_transition_event R (HashMap adversary_initial_state))
   adversary_initial_state \<le> nnreal(fs_builder_fresh_budget Q*b)/nnreal size"
 using fs_builder_witness_adaptive[OF assms(1,2)] steps
 unfolding adaptive_hash_query_budget_def hash_state_relation_budget_def
   hash_relation_budget_value_def by blast

lemma fs_builder_witness_event:
 "wp_event (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
   (\<lambda>out. case out of None \<Rightarrow> False
    | Some ((prefix,data,query_start,raws,query_states),t) \<Rightarrow> E data t) s =
  wp_event (ro_checked_staged_transcript_program A)
   (\<lambda>out. case out of None \<Rightarrow> False | Some(data,t) \<Rightarrow> E data t) s"
proof -
 have "wp_event (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A
     \<bind> (\<lambda>(_,data,query_start,raws,query_states). return data))
    (\<lambda>out. case out of None \<Rightarrow> False | Some(data,t) \<Rightarrow> E data t) s =
   wp_event (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
    (\<lambda>out. case out of None \<Rightarrow> False
      | Some ((prefix,data,query_start,raws,query_states),t) \<Rightarrow> E data t) s"
   unfolding split_def wp_event_bind_return_map
   by (rule arg_cong[where f="\<lambda>E. wp_event
     (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A) E s"],
     rule ext) (auto split: option.splits prod.splits)
 then show ?thesis using fs_builder_witness_projection[of A] by simp
qed


lemma fs_builder_witness_state_event:
 "wp_event (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
   (\<lambda>out. case out of None \<Rightarrow> False | Some(_,t) \<Rightarrow> E t) s =
  wp_event (ro_checked_staged_transcript_program A)
   (\<lambda>out. case out of None \<Rightarrow> False | Some(_,t) \<Rightarrow> E t) s"
proof -
 have eq: "(\<lambda>out. case out of None \<Rightarrow> False
   | Some ((prefix,data,query_start,raws,query_states),t) \<Rightarrow> E t) =
   (\<lambda>out. case out of None \<Rightarrow> False | Some(_,t) \<Rightarrow> E t)"
   by (rule ext) (auto split: option.splits prod.splits)
 show ?thesis using fs_builder_witness_event[where A=A and E="\<lambda>_. E" and s=s]
   unfolding eq .
qed

lemma fs_builder_witness_collision:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
 shows "wp_event
   (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
     (fs_compile_replay A P)) final_hash_collision_event adversary_initial_state \<le>
   hash_collision_budget_value 0 (fs_builder_fresh_budget Q)"
proof -
 have budget:
  "wp_event (ro_checked_staged_transcript_program(fs_compile_replay A P))
    (hash_new_collision_event adversary_initial_state) adversary_initial_state \<le>
   hash_collision_budget_value (card(hash_map_output_values adversary_initial_state))
     (fs_builder_fresh_budget Q)"
   using fs_compiled_builder_collision[OF fixed bound, where A=A,
     unfolded hash_collision_budget_def, rule_format, of adversary_initial_state]
     adversary_initial_state_no_output_collision by blast
 have eq: "hash_new_collision_event adversary_initial_state = final_hash_collision_event"
   by (rule ext) (auto simp: hash_new_collision_event_def
     final_hash_collision_event_def hash_map_new_output_collision_def
     split: option.splits prod.splits)
 have projected:
  "wp_event (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
     (fs_compile_replay A P)) final_hash_collision_event adversary_initial_state =
   wp_event (ro_checked_staged_transcript_program(fs_compile_replay A P))
     final_hash_collision_event adversary_initial_state"
   unfolding final_hash_collision_event_def[abs_def]
   by (rule fs_builder_witness_state_event)
 show ?thesis using budget projected by (simp add: eq)
qed

lemma fs_builder_witness_target:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
 shows "wp_event
   (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
     (fs_compile_replay A P))
   (hash_new_output_hit_event B adversary_initial_state) adversary_initial_state \<le>
   hash_target_budget_value B (fs_builder_fresh_budget Q)"
proof -
 have budget:
  "wp_event (ro_checked_staged_transcript_program(fs_compile_replay A P))
   (hash_new_output_hit_event B adversary_initial_state) adversary_initial_state \<le>
   hash_target_budget_value B (fs_builder_fresh_budget Q)"
   using fs_compiled_builder_target[OF fixed bound]
   unfolding hash_target_program_def hash_target_budget_def by blast
 have projected:
  "wp_event (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
     (fs_compile_replay A P))
     (hash_new_output_hit_event B adversary_initial_state) adversary_initial_state =
   wp_event (ro_checked_staged_transcript_program(fs_compile_replay A P))
     (hash_new_output_hit_event B adversary_initial_state) adversary_initial_state"
   unfolding hash_new_output_hit_event_def[abs_def]
   by (rule fs_builder_witness_state_event)
 show ?thesis using budget projected by simp
qed

end

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then () else error "Unexpected builder witness dependency")
    @{thms soundness.fs_builder_witness_projection soundness.fs_builder_witness_domain
      soundness.fs_builder_witness_relation soundness.fs_builder_witness_collision
      soundness.fs_builder_witness_target};
\<close>
end
