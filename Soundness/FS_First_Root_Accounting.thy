theory FS_First_Root_Accounting
 imports "Stark.FS_Prefix_Witness_Replay"
begin

section \<open>Single-producer accounting at the actual first-root boundary\<close>

text \<open>Retain the producer source and saved prefix in exact program equalities.
  The adaptive producer runs once; only its fixed-source selectors have zero
  allowance afterwards. Original events, failure and final states are retained.
  No protocol operation or operational replay allowance is changed.\<close>

context soundness
begin

lemma fs_first_root_replay:
 "ro_staged_first_trace_fri_root_prefix_program(fs_replay_staged P family) =
  (fs_run P \<bind> (\<lambda>x. ro_staged_first_trace_fri_root_prefix_program
    ((fs_replay_staged P family)\<lparr>trace_root_stage:=trace_root_stage(family x)\<rparr>)))"
 by (cases "ceil_log clength")
   (simp_all add: ro_staged_first_trace_fri_root_prefix_program_def
     fs_replay_staged_def sm_bind_assoc)

lemma fs_first_root_elimination:
 assumes fixed: "fs_fixed P"
 shows "ro_staged_first_trace_fri_root_prefix_program(fs_compile_replay A P) =
   (fs_run P \<bind> (\<lambda>source. ro_staged_first_trace_fri_root_prefix_program
     (fs_fixed_transcript_staged_adversary A source)))"
proof (unfold fs_compile_replay_def, rule fs_wp_ext)
 fix F s
 let ?family = "fs_fixed_transcript_staged_adversary A"
 have point: "wp(ro_staged_first_trace_fri_root_prefix_program
     ((fs_replay_staged P ?family)\<lparr>trace_root_stage:=trace_root_stage(?family x)\<rparr>)) F t =
   wp(ro_staged_first_trace_fri_root_prefix_program(?family x)) F t"
   if out: "Some(x,t)\<in>set_dist(execute(fs_run P)s)" for x t
   by (rule fs_above_eqD[OF _ hash_ext_refl],
       rule fs_prefix_first_prefix_above[OF _ fs_fixed_callbacks_extend])
     (rule fs_callbacks_above_eq_root[OF fs_replay_staged_above_eq[OF fixed out]])
 show "wp(ro_staged_first_trace_fri_root_prefix_program(fs_replay_staged P ?family)) F s =
   wp(fs_run P \<bind> (\<lambda>source. ro_staged_first_trace_fri_root_prefix_program(?family source))) F s"
   apply (subst fs_first_root_replay)
   apply (simp only: wp_bind)
   apply (rule fs_wp_cong_on_support)
   using point by (auto split: option.splits prod.splits)
qed


lemma fs_fixed_first_root_range:
 assumes nonempty: "0<ceil_log clength"
 shows "hash_range_budget 2 (ro_staged_first_trace_fri_root_prefix_program
   (fs_fixed_transcript_staged_adversary A source))"
 using hash_range_budget_ro_staged_first_trace_fri_root_prefix_program
   [OF nonempty fs_replay_budgets_wellformed
      fs_fixed_selectors_zero[where A=A and source=source]]
 by (simp add: staged_trace_fri_search_queries_def fs_replay_budgets_def sum_list_replicate numeral_2_eq_2)

lemma fs_first_root_range:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and nonempty: "0<ceil_log clength"
 shows "hash_range_budget (Q+2)
   (ro_staged_first_trace_fri_root_prefix_program(fs_compile_replay A P))"
 unfolding fs_first_root_elimination[OF fixed]
 by (rule hash_range_budget_bind)
   (rule controlled_ro_program_range[OF fs_run_controlled[OF bound]],
    rule fs_fixed_first_root_range[OF nonempty])

lemma fs_first_root_state:
 assumes "Some ((prefix,ps),t)\<in>set_dist(execute
   (ro_staged_first_trace_fri_root_prefix_program A)s)"
 shows "t=ps"
 using assms unfolding ro_staged_first_trace_fri_root_prefix_program_def
 by (auto elim!: set_dist_bindE split: nat.splits)

definition fs_source_first_root_head where
 "fs_source_first_root_head A P =
  (fs_run P \<bind> (\<lambda>source. ro_staged_first_trace_fri_root_prefix_program
    (fs_fixed_transcript_staged_adversary A source) \<bind>
     (\<lambda>head. return (source,head))))"

lemma fs_source_first_root_projection:
 assumes fixed: "fs_fixed P"
 and head: "Some ((source,x),t)\<in>set_dist(execute(fs_source_first_root_head A P)s)"
 shows "Some (x,t)\<in>set_dist(execute
   (ro_staged_first_trace_fri_root_prefix_program(fs_compile_replay A P))s)"
 using head unfolding fs_source_first_root_head_def fs_first_root_elimination[OF fixed]
 by (auto elim!: set_dist_bindE intro: set_dist_bindI)


lemma fs_first_root_card:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and nonempty: "0<ceil_log clength"
   and head: "Some ((prefix,ps),t)\<in>set_dist(execute
     (ro_staged_first_trace_fri_root_prefix_program(fs_compile_replay A P))
       adversary_initial_state)"
 shows "card(first_trace_fri_root_prefix_merkle_targets prefix ps)\<le>2+2*(Q+2)"
proof -
 have state: "t=ps" by (rule fs_first_root_state[OF head])
 have range: "card(hash_map_output_values ps)\<le>Q+2"
   using fs_first_root_range[OF fixed bound nonempty, where A=A,
     unfolded hash_range_budget_def, rule_format, OF head] state by simp
 obtain fr bs root where prefix: "prefix=(fr,bs,root)" by (cases prefix) auto
 show ?thesis
 proof (cases "hash_map_output_collision ps")
  case True
  then show ?thesis unfolding prefix first_trace_fri_root_prefix_merkle_targets_def by simp
 next
  case False
  have paths: "card(merkle_prefix_path_targets {fr,root} ps)\<le>
      card {fr,root}+2*card(hash_map_output_values ps)"
   by (rule card_merkle_prefix_path_targets_le_if_no_collision) (simp_all add: False)
  have roots: "card {fr,root}\<le>2" by (simp add: card_insert_if)
  have capped: "card(merkle_prefix_path_targets {fr,root} ps)\<le>2+2*(Q+2)"
   by (rule order_trans[OF paths add_mono[OF roots mult_left_mono[OF range]]]) simp
  show ?thesis using capped False
   unfolding prefix first_trace_fri_root_prefix_merkle_targets_def by simp
 qed
qed

definition fs_first_root_tail where
 "fs_first_root_tail =
   ro_checked_staged_after_first_root_with_query_hash_query_budget_for(fs_replay_budgets 0)"

lemma fs_fixed_first_root_tail:
 assumes nonempty: "0<ceil_log clength"
 shows "hash_target_program B fs_first_root_tail
   (ro_checked_staged_after_first_root_with_query_witnesses_program
     (fs_fixed_transcript_staged_adversary A source) prefix)"
 unfolding fs_first_root_tail_def
 by (rule hash_target_program_ro_checked_staged_after_first_root_with_query_witnesses
   [OF nonempty fs_replay_budgets_wellformed fs_fixed_selectors_zero])

lemma fs_fixed_first_root_security_tail:
 assumes nonempty: "0<ceil_log clength"
 shows "hash_target_program B (fs_first_root_tail+ro_verifier_hash_query_budget)
   (ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program
     (fs_fixed_transcript_staged_adversary A source) prefix)"
 unfolding fs_first_root_tail_def
 by (rule hash_target_program_ro_absorb_checked_staged_after_first_root_with_query_witnesses_security
   [OF nonempty fs_replay_budgets_wellformed fs_fixed_selectors_zero])

lemma fs_first_root_builder_decomposition:
 assumes fixed: "fs_fixed P"
 shows "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
   (fs_compile_replay A P) =
   (fs_source_first_root_head A P \<bind> (\<lambda>(source,prefix).
     ro_checked_staged_after_first_root_with_query_witnesses_program
       (fs_fixed_transcript_staged_adversary A source) prefix))"
 apply (subst fs_prefix_witness_builder_elimination[OF fixed])
 unfolding fs_source_first_root_head_def
   ro_checked_staged_transcript_program_with_first_root_prefix_decomposition
 by (simp add: sm_bind_assoc split_def)

lemma fs_first_root_security_decomposition:
 assumes fixed: "fs_fixed P"
 shows "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
   (fs_compile_replay A P) =
   (fs_source_first_root_head A P \<bind> (\<lambda>(source,prefix).
     ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program
       (fs_fixed_transcript_staged_adversary A source) prefix))"
 apply (subst fs_prefix_security_witness_elimination[OF fixed])
 unfolding fs_source_first_root_head_def
   ro_absorb_checked_staged_security_with_first_root_prefix_decomposition
 by (simp add: sm_bind_assoc split_def)


lemma fs_source_first_root_state:
 assumes fixed: "fs_fixed P"
 and head: "Some ((source,prefix,ps),t)\<in>set_dist(execute
   (fs_source_first_root_head A P)s)"
 shows "t=ps"
 by (rule fs_first_root_state[OF fs_source_first_root_projection[OF fixed head]])

lemma fs_source_first_root_value:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
 and nonempty: "0<ceil_log clength"
 and head: "Some ((source,prefix,ps),t)\<in>set_dist(execute
   (fs_source_first_root_head A P)adversary_initial_state)"
 shows "hash_target_budget_value (first_trace_fri_root_prefix_merkle_targets prefix ps) n
   \<le>nnreal(n*(2+2*(Q+2)))/nnreal size"
 unfolding hash_target_budget_value_def
 by (rule nnreal_nat_divide_right_mono,
     rule mult_left_mono[OF fs_first_root_card
       [OF fixed bound nonempty fs_source_first_root_projection[OF fixed head]]]) simp

lemma fs_first_root_builder_bound:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
 and nonempty: "0<ceil_log clength"
 shows "wp_event (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
   (fs_compile_replay A P)) ro_checked_staged_first_root_prefix_merkle_target_hit
   adversary_initial_state \<le> nnreal(fs_first_root_tail*(2+2*(Q+2)))/nnreal size"
proof -
 let ?M = "fs_source_first_root_head A P"
 let ?K = "\<lambda>(source,prefix). ro_checked_staged_after_first_root_with_query_witnesses_program
   (fs_fixed_transcript_staged_adversary A source) prefix"
 let ?E = "ro_checked_staged_first_root_prefix_merkle_target_hit"
 show ?thesis unfolding fs_first_root_builder_decomposition[OF fixed]
 proof (rule wp_event_bind_output_state_dependent_new_output_bound_by_target_budget
   [where B="\<lambda>(source,prefix,ps) t. first_trace_fri_root_prefix_merkle_targets prefix ps"
    and n=fs_first_root_tail])
  show "\<not>?E None" unfolding ro_checked_staged_first_root_prefix_merkle_target_hit_def by simp
 next
  fix x t out
  assume head: "Some(x,t)\<in>set_dist(execute ?M adversary_initial_state)"
    and out: "out\<in>set_dist(execute(?K x)t)" and event: "?E out"
  obtain source prefix ps where x: "x=(source,prefix,ps)" by (cases x) auto
  have state: "t=ps"
   by (rule fs_source_first_root_state[OF fixed]) (use head in \<open>simp add: x\<close>)
  show "hash_new_output_hit_event
      ((\<lambda>(source,prefix,ps) t. first_trace_fri_root_prefix_merkle_targets prefix ps) x t) t out"
   using event out state unfolding x ro_checked_staged_first_root_prefix_merkle_target_hit_def
     hash_new_output_hit_event_def ro_checked_staged_after_first_root_with_query_witnesses_program_def
   by (cases out) (auto elim!: set_dist_bindE split: prod.splits)
 next
  fix x t
  assume "Some(x,t)\<in>set_dist(execute ?M adversary_initial_state)"
  show "hash_target_budget
      ((\<lambda>(source,prefix,ps) t. first_trace_fri_root_prefix_merkle_targets prefix ps) x t)
      fs_first_root_tail (?K x)"
   by (cases x) (auto intro: hash_target_program_budget fs_fixed_first_root_tail[OF nonempty])
 next
  fix x t
  assume head: "Some(x,t)\<in>set_dist(execute ?M adversary_initial_state)"
  show "hash_target_budget_value
      ((\<lambda>(source,prefix,ps) t. first_trace_fri_root_prefix_merkle_targets prefix ps) x t)
      fs_first_root_tail \<le>nnreal(fs_first_root_tail*(2+2*(Q+2)))/nnreal size"
   using head fs_source_first_root_value[OF fixed bound nonempty]
    by (cases x) fastforce
 qed
qed


lemma fs_first_root_security_bound:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
 and nonempty: "0<ceil_log clength"
 shows "wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
   (fs_compile_replay A P)) ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
   adversary_initial_state \<le>
   nnreal((fs_first_root_tail+ro_verifier_hash_query_budget)*(2+2*(Q+2)))/nnreal size"
proof -
 let ?M = "fs_source_first_root_head A P"
 let ?K = "\<lambda>(source,prefix). ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program
   (fs_fixed_transcript_staged_adversary A source) prefix"
 let ?E = "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit"
 let ?n = "fs_first_root_tail+ro_verifier_hash_query_budget"
 show ?thesis unfolding fs_first_root_security_decomposition[OF fixed]
 proof (rule wp_event_bind_output_state_dependent_new_output_bound_by_target_budget
   [where B="\<lambda>(source,prefix,ps) t. first_trace_fri_root_prefix_merkle_targets prefix ps" and n="?n"])
  show "\<not>?E None"
   unfolding ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_def by simp
 next
  fix x t out
  assume head: "Some(x,t)\<in>set_dist(execute ?M adversary_initial_state)"
    and out: "out\<in>set_dist(execute(?K x)t)" and event: "?E out"
  obtain source prefix ps where x: "x=(source,prefix,ps)" by (cases x) auto
  have state: "t=ps"
   by (rule fs_source_first_root_state[OF fixed]) (use head in \<open>simp add: x\<close>)
  show "hash_new_output_hit_event
      ((\<lambda>(source,prefix,ps) t. first_trace_fri_root_prefix_merkle_targets prefix ps) x t) t out"
   using event out state unfolding x
     ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_def
     hash_new_output_hit_event_def
     ro_absorb_checked_staged_after_first_root_with_query_witnesses_security_program_def
     ro_checked_staged_after_first_root_with_query_witnesses_program_def
   by (cases out) (auto elim!: set_dist_bindE split: prod.splits)
 next
  fix x t
  assume "Some(x,t)\<in>set_dist(execute ?M adversary_initial_state)"
  show "hash_target_budget
      ((\<lambda>(source,prefix,ps) t. first_trace_fri_root_prefix_merkle_targets prefix ps) x t) ?n (?K x)"
   by (cases x)
     (auto intro: hash_target_program_budget fs_fixed_first_root_security_tail[OF nonempty])
 next
  fix x t
  assume head: "Some(x,t)\<in>set_dist(execute ?M adversary_initial_state)"
  show "hash_target_budget_value
      ((\<lambda>(source,prefix,ps) t. first_trace_fri_root_prefix_merkle_targets prefix ps) x t) ?n
      \<le>nnreal(?n*(2+2*(Q+2)))/nnreal size"
   using head fs_source_first_root_value[OF fixed bound nonempty]
    by (cases x) fastforce
 qed
qed

lemma fs_first_root_hit_extension:
 assumes ext: "attacker\<le>final"
 and hit: "hash_map_new_output_hit B prefix attacker"
 shows "hash_map_new_output_hit B prefix final"
 using hit ext unfolding hash_map_new_output_hit_def
 by (blast intro: hash_extension_lookup)

definition fs_first_root_builder_error where
 "fs_first_root_builder_error Q =
   nnreal(fs_first_root_tail*(2+2*(Q+2)))/nnreal size"

definition fs_first_root_security_error where
 "fs_first_root_security_error Q =
   nnreal((fs_first_root_tail+ro_verifier_hash_query_budget)*(2+2*(Q+2)))/nnreal size"

lemma fs_first_root_head_le_replay:
 "Q+2 \<le> staged_trace_fri_search_queries(fs_replay_budgets Q)0+2"
 unfolding staged_trace_fri_search_queries_def fs_replay_budgets_def
 by simp

lemma fs_first_root_tail_le_replay:
 "fs_first_root_tail \<le>
   ro_checked_staged_after_first_root_with_query_hash_query_budget_for(fs_replay_budgets Q)"
 unfolding fs_first_root_tail_def
   ro_checked_staged_after_first_root_with_query_hash_query_budget_for_def
   ro_checked_staged_after_first_root_hash_query_budget_for_def fs_replay_budgets_def
 by (simp add: sum_list_replicate; arith)

lemma fs_first_root_builder_error_le_replay:
 "fs_first_root_builder_error Q \<le>
   ro_checked_staged_first_root_prefix_merkle_target_error(fs_replay_budgets Q)"
 unfolding fs_first_root_builder_error_def ro_checked_staged_first_root_prefix_merkle_target_error_def
 apply (rule nnreal_nat_divide_right_mono, rule mult_le_mono[OF fs_first_root_tail_le_replay])
 using fs_first_root_head_le_replay[of Q] by simp

lemma fs_first_root_security_error_le_replay:
 "fs_first_root_security_error Q \<le>
   ro_absorb_checked_staged_first_root_prefix_merkle_target_error(fs_replay_budgets Q)"
 unfolding fs_first_root_security_error_def ro_absorb_checked_staged_first_root_prefix_merkle_target_error_def
 apply (rule nnreal_nat_divide_right_mono, rule mult_le_mono)
 using fs_first_root_tail_le_replay[of Q] fs_first_root_head_le_replay[of Q] by simp_all


end

ML \<open>
 List.app (fn th =>
   if null(Thm.hyps_of th) andalso null(Thm_Deps.all_oracles [th])
   then () else error "Unexpected first-root audit dependency")
   @{thms soundness.fs_first_root_elimination soundness.fs_first_root_range
     soundness.fs_first_root_card soundness.fs_fixed_first_root_tail
     soundness.fs_fixed_first_root_security_tail soundness.fs_first_root_builder_decomposition
     soundness.fs_first_root_security_decomposition soundness.fs_first_root_builder_bound
     soundness.fs_first_root_security_bound soundness.fs_first_root_hit_extension
      soundness.fs_first_root_builder_error_le_replay soundness.fs_first_root_security_error_le_replay};
\<close>
end
