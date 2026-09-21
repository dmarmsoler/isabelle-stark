theory FS_Prefix_Witness_Replay
 imports "Stark.FS_Builder_Accounting"
   "Stark.Soundness_FRI_Query_Head_Range"
   "Stark.Soundness_FRI_RO_Actual_Query_Trace_Composition_Target_Bound"
begin

section \<open>Witness-preserving conventional-FS replay\<close>

text \<open>Exact replay equalities preserve the query-start state, first-root prefix,
  raw queries, opening chunks, failure and final state. They hold locally for
  fixed private choices while retaining adaptive oracle answers. The existing
  private-program mixture removes that local restriction at the public theorem.
  The head and tail quantities below are probability-accounting envelopes;
  the operational compiler and its callback allowances are unchanged.\<close>

context soundness
begin

lemma fs_prefix_get_extends:
 "hash_extension_preserving get"
 by (simp add: hash_extension_preserving_def hash_ext_refl)

lemma fs_prefix_query_witness_extend:
 assumes "\<And>i raw. hash_extension_preserving (query_opening_stage B i raw)"
 shows "hash_extension_preserving
   (ro_checked_staged_query_program_with_witnesses B rs crs qs i n)"
 by (induction n arbitrary: i qs)
   (auto simp: Let_def split_def intro!: hash_extension_preserving_bind
     intro: assms fs_assert_extends fs_records_extend fs_prefix_get_extends
       hash_extension_preserving_return fs_challenges_extend)

lemma fs_prefix_query_witness_above:
 assumes cb: "\<And>i raw. fs_above_eq t (query_opening_stage A i raw)
   (query_opening_stage B i raw)"
 and ext: "\<And>i raw. hash_extension_preserving (query_opening_stage B i raw)"
 shows "fs_above_eq t (ro_checked_staged_query_program_with_witnesses A rs crs qs i n)
   (ro_checked_staged_query_program_with_witnesses B rs crs qs i n)"
 by (induction n arbitrary: i qs)
   (auto simp: Let_def split_def intro!: fs_above_eq_bind
     intro: cb ext fs_above_eq_refl fs_records_extend fs_assert_extends
       fs_challenges_extend fs_prefix_get_extends fs_prefix_query_witness_extend
       hash_extension_preserving_return)

lemma fs_prefix_first_prefix_extend:
 assumes "fs_callbacks_extend B"
 shows "hash_extension_preserving (ro_staged_first_trace_fri_root_prefix_program B)"
 using assms unfolding fs_callbacks_extend_def ro_staged_first_trace_fri_root_prefix_program_def
 by (cases "ceil_log clength")
   (auto intro!: hash_extension_preserving_bind
     intro: fs_record_extends fs_prefix_get_extends hash_extension_preserving_return)

lemma fs_prefix_first_prefix_above:
 assumes "fs_callbacks_above_eq t A B" "fs_callbacks_extend B"
 shows "fs_above_eq t (ro_staged_first_trace_fri_root_prefix_program A)
   (ro_staged_first_trace_fri_root_prefix_program B)"
 using assms unfolding fs_callbacks_above_eq_def fs_callbacks_extend_def
   ro_staged_first_trace_fri_root_prefix_program_def
 by (cases "ceil_log clength")
   (auto intro!: fs_above_eq_bind
     intro: fs_above_eq_refl fs_record_extends fs_prefix_get_extends
       hash_extension_preserving_return)

lemma fs_prefix_after_prefix_extend:
 assumes "fs_callbacks_extend B"
 shows "hash_extension_preserving
   (ro_checked_staged_after_first_trace_fri_root_prefix_program B prefix)"
 using assms unfolding fs_callbacks_extend_def
   ro_checked_staged_after_first_trace_fri_root_prefix_program_def
 by (cases prefix; cases "ceil_log clength")
   (auto simp: Let_def split_def intro!: hash_extension_preserving_bind
     intro: fs_record_extends fs_alphas_extend fs_assert_extends
       fs_trace_loop_extend fs_composition_loop_extend
       fs_challenges_extend hash_extension_preserving_return)

lemma fs_prefix_after_prefix_above:
 assumes "fs_callbacks_above_eq t A B" "fs_callbacks_extend B"
 shows "fs_above_eq t
   (ro_checked_staged_after_first_trace_fri_root_prefix_program A prefix)
   (ro_checked_staged_after_first_trace_fri_root_prefix_program B prefix)"
 using assms unfolding fs_callbacks_above_eq_def fs_callbacks_extend_def
   ro_checked_staged_after_first_trace_fri_root_prefix_program_def
 by (cases prefix; cases "ceil_log clength")
   (auto simp: Let_def split_def intro!: fs_above_eq_bind
     intro: fs_above_eq_refl fs_record_extends fs_alphas_extend fs_assert_extends
       fs_trace_loop_above_eq fs_trace_loop_extend
       fs_composition_loop_above_eq fs_composition_loop_extend
       fs_challenges_extend hash_extension_preserving_return)

lemma fs_prefix_head_above:
 assumes "fs_callbacks_above_eq t A B" "fs_callbacks_extend B"
 shows "fs_above_eq t (ro_checked_staged_first_root_query_head_program A)
   (ro_checked_staged_first_root_query_head_program B)"
 unfolding ro_checked_staged_first_root_query_head_program_def
 by (auto intro!: fs_above_eq_bind
   intro: fs_prefix_first_prefix_above[OF assms] fs_prefix_first_prefix_extend[OF assms(2)]
     fs_prefix_after_prefix_above[OF assms] fs_prefix_after_prefix_extend[OF assms(2)]
     fs_above_eq_refl fs_prefix_get_extends hash_extension_preserving_return)

lemma fs_prefix_head_extend:
 assumes "fs_callbacks_extend B"
 shows "hash_extension_preserving (ro_checked_staged_first_root_query_head_program B)"
 unfolding ro_checked_staged_first_root_query_head_program_def
 by (auto intro!: hash_extension_preserving_bind
   intro: fs_prefix_first_prefix_extend[OF assms] fs_prefix_after_prefix_extend[OF assms]
     fs_prefix_get_extends hash_extension_preserving_return)

lemma fs_prefix_witness_builder_above:
 assumes "fs_callbacks_above_eq t A B" "fs_callbacks_extend B"
 shows "fs_above_eq t
   (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
   (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses B)"
 unfolding ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
 apply (rule fs_above_eq_bind[OF fs_prefix_head_above[OF assms] fs_prefix_head_extend[OF assms(2)]])
 using assms unfolding fs_callbacks_above_eq_def fs_callbacks_extend_def
 by (auto simp: split_def intro!: fs_above_eq_bind
   intro: fs_prefix_query_witness_above fs_prefix_query_witness_extend fs_above_eq_refl)

lemma fs_prefix_after_prefix_root_update:
 "ro_checked_staged_after_first_trace_fri_root_prefix_program
   (A\<lparr>trace_root_stage:=m\<rparr>) prefix =
  ro_checked_staged_after_first_trace_fri_root_prefix_program A prefix"
 unfolding ro_checked_staged_after_first_trace_fri_root_prefix_program_def
 apply (cases "ceil_log clength")
 by (simp_all add: split_def fs_trace_loop_root_update fs_composition_loop_root_update)

lemma fs_prefix_query_witness_root_update:
 "ro_checked_staged_query_program_with_witnesses (A\<lparr>trace_root_stage:=m\<rparr>) rs crs qs i n =
  ro_checked_staged_query_program_with_witnesses A rs crs qs i n"
 by (induction n arbitrary: i qs) (simp_all add: Let_def split_def)

lemma fs_prefix_head_replay_first:
 "ro_checked_staged_first_root_query_head_program(fs_replay_staged P family) =
  (fs_run P \<bind> (\<lambda>x. ro_checked_staged_first_root_query_head_program
    ((fs_replay_staged P family)\<lparr>trace_root_stage:=trace_root_stage(family x)\<rparr>)))"
proof -
 have root: "trace_root_stage(fs_replay_staged P family) =
   (fs_run P \<bind> (\<lambda>x. trace_root_stage(family x)))"
   by (simp add: fs_replay_staged_def)
 show ?thesis
   by (cases "ceil_log clength")
     (simp_all add: ro_checked_staged_first_root_query_head_program_def
       ro_staged_first_trace_fri_root_prefix_program_def root sm_bind_assoc
       fs_prefix_after_prefix_root_update)
qed

lemma fs_prefix_head_elimination:
 assumes fixed: "fs_fixed P"
 shows "ro_checked_staged_first_root_query_head_program(fs_compile_replay A P) =
   (fs_run P \<bind> (\<lambda>source. ro_checked_staged_first_root_query_head_program
     (fs_fixed_transcript_staged_adversary A source)))"
proof (unfold fs_compile_replay_def, rule fs_wp_ext)
 fix F s
 let ?family = "fs_fixed_transcript_staged_adversary A"
 have point: "wp(ro_checked_staged_first_root_query_head_program
     ((fs_replay_staged P ?family)\<lparr>trace_root_stage:=trace_root_stage(?family x)\<rparr>)) F t =
   wp(ro_checked_staged_first_root_query_head_program(?family x)) F t"
   if out: "Some(x,t)\<in>set_dist(execute(fs_run P)s)" for x t
   by (rule fs_above_eqD[OF _ hash_ext_refl],
       rule fs_prefix_head_above[OF _ fs_fixed_callbacks_extend])
     (rule fs_callbacks_above_eq_root[OF fs_replay_staged_above_eq[OF fixed out]])
 show "wp(ro_checked_staged_first_root_query_head_program(fs_replay_staged P ?family)) F s =
   wp(fs_run P \<bind> (\<lambda>source. ro_checked_staged_first_root_query_head_program(?family source))) F s"
   apply (subst fs_prefix_head_replay_first)
   apply (simp only: wp_bind)
   apply (rule fs_wp_cong_on_support)
   using point by (auto split: option.splits prod.splits)
qed

lemma fs_prefix_witness_builder_replay_first:
 "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses(fs_replay_staged P family) =
  (fs_run P \<bind> (\<lambda>x. ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
    ((fs_replay_staged P family)\<lparr>trace_root_stage:=trace_root_stage(family x)\<rparr>)))"
 by (simp add: ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
   fs_prefix_head_replay_first sm_bind_assoc fs_prefix_query_witness_root_update)

lemma fs_prefix_witness_builder_elimination:
 assumes fixed: "fs_fixed P"
 shows "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses(fs_compile_replay A P) =
   (fs_run P \<bind> (\<lambda>source. ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
     (fs_fixed_transcript_staged_adversary A source)))"
proof (unfold fs_compile_replay_def, rule fs_wp_ext)
 fix F s
 let ?family = "fs_fixed_transcript_staged_adversary A"
 have point: "wp(ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
     ((fs_replay_staged P ?family)\<lparr>trace_root_stage:=trace_root_stage(?family x)\<rparr>)) F t =
   wp(ro_checked_staged_transcript_program_with_first_root_and_query_witnesses(?family x)) F t"
   if out: "Some(x,t)\<in>set_dist(execute(fs_run P)s)" for x t
   by (rule fs_above_eqD[OF _ hash_ext_refl],
       rule fs_prefix_witness_builder_above[OF _ fs_fixed_callbacks_extend])
     (rule fs_callbacks_above_eq_root[OF fs_replay_staged_above_eq[OF fixed out]])
 show "wp(ro_checked_staged_transcript_program_with_first_root_and_query_witnesses(fs_replay_staged P ?family)) F s =
   wp(fs_run P \<bind> (\<lambda>source. ro_checked_staged_transcript_program_with_first_root_and_query_witnesses(?family source))) F s"
   apply (subst fs_prefix_witness_builder_replay_first)
   apply (simp only: wp_bind)
   apply (rule fs_wp_cong_on_support)
   using point by (auto split: option.splits prod.splits)
qed

lemma fs_prefix_security_witness_elimination:
 assumes "fs_fixed P"
 shows "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
   (fs_compile_replay A P) =
   (fs_run P \<bind> (\<lambda>source.
     ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
       (fs_fixed_transcript_staged_adversary A source)))"
 by (simp add: ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_def
   fs_prefix_witness_builder_elimination[OF assms] sm_bind_assoc)

definition fs_prefix_head_budget where
 "fs_prefix_head_budget Q = Q+ro_checked_staged_query_head_hash_query_budget_for (fs_replay_budgets 0)"

lemma fs_prefix_head_range:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and nonempty: "0<ceil_log clength"
 shows "hash_range_budget (fs_prefix_head_budget Q)
   (ro_checked_staged_first_root_query_head_program(fs_compile_replay A P))"
 unfolding fs_prefix_head_elimination[OF fixed] fs_prefix_head_budget_def
 by (rule hash_range_budget_bind)
   (rule controlled_ro_program_range[OF fs_run_controlled[OF bound]],
    rule hash_range_budget_ro_checked_staged_first_root_query_head_program
      [OF nonempty fs_replay_budgets_wellformed fs_fixed_selectors_zero])

lemma fs_prefix_head_domain:
 assumes fixed: "fs_fixed P" and bound: "fs_query_bound Q P"
   and nonempty: "0<ceil_log clength"
   and head: "Some ((prefix,data,qs),t)\<in>set_dist(execute
     (ro_checked_staged_first_root_query_head_program(fs_compile_replay A P))
     adversary_initial_state)"
   and ext: "qs\<le>later" and clean: "\<not>hash_map_output_collision later"
 shows "card(fmdom'(HashMap qs))\<le>fs_prefix_head_budget Q"
proof -
 have state: "t=qs"
   by (rule ro_checked_staged_first_root_query_head_program_state[OF head])
 have prefix_clean: "\<not>hash_map_output_collision qs"
   using clean ext hash_map_output_collision_mono by blast
 have range: "card(hash_map_output_values qs)\<le>fs_prefix_head_budget Q"
   using fs_prefix_head_range[OF fixed bound nonempty, where A=A,
     unfolded hash_range_budget_def, rule_format, OF head] state
   by simp
 show ?thesis
   by (rule order_trans[OF card_fmdom_le_hash_map_output_values_if_no_collision[OF prefix_clean] range])
qed

definition fs_prefix_tail_budget where
 "fs_prefix_tail_budget = rounds+rounds*ro_checked_query_round_transcript_bound"

lemma fs_prefix_fixed_query_target:
 assumes trace_len: "length rs=ceil_log clength"
   and composition_len: "length crs\<le>ceil_log(maxDegree+1)"
 shows "hash_target_program B fs_prefix_tail_budget
   (ro_checked_staged_query_program_with_witnesses
     (fs_fixed_transcript_staged_adversary A source) rs crs qs 0 rounds)"
 using hash_target_program_ro_checked_staged_query_program_with_witnesses_closed
   [OF fs_replay_budgets_wellformed fs_fixed_selectors_zero trace_len composition_len,
    where B=B and query_state=qs]
 by (simp add: fs_replay_budgets_def fs_prefix_tail_budget_def sum_list_replicate)

lemma fs_prefix_fixed_query_verifier_target:
 assumes trace_len: "length(staged_trace_fri_roots data)=ceil_log clength"
   and composition_len: "length(staged_composition_fri_roots data)\<le>ceil_log(maxDegree+1)"
 shows "hash_target_program B (fs_prefix_tail_budget+ro_verifier_hash_query_budget)
   (ro_checked_staged_query_program_with_witnesses
      (fs_fixed_transcript_staged_adversary A source)
      (staged_trace_fri_roots data) (staged_composition_fri_roots data) qs 0 rounds \<bind>
    (\<lambda>(raws,states,chunks). ro_checked_verifier_state_transfer_with_saved
      (staged_proof_transcript(data\<lparr>staged_query_chunks:=chunks\<rparr>)) \<bind>
     (\<lambda>saved. ro_verify_monad \<bind>
      (\<lambda>result. return (((prefix,data\<lparr>staged_query_chunks:=chunks\<rparr>,qs,raws,states),saved),result)))))"
 using hash_target_program_ro_absorb_checked_staged_query_and_verifier_tail
   [OF fs_replay_budgets_wellformed fs_fixed_selectors_zero trace_len composition_len,
    where B=B and query_start=qs and prefix_with_state=prefix]
 by (simp add: fs_replay_budgets_def fs_prefix_tail_budget_def sum_list_replicate)

definition fs_source_query_head where
 "fs_source_query_head A P =
  (fs_run P \<bind> (\<lambda>source.
    ro_checked_staged_first_root_query_head_program
      (fs_fixed_transcript_staged_adversary A source) \<bind>
    (\<lambda>head. return (source,head))))"

lemma fs_source_query_head_projection:
 assumes fixed: "fs_fixed P"
 and head: "Some ((source,x),t)\<in>set_dist(execute(fs_source_query_head A P)s)"
 shows "Some (x,t)\<in>set_dist(execute
   (ro_checked_staged_first_root_query_head_program(fs_compile_replay A P))s)"
 using head unfolding fs_source_query_head_def fs_prefix_head_elimination[OF fixed]
 by (auto elim!: set_dist_bindE intro: set_dist_bindI)

end
ML \<open>
  val fs_prefix_checkpoints = @{thms soundness.fs_prefix_head_elimination
    soundness.fs_prefix_witness_builder_elimination soundness.fs_prefix_security_witness_elimination
    soundness.fs_prefix_head_range soundness.fs_prefix_head_domain
    soundness.fs_prefix_fixed_query_target soundness.fs_prefix_fixed_query_verifier_target
    soundness.fs_source_query_head_projection};
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then writeln ("Witness replay: no hidden hypotheses/oracles; exported premises " ^
      string_of_int (Thm.nprems_of th))
    else error "Unexpected witness replay proof dependency") fs_prefix_checkpoints;
\<close>
end
