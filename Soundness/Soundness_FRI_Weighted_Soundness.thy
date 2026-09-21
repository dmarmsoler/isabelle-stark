(* Title: Stark/Soundness_FRI_Weighted_Soundness.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Soundness
  imports
    "Soundness_FRI_Weighted_Residual_Union"
    "Soundness_FRI_Weighted_Challenge_Completion"
    "Stark.Soundness_FRI_Correlated_Agreement_Parameter_Bound"
begin

section \<open>Soundness for weighted MCA soundness\<close>

text \<open>Complete weighted MCA soundness for the unchanged adaptive random-oracle experiment. Every classification exception is charged, the three public premises are retained, and the minimum keeps older bounds and all ineligible-case fallbacks. No concrete security profile or unconditional strict improvement is asserted.\<close>

subsection \<open>Joint Guarded Classification\<close>

context soundness
begin

lemma jgc_extension:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength"
   and supported: "Some(((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)
     \<in>set_dist (execute (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
 shows "attacker_state\<le>u"
proof (rule ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_outcomeE[OF supported])
 assume builder: "Some (((prefix,prefix_state),data,query_start,raws,query_states),attacker_state)
     \<in>set_dist (execute (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and verifier: "Some(results,u)\<in>set_dist (execute ro_verify_monad
     (verifier_state_from_adversary attacker_state (staged_proof_transcript data)))"
 show ?thesis by (rule cee_builder_final_extension(1)[OF wf controlled nonempty builder verifier])
qed

lemma jgc_initial_extension:
 assumes ext: "attacker_state\<le>u"
   and hit: "ro_absorb_checked_staged_security_builder_initial_target_hit
     (Some(((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u))"
 shows "hash_new_output_hit_event {PState adversary_initial_state} adversary_initial_state
     (Some(((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u))"
proof -
 obtain k where lookup: "fmlookup (HashMap attacker_state) k=Some(PState adversary_initial_state)"
   using hit unfolding ro_absorb_checked_staged_security_builder_initial_target_hit_def
     ro_absorb_checked_staged_security_builder_head_event_def hash_new_output_hit_event_def
     hash_map_new_output_hit_def by auto
 have final: "fmlookup (HashMap u) k=Some(PState adversary_initial_state)"
   by (rule hash_extension_lookup[OF lookup ext])
 show ?thesis using final unfolding hash_new_output_hit_event_def hash_map_new_output_hit_def
   adversary_initial_state_def by auto
qed

lemma jgc_fri_guard_split:
 assumes ext: "attacker_state\<le>u"
   and hit: "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
     (fri_mca_combined_query_lists N rT rC)
     (Some(((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u))"
 shows "final_hash_collision_event
     (Some(((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)) \<or>
   hash_new_output_hit_event {PState adversary_initial_state} adversary_initial_state
     (Some(((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)) \<or>
   ro_absorb_checked_staged_security_clean_builder_merkle_target_hit
     (Some(((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)) \<or>
   ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit
     (Some(((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)) \<or>
   cre_event N rT rC
     (Some(((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u))"
proof -
 have collision: "hash_map_output_collision attacker_state \<Longrightarrow> hash_map_output_collision u"
   by (rule hash_map_output_collision_mono[OF _ ext])
 have targets: "fri_checked_builder_merkle_targets (ro_query_head_data data) query_start =
     fri_checked_builder_merkle_targets data query_start"
   by (simp add: ro_query_head_data_def fri_checked_builder_merkle_targets_def)
 show ?thesis using hit collision cita_initial_guard_exact[of _ u]
   unfolding cre_original_guarded_iff
     ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
     ro_absorb_checked_staged_security_clean_builder_merkle_target_hit_def
     ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit_def
     ro_absorb_checked_staged_security_builder_head_event_def
     ro_query_head_dependent_fri_builder_merkle_target_hit_def
     final_hash_collision_event_def
   by (force simp: targets)
qed

definition jgc_union where
 "jgc_union N rT rC out \<longleftrightarrow>
  final_hash_collision_event out \<or>
  jre_event N rT rC out \<or>
  ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit out \<or>
  ro_absorb_checked_staged_security_with_first_root_clean_composition_prefix_target_hit out \<or>
  ro_absorb_checked_staged_security_clean_builder_merkle_target_hit out \<or>
  hash_new_output_hit_event {PState adversary_initial_state} adversary_initial_state out \<or>
  ro_mca_security_bad True out \<or> ro_mca_security_bad False out \<or>
  ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit out \<or>
  ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent out"

lemma jgc_classification:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength" and ep: "clength*scale=2^N"
   and tf: "Suc (ceil_log clength)\<le>N" and cf: "Suc (ceil_log (Suc maxDegree))\<le>N"
   and acc: "accepted out"
   and support: "out\<in>set_dist (execute
     (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
 shows "jgc_union N rT rC out"
proof -
 obtain prefix prefix_state data query_start raws query_states attacker_state results u where
   out: "out=Some(((((prefix,prefix_state),data,query_start,raws,query_states),attacker_state),results),u)"
   using acc unfolding accepted_def by (cases out) (auto split: prod.splits)
 have ext: "attacker_state\<le>u"
   by (rule jgc_extension[OF wf controlled nonempty]) (use support out in simp)
 have old: "ro_mca_obstruction_union N rT rC out"
   by (rule ro_mca_acceptance_classification[OF wf controlled nonempty ep tf cf acc support])
 show ?thesis using old cita_semantic_guard_split[where rT=rT and rC=rC and out=out]
   jgc_initial_extension[OF ext, where prefix=prefix and prefix_state=prefix_state and data=data
     and query_start=query_start and raws=raws and query_states=query_states and results=results]
   jgc_fri_guard_split[OF ext, where prefix=prefix and prefix_state=prefix_state and data=data
     and query_start=query_start and raws=raws and query_states=query_states and results=results
     and N=N and rT=rT and rC=rC]
   unfolding ro_mca_obstruction_union_def jgc_union_def jre_event_def out by blast
qed

end

subsection \<open>Joint Complete Bound\<close>

context soundness
begin

lemma jcb_list_union_bound:
 "wp_event m (\<lambda>out. \<exists>E\<in>set Es. E out) s \<le>
   sum_list (map (\<lambda>E. wp_event m E s) Es)"
proof (induction Es)
 case Nil show ?case by simp
next
 case (Cons E Es)
 have "wp_event m (\<lambda>out. \<exists>F\<in>set (E#Es). F out) s =
   wp_event m (\<lambda>out. E out \<or> (\<exists>F\<in>set Es. F out)) s" by simp
 also have "...\<le>wp_event m E s+wp_event m (\<lambda>out. \<exists>F\<in>set Es. F out) s"
   by (rule wp_event_union_bound)
 also have "...\<le>wp_event m E s+sum_list (map (\<lambda>F. wp_event m F s) Es)"
   by (rule add_left_mono[OF Cons.IH])
 finally show ?case by simp
qed

definition ro_mca_weighted_sampling_error where
 "ro_mca_weighted_sampling_error rT rC budgets =
  nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*
    ro_mca_weighted_residual_power_sum rT rC rounds+
  fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"

definition ro_mca_weighted_common_error where
 "ro_mca_weighted_common_error budgets =
   hash_collision_budget_value 0 (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
   ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
   ro_absorb_checked_staged_local_composition_prefix_target_error budgets +
   ro_absorb_checked_staged_fri_builder_merkle_target_error budgets +
   ro_mca_challenge_error budgets +
   ro_mca_challenge_error budgets +
   ro_checked_staged_local_query_phase_target_error budgets +
   ro_checked_staged_first_root_robust_alpha_pivot_error budgets"

definition ro_mca_weighted_nonempty_parameter_error where
 "ro_mca_weighted_nonempty_parameter_error rT rC budgets = ro_mca_weighted_common_error budgets +
   nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)/nnreal size +
   ro_mca_weighted_sampling_error rT rC budgets"

lemma wp_ro_mca_weighted_nonempty_parameter_bound:
 assumes false_statement: "\<not>exists_valid_trace"
   and wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength" and positive: "0<rounds"
   and eval_power: "clength*scale=2^N"
   and trace_rounds_fit: "Suc(ceil_log clength)\<le>N"
   and composition_rounds_fit: "Suc(ceil_log(Suc maxDegree))\<le>N"
   and trace_rate: "4*fri_padded_degree_bound (clength-1)\<le>clength*scale"
   and composition_rate: "4*fri_padded_degree_bound maxDegree\<le>clength*scale"
 shows "wp_event
   (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
     accepted adversary_initial_state \<le> ro_mca_weighted_nonempty_parameter_error rT rC budgets"
proof -
 let ?M="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A"
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
 have Collision: "wp_event ?M ?Collision adversary_initial_state\<le>hash_collision_budget_value 0 (ro_absorb_checked_staged_security_hash_query_budget_for budgets)"
   by (rule wp_ro_absorb_checked_staged_security_with_first_root_final_hash_collision_bound[OF wf controlled nonempty])
 have TraceTarget: "wp_event ?M ?TraceTarget adversary_initial_state\<le>ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets"
   by (rule wp_ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_bound[OF nonempty wf controlled])
 have CompositionTarget: "wp_event ?M ?CompositionTarget adversary_initial_state\<le>ro_absorb_checked_staged_local_composition_prefix_target_error budgets"
   by (rule wp_ro_absorb_checked_staged_clean_composition_prefix_target_hit_local_bound[OF nonempty wf controlled])
 have BuilderTarget: "wp_event ?M ?BuilderTarget adversary_initial_state\<le>ro_absorb_checked_staged_fri_builder_merkle_target_error budgets"
   by (rule wp_ro_absorb_checked_staged_security_clean_builder_merkle_target_hit_bound[OF wf controlled])
 have TraceChallenge: "wp_event ?M ?TraceChallenge adversary_initial_state\<le>ro_mca_challenge_error budgets"
   by (rule wp_ro_mca_trace_security_bad[OF wf controlled eval_power trace_rounds_fit trace_rate])
 have CompositionChallenge: "wp_event ?M ?CompositionChallenge adversary_initial_state\<le>ro_mca_challenge_error budgets"
   by (rule wp_ro_mca_composition_security_bad[OF wf controlled eval_power composition_rounds_fit composition_rate])
 have QueryPhaseTarget: "wp_event ?M ?QueryPhaseTarget adversary_initial_state\<le>ro_checked_staged_local_query_phase_target_error budgets"
   unfolding ro_absorb_checked_staged_security_query_phase_builder_merkle_target_hit_def
   by (rule order_trans[OF wp_ro_absorb_checked_staged_security_builder_head_event_le
     wp_ro_checked_staged_query_phase_builder_merkle_target_hit_local_bound[OF nonempty wf controlled]])
 have Alpha: "wp_event ?M ?Alpha adversary_initial_state\<le>ro_checked_staged_first_root_robust_alpha_pivot_error budgets"
   by (rule wp_ro_absorb_checked_staged_security_robust_decoded_all_queries_consistent_bound[OF false_statement wf controlled nonempty])
 have Initial: "wp_event ?M ?Initial adversary_initial_state\<le>nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)/nnreal size"
   by (rule cita_final_initial_bound[OF wf controlled])
 have Joint: "wp_event ?M ?Joint adversary_initial_state\<le>ro_mca_weighted_sampling_error rT rC budgets"
   unfolding ro_mca_weighted_sampling_error_def
   by (rule jre_original_bound[OF wf controlled nonempty positive lenf lenc eval_power])
 have closed: "sum_list(map (\<lambda>E. wp_event ?M E adversary_initial_state) ?Es)\<le>
     ro_mca_weighted_nonempty_parameter_error rT rC budgets"
   unfolding ro_mca_weighted_nonempty_parameter_error_def ro_mca_weighted_common_error_def
   apply (simp only: list.map sum_list.Cons sum_list.Nil add.assoc add.right_neutral)
   by (intro add_mono Collision TraceTarget CompositionTarget BuilderTarget TraceChallenge CompositionChallenge QueryPhaseTarget Alpha Initial Joint)
 show ?thesis by (rule order_trans[OF classified order_trans[OF union closed]])
qed

lemma ro_absorb_stark_soundness_mca_weighted_nonempty:
 assumes false_statement: "\<not>exists_valid_trace"
   and wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength" and positive: "0<rounds"
   and eval_power: "clength*scale=2^N"
   and trace_rounds_fit: "Suc(ceil_log clength)\<le>N"
   and composition_rounds_fit: "Suc(ceil_log(Suc maxDegree))\<le>N"
   and trace_rate: "4*fri_padded_degree_bound (clength-1)\<le>clength*scale"
   and composition_rate: "4*fri_padded_degree_bound maxDegree\<le>clength*scale"
 shows "ro_absorb_checked_staged_adversary_acceptance_probability A\<le>ro_mca_weighted_nonempty_parameter_error rT rC budgets"
proof -
 have bound: "wp_event
   (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
     accepted adversary_initial_state \<le> ro_mca_weighted_nonempty_parameter_error rT rC budgets"
   by (rule wp_ro_mca_weighted_nonempty_parameter_bound[OF false_statement wf controlled nonempty positive eval_power
     trace_rounds_fit composition_rounds_fit trace_rate composition_rate])
 show ?thesis using bound wp_ro_absorb_checked_staged_security_with_first_root_acceptance_eq[OF nonempty, of A]
   unfolding ro_absorb_checked_staged_adversary_acceptance_probability_def accepted_def by simp
qed

end

subsection \<open>Joint All Rounds Endpoint\<close>

context soundness
begin

definition ro_mca_weighted_parameter_regime where
 "ro_mca_weighted_parameter_regime N \<longleftrightarrow> ro_mca_parameter_regime N \<and> 0<rounds"

definition ro_mca_weighted_parameter_error where
 "ro_mca_weighted_parameter_error N rT rC budgets =
   (if ro_mca_weighted_parameter_regime N
    then min (ro_mca_parameter_error N rT rC budgets) (ro_mca_weighted_nonempty_parameter_error rT rC budgets)
    else ro_mca_parameter_error N rT rC budgets)"

lemma ro_mca_weighted_parameter_error_le_mca:
 "ro_mca_weighted_parameter_error N rT rC budgets\<le>ro_mca_parameter_error N rT rC budgets"
 unfolding ro_mca_weighted_parameter_error_def by simp

lemma ro_mca_weighted_parameter_error_outside_regime:
 "\<not>ro_mca_weighted_parameter_regime N \<Longrightarrow> ro_mca_weighted_parameter_error N rT rC budgets=ro_mca_parameter_error N rT rC budgets"
 unfolding ro_mca_weighted_parameter_error_def by simp

lemma ro_mca_weighted_parameter_error_zero_repetitions:
 "rounds=0 \<Longrightarrow> ro_mca_weighted_parameter_error N rT rC budgets=ro_mca_parameter_error N rT rC budgets"
 unfolding ro_mca_weighted_parameter_error_def ro_mca_weighted_parameter_regime_def by simp

lemma ro_mca_weighted_parameter_error_zero_trace_depth:
 "ceil_log clength=0 \<Longrightarrow> ro_mca_weighted_parameter_error N rT rC budgets=
   ro_absorb_checked_staged_conditioned_explicit_zero_round_parameter_error budgets"
 unfolding ro_mca_weighted_parameter_error_def ro_mca_weighted_parameter_regime_def ro_mca_parameter_regime_def
 using ro_mca_parameter_error_zero_rounds by simp

lemma ro_mca_weighted_parameter_error_outside_mca:
 "\<not>ro_mca_parameter_regime N \<Longrightarrow> ro_mca_weighted_parameter_error N rT rC budgets=
   ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets"
 unfolding ro_mca_weighted_parameter_error_def ro_mca_weighted_parameter_regime_def
 using ro_mca_parameter_error_outside_regime by simp

theorem ro_absorb_stark_soundness_mca_weighted:
 assumes false_statement: "\<not>exists_valid_trace"
   and wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
 shows "ro_absorb_checked_staged_adversary_acceptance_probability A\<le>
   ro_mca_weighted_parameter_error N rT rC budgets"
proof -
 have current: "ro_absorb_checked_staged_adversary_acceptance_probability A\<le>
     ro_mca_parameter_error N rT rC budgets"
   by (rule ro_absorb_stark_soundness_mca[OF false_statement wf controlled])
 show ?thesis
 proof (cases "ro_mca_weighted_parameter_regime N")
   case True
   then have conditions: "0<ceil_log clength" "0<rounds" "clength*scale=2^N"
     "Suc(ceil_log clength)\<le>N" "Suc(ceil_log(Suc maxDegree))\<le>N"
     "4*fri_padded_degree_bound (clength-1)\<le>clength*scale"
     "4*fri_padded_degree_bound maxDegree\<le>clength*scale"
     unfolding ro_mca_weighted_parameter_regime_def ro_mca_parameter_regime_def by blast+
   have refined: "ro_absorb_checked_staged_adversary_acceptance_probability A\<le>
       ro_mca_weighted_nonempty_parameter_error rT rC budgets"
     by (rule ro_absorb_stark_soundness_mca_weighted_nonempty[OF false_statement wf controlled conditions])
   show ?thesis using current refined True unfolding ro_mca_weighted_parameter_error_def by simp
 next
   case False
   show ?thesis using current False unfolding ro_mca_weighted_parameter_error_def by simp
 qed
qed

lemma ro_mca_weighted_residual_power_sum_explicit:
 "ro_mca_weighted_residual_power_sum rT rC n =
  (nnreal (query_raw_preimage_card_envelope (mca_decoded_semantic_query_index_bound rT rC))/nnreal size)^n+
  (nnreal (query_raw_preimage_card_envelope (fri_mca_residual_branch_bound rT True))/nnreal size)^n+
  (nnreal (query_raw_preimage_card_envelope (fri_mca_residual_branch_bound rC False))/nnreal size)^n"
 by (simp add: ro_mca_weighted_residual_power_sum_def cap_cost_def ro_mca_weighted_fri_base_def add.assoc)

lemma ro_mca_weighted_connection_charge_real:
 "nn2real (fc_charge ({}::'f set) q 0)=5*real q*(real q-1)/(2*real size)"
 by (simp add: fc_charge_real)

lemma ro_mca_weighted_old_nonempty_decomposition:
 "ro_mca_nonempty_parameter_error rT rC budgets =
   ro_mca_weighted_common_error budgets+
   nnreal (ro_checked_staged_transcript_hash_query_budget_for budgets)/nnreal size+
   ro_mca_weighted_residual_power_sum rT rC (rounds-staged_attacker_query_budget budgets)"
 unfolding ro_mca_nonempty_parameter_error_def ro_mca_weighted_common_error_def
   ro_checked_staged_conditioned_initial_target_error_def
   ro_mca_combined_rectangle_error_def ro_mca_rectangle_error_def
   ro_mca_weighted_residual_power_sum_def cap_cost_def ro_mca_weighted_fri_base_def
 by (simp add: algebra_simps)

lemma ro_mca_weighted_complete_comparison:
 "(ro_mca_weighted_nonempty_parameter_error rT rC budgets\<le>ro_mca_nonempty_parameter_error rT rC budgets) \<longleftrightarrow>
  (nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)/nnreal size+
     ro_mca_weighted_sampling_error rT rC budgets \<le>
   nnreal (ro_checked_staged_transcript_hash_query_budget_for budgets)/nnreal size+
     ro_mca_weighted_residual_power_sum rT rC (rounds-staged_attacker_query_budget budgets))"
 by (simp add: ro_mca_weighted_nonempty_parameter_error_def ro_mca_weighted_old_nonempty_decomposition add.assoc)

lemma ro_mca_weighted_initial_charge_split:
 "nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)/nnreal size =
  nnreal (ro_checked_staged_transcript_hash_query_budget_for budgets)/nnreal size+
  nnreal ro_verifier_hash_query_budget/nnreal size"
 unfolding ro_absorb_checked_staged_security_hash_query_budget_for_def
 by (simp add: add_divide_nnreal)

lemma ro_mca_weighted_increment_comparison:
 "(ro_mca_weighted_nonempty_parameter_error rT rC budgets\<le>ro_mca_nonempty_parameter_error rT rC budgets) \<longleftrightarrow>
  (ro_mca_weighted_sampling_error rT rC budgets+
    nnreal ro_verifier_hash_query_budget/nnreal size \<le>
   ro_mca_weighted_residual_power_sum rT rC (rounds-staged_attacker_query_budget budgets))"
 apply (subst ro_mca_weighted_complete_comparison)
 apply (subst ro_mca_weighted_initial_charge_split)
 apply (simp only: add.assoc add_le_cancel_left)
 by (simp only: add.commute)

lemma ro_mca_weighted_parameter_error_inside_regime:
 "ro_mca_weighted_parameter_regime N \<Longrightarrow> ro_mca_weighted_parameter_error N rT rC budgets =
  min (min (ro_absorb_checked_staged_conditioned_explicit_parameter_error budgets)
      (ro_mca_nonempty_parameter_error rT rC budgets))
    (ro_mca_weighted_nonempty_parameter_error rT rC budgets)"
 unfolding ro_mca_weighted_parameter_error_def ro_mca_weighted_parameter_regime_def ro_mca_parameter_error_def by simp

end

end
