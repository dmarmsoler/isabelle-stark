(* Title: Stark/Soundness_FRI_Weighted_Residual_Union.thy
   License: BSD-3-Clause *)

theory Soundness_FRI_Weighted_Residual_Union
  imports
    "Soundness_FRI_Weighted_FRI_Endpoint"
begin

section \<open>Residual Union for weighted MCA soundness\<close>

text \<open>Combine semantic and FRI live scores before charging the bad-connection count. This yields one connection charge for the union of all three guarded residual branches.\<close>

subsection \<open>Joint Residual Probability\<close>

context soundness
begin

definition jrp_event where
 "jrp_event N rT rC n j out \<longleftrightarrow> lpu_event rT rC n j out \<or> cau_event N rT rC n j out"

definition ro_mca_weighted_residual_power_sum where
 "ro_mca_weighted_residual_power_sum rT rC n = (ro_mca_weighted_semantic_base rT rC)^n + cap_cost rT rC n"

lemma jrp_semantic_score:
 assumes hist: "fc_history fmempty es (HashMap t)" and good: "fc_no_bad {} es"
   and event: "lpu_event rT rC n j (Some(x,t))"
 shows "1\<le>lpp_total rT rC n j es (HashMap t)"
proof -
 have selected: "lpp_selected_event rT rC n j (Some((x,es),t))"
   by (rule lpu_history_selected[OF hist good event])
 obtain e f where member: "e\<in>set es" and birth: "as_birth rT rC j e=Some f"
   and acc: "lpp_family_accept n f (HashMap t)"
   using selected unfolding lpp_selected_event_def by auto
 show ?thesis by (rule lpp_member_score[OF member birth acc])
qed

lemma jrp_logged_bound:
 assumes logged: "lp_rule q m L" and empty: "HashMap s=fmempty"
 shows "wp_event m (jrp_event N rT rC n j) s\<le>nnreal q*ro_mca_weighted_residual_power_sum rT rC n+
   fc_charge ({}::'f set) q 0"
proof -
 let ?E="jrp_event N rT rC n j"
 let ?I="\<lambda>out. case out of None \<Rightarrow> (0::prob) | Some((x,es),t) \<Rightarrow> if ?E(Some(x,t)) then 1 else 0"
 let ?S="\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow>
   lpp_live_total rT rC n j (HashMap s) es (HashMap t)"
 let ?F="\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow>
   cap_live_total N rT rC n j (HashMap s) es (HashMap t)"
 let ?B="\<lambda>out. case out of None \<Rightarrow> 0 | Some((x,es),t) \<Rightarrow> fc_bad_count ({}::'f set) es"
 have trace: "lg_trace q m L" using logged by (simp add: lp_rule_def)
 have erase: "wp_event m ?E s=wp L ?I s"
   unfolding wp_event_def using lg_wp_erase[OF trace, where P="\<lambda>out. if ?E out then 1 else 0" and s=s]
   by (simp only: jrp_event_def lpu_event_def cau_event_def option.simps if_False simp_thms)
 have point: "?I out\<le>(?S out+?F out)+?B out"
   if mem: "out\<in>set_dist (execute L s)" for out
 proof (cases out)
   case None then show ?thesis by simp
 next
   case (Some a)
   obtain x es t where out: "out=Some((x,es),t)" using Some by (cases a) auto
   show ?thesis
   proof (cases "?E(Some(x,t))")
     case False then show ?thesis by (simp add: out)
   next
     case hit: True
     have hist: "fc_history fmempty es (HashMap t)"
       using trace mem empty unfolding lg_trace_def
       apply (simp only: out)
       by fastforce
     have bound: "1\<le>(?S out+?F out)+?B out"
     proof (cases "fc_no_bad {} es")
       case good: True
       have clean: "\<not>hash_map_output_collision (channel_for_hash_map (HashMap t))"
         using hit by (auto simp: jrp_event_def lpu_event_def cau_event_def)
       have alive: "lpl_alive (HashMap s) es (HashMap t)"
         by (simp add: lpl_alive_def empty hist good clean)
       have score: "1\<le>lpp_total rT rC n j es (HashMap t)+cap_total N rT rC n j es (HashMap t)"
       proof (cases "lpu_event rT rC n j (Some(x,t))")
         case True
         show ?thesis by (rule order_trans[OF jrp_semantic_score[OF hist good True]]) simp
       next
         case False
         have fri: "cau_event N rT rC n j (Some(x,t))"
           using hit False unfolding jrp_event_def by blast
         show ?thesis by (rule order_trans[OF cau_history_score[OF hist good fri]]) simp
       qed
       have "1\<le>(lpp_total rT rC n j es (HashMap t)+cap_total N rT rC n j es (HashMap t))+
         fc_bad_count ({}::'f set) es"
         by (rule order_trans[OF score]) simp
       then show ?thesis by (simp add: out lpp_live_total_def cap_live_total_def alive)
     next
       case False
       have bad: "1\<le>fc_bad_count ({}::'f set) es" by (rule fc_bad_count_detects[OF False])
       have dead: "\<not>lpl_alive (HashMap s) es (HashMap t)" using False by (simp add: lpl_alive_def)
       show ?thesis using bad by (simp add: out lpp_live_total_def cap_live_total_def dead)
     qed
     show ?thesis using bound hit by (simp add: out)
   qed
 qed
 have cap: "card(fmdom' (HashMap s))\<le>0" by (simp add: empty)
 have "wp_event m ?E s\<le>wp L (\<lambda>out. (?S out+?F out)+?B out) s"
   unfolding erase by (rule wp_mono_on_support) (rule point)
 also have "...=(wp L ?S s+wp L ?F s)+wp L ?B s"
   by (simp only: causal_wp_add)
 also have "...\<le>(nnreal q*(ro_mca_weighted_semantic_base rT rC)^n+nnreal q*cap_cost rT rC n)+fc_charge ({}::'f set) q 0"
   by (intro add_mono lpp_logged_total[OF logged] cap_logged_total[OF logged]
     ll_logged_bad_count[OF logged cap])
 finally show ?thesis by (simp add: ro_mca_weighted_residual_power_sum_def algebra_simps)
qed

lemma jrp_program_bound:
 assumes program: "lc_program q m" and empty: "HashMap s=fmempty"
 shows "wp_event m (jrp_event N rT rC n j) s\<le>nnreal q*ro_mca_weighted_residual_power_sum rT rC n+
   fc_charge ({}::'f set) q 0"
 using program unfolding lc_program_def by (blast intro: jrp_logged_bound[OF _ empty])

lemma jrp_saved_experiment_bound:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
 shows "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
     (jrp_event N rT rC n j) adversary_initial_state\<le>
   nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*ro_mca_weighted_residual_power_sum rT rC n+
   fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
 by (rule jrp_program_bound[OF
   lc_program_ro_absorb_checked_staged_security_experiment_with_data_state[OF wf controlled]])
   (simp add: adversary_initial_state_def)

end

subsection \<open>Joint Residual Endpoint\<close>

context soundness
begin

definition jre_event where
 "jre_event N rT rC out \<longleftrightarrow> vr_clean_semantic_event rT rC out \<or> cre_event N rT rC out"

lemma jre_path_map:
 fixes m :: "('a, 'f protocol_channel) state_monad"
 shows "wp_event (m \<bind> (\<lambda>x. return (f x))) (jrp_event N rT rC n j) s=
   wp_event m (jrp_event N rT rC n j) s"
proof -
 have pair: "jrp_event N rT rC n j (Some (f x,t))=jrp_event N rT rC n j (Some (x,t))" for x and t :: "'f protocol_channel"
   by (simp only: jrp_event_def lpu_event_def cau_event_def option.simps prod.case)
 have none: "\<not>jrp_event N rT rC n j None"
   unfolding jrp_event_def lpu_event_def cau_event_def
   by simp
 show ?thesis unfolding wp_event_def wp_bind_return_map
   apply (rule arg_cong[where f="\<lambda>P. wp m P s"], rule ext)
   subgoal for out
     by (cases out) (auto simp only: option.simps prod.case pair none split: prod.splits)
   done
qed

lemma jre_witness_path_probability:
 "wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
    (jrp_event N rT rC n j) s=
  wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
    (jrp_event N rT rC n j) s"
proof -
 have a: "wp_event (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
    (jrp_event N rT rC n j) s=
  wp_event (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
    (jrp_event N rT rC n j) s"
   using jre_path_map[where m="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A"
     and f="\<lambda>(((prefix_with_state,data,query_start,raws,query_states),attacker_state),result).
       (((data,query_start,raws,query_states),attacker_state),result)"
     and N=N and rT=rT and rC=rC and n=n and j=j and s=s]
   by (simp only: split_def ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_projection_all_rounds[unfolded split_def])
 have b: "wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
    (jrp_event N rT rC n j) s=
  wp_event (ro_absorb_checked_staged_security_experiment_with_query_witnesses A)
    (jrp_event N rT rC n j) s"
   using jre_path_map[where m="ro_absorb_checked_staged_security_experiment_with_query_witnesses A"
     and f="\<lambda>(((data,query_start,raws,query_states),attacker_state),result).
       ((data,attacker_state),result)"
     and N=N and rT=rT and rC=rC and n=n and j=j and s=s]
   by (simp only: split_def ro_absorb_checked_staged_security_experiment_with_query_witnesses_projection[unfolded split_def])
 show ?thesis using a b by simp
qed


lemma jre_on_support:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength" and positive: "0<rounds"
   and power: "clength*scale=2^N"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log(maxDegree+1)\<le>N"
   and supported: "out\<in>set_dist (execute
     (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
       adversary_initial_state)"
   and event: "jre_event N rT rC out"
 shows "jrp_event N rT rC rounds 0 out"
 using event
   lpr_clean_semantic_on_support[OF wf controlled nonempty positive power lenf lenc supported]
   cob_on_support[OF wf controlled nonempty positive power lenf lenc supported]
 unfolding jre_event_def jrp_event_def by blast

lemma jre_original_bound:
 assumes wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and nonempty: "0<ceil_log clength" and positive: "0<rounds"
   and lenf: "ceil_log clength\<le>N" and lenc: "ceil_log(maxDegree+1)\<le>N"
   and power: "clength*scale=2^N"
 shows "wp_event
   (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A)
   (jre_event N rT rC) adversary_initial_state \<le>
     nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*
       ro_mca_weighted_residual_power_sum rT rC rounds+
     fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
proof -
 let ?run="ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses A"
 have "wp_event ?run (jre_event N rT rC) adversary_initial_state\<le>
     wp_event ?run (jrp_event N rT rC rounds 0) adversary_initial_state"
   unfolding wp_event_def
   by (rule wp_mono_on_support)
      (use jre_on_support[OF wf controlled nonempty positive power lenf lenc] in auto)
 also have "...=wp_event (ro_absorb_checked_staged_security_experiment_with_data_state A)
     (jrp_event N rT rC rounds 0) adversary_initial_state"
   by (rule jre_witness_path_probability)
 also have "... \<le>nnreal (ro_absorb_checked_staged_security_hash_query_budget_for budgets)*
       ro_mca_weighted_residual_power_sum rT rC rounds+
     fc_charge ({}::'f set) (ro_absorb_checked_staged_security_hash_query_budget_for budgets) 0"
   by (rule jrp_saved_experiment_bound[OF wf controlled])
 finally show ?thesis .
qed

end

end
