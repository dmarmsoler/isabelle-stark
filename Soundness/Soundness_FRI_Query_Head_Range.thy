theory Soundness_FRI_Query_Head_Range
  imports "Stark.Soundness_FRI_First_Root_RO_Prefix_Target_Bound"
begin

section \<open>Pre-query hash range and clean prefix targets\<close>
text \<open>
  This layer bounds the actual saved query-head state before query sampling or
  opening-stage work. The guarded cardinality conclusions use hash extension and
  an already charged clean later state; they do not assume unconditional
  collision freedom. Nonempty trace FRI is an auxiliary guard, not a new public
  soundness premise. The zero-round public fallback is unchanged.
\<close>

context soundness
begin

lemma hash_range_budget_ro_checked_staged_after_first_trace_fri_root_prefix:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (ro_checked_staged_after_first_root_hash_query_budget_for budgets)
      (ro_checked_staged_after_first_trace_fri_root_prefix_program A prefix)"
proof -
  obtain n where rounds_eq: "ceil_log clength = Suc n"
    using nonempty by (cases "ceil_log clength") auto
  let ?trace_fri =
    "sum_list
        (take (ceil_log clength - 1)
          (drop 1 (trace_fri_budgets budgets))) +
      2 * (ceil_log clength - 1)"
  let ?trace_final = "trace_final_budget budgets"
  let ?alpha = "2 * length spec"
  let ?degree = "degree_budget budgets"
  let ?composition_fri =
    "sum_list (composition_fri_budgets budgets) +
      2 * ceil_log (maxDegree + 1)"
  let ?composition_final = "composition_final_budget budgets"
  have trace_len:
    "1 + (ceil_log clength - 1) \<le> length (trace_fri_budgets budgets)"
    using nonempty wf
    unfolding staged_budget_wellformed_def
    by simp
  have trace_fri_program:
    "\<And>bs. hash_range_budget ?trace_fri
      (ro_staged_trace_fri_program A 1 (ceil_log clength - 1) bs)"
    by (rule hash_range_budget_ro_staged_trace_fri_program[
      OF controlled trace_len])
  have trace_fri_program_n:
    "\<And>bs. hash_range_budget
      (sum_list
          (take (Suc n - 1)
            (drop 1 (trace_fri_budgets budgets))) +
        2 * (Suc n - 1))
      (ro_staged_trace_fri_program A 1 n bs)"
    using trace_fri_program rounds_eq by simp
  have trace_final_program:
    "\<And>bs. hash_range_budget ?trace_final (trace_final_stage A bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have alpha_program:
    "hash_range_budget ?alpha
      (ro_staged_alpha_program (length spec))"
    by (rule hash_range_budget_ro_staged_alpha_program)
  have degree_program:
    "\<And>as. hash_range_budget ?degree (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  have composition_fri_program:
    "\<And>dg. hash_range_budget ?composition_fri
      (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)) \<bind>
        (\<lambda>_. ro_staged_composition_fri_program A dg 0
          (ceil_log (to_nat dg + 1)) []))"
    by (rule hash_range_budget_guarded_ro_staged_composition_fri_program[
      OF wf controlled])
  have composition_final_program:
    "\<And>dg bs. hash_range_budget ?composition_final
      (composition_final_stage A dg bs)"
    using controlled unfolding staged_adversary_controlled_def
    by (blast intro: controlled_ro_program_range)
  obtain fr trace_bs first_root where prefix_eq:
    "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  show ?thesis
    unfolding prefix_eq
      ro_checked_staged_after_first_trace_fri_root_prefix_program_def
      ro_checked_staged_after_first_root_hash_query_budget_for_def
      Let_def split_def rounds_eq
  apply (simp only: nat.case prod.sel)
  apply (rule hash_range_budget_bind)
   apply (rule hash_range_budget_receive_trace_fri_challenge)
  subgoal for b
    apply (rule hash_range_budget_bind)
     apply (rule trace_fri_program_n)
    subgoal for trace_pair
      apply (cases trace_pair)
      apply (rule hash_range_budget_bind)
       apply (rule trace_final_program)
      subgoal for trace_final
        apply (rule hash_range_budget_bind)
         apply (rule hash_range_budget_ro_record_staged_message)
        subgoal
          apply (rule hash_range_budget_bind)
           apply (rule alpha_program)
          subgoal for as
            apply (rule hash_range_budget_bind)
             apply (rule degree_program)
            subgoal for dg
              apply (rule hash_range_budget_bind)
               apply (rule hash_range_budget_ro_record_staged_message)
              subgoal
                apply (subst sm_bind_assoc[symmetric])
                apply (rule hash_range_budget_bind)
                 apply (rule composition_fri_program)
                subgoal for composition_pair
                  apply (cases composition_pair)
                  apply (rule hash_range_budget_bind)
                   apply (rule composition_final_program)
                  subgoal for composition_final
                    apply (rule hash_range_budget_bind)
                     apply (rule hash_range_budget_ro_record_staged_message)
                    apply (rule hash_range_budget_return)
                    done
                  done
                done
              done
            done
          done
        done
      done
    done
  done
qed



definition ro_checked_staged_query_head_hash_query_budget_for :: "staged_budgets \<Rightarrow> nat"
where
 "ro_checked_staged_query_head_hash_query_budget_for budgets =
    trace_root_budget budgets + sum_list (trace_fri_budgets budgets) +
    trace_final_budget budgets + degree_budget budgets +
    sum_list (composition_fri_budgets budgets) +
    composition_final_budget budgets +
    4 + 2 * ceil_log clength + 2 * length spec +
    2 * ceil_log (maxDegree + 1)"

lemma ro_checked_staged_query_head_budget_split:
 assumes nonempty: "0 < ceil_log clength"
   and wf: "staged_budget_wellformed budgets"
 shows "ro_checked_staged_query_head_hash_query_budget_for budgets =
   (staged_trace_fri_search_queries budgets 0 + 2) +
   ro_checked_staged_after_first_root_hash_query_budget_for budgets"
proof -
 obtain n where rounds_eq: "ceil_log clength = Suc n"
   using nonempty by (cases "ceil_log clength") auto
 obtain b bs where bs_eq: "trace_fri_budgets budgets = b # bs"
   using wf nonempty unfolding staged_budget_wellformed_def
   by (cases "trace_fri_budgets budgets") auto
 have len: "length bs = n"
   using wf unfolding staged_budget_wellformed_def rounds_eq bs_eq by simp
 show ?thesis
   unfolding ro_checked_staged_query_head_hash_query_budget_for_def staged_trace_fri_search_queries_def
     ro_checked_staged_after_first_root_hash_query_budget_for_def
   by (simp add: rounds_eq bs_eq len[symmetric] algebra_simps)
qed

lemma hash_range_budget_ro_checked_staged_first_root_query_head_program:
 assumes nonempty: "0 < ceil_log clength"
   and wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
 shows "hash_range_budget (ro_checked_staged_query_head_hash_query_budget_for budgets)
   (ro_checked_staged_first_root_query_head_program A)"
proof -
 have raw: "hash_range_budget
   ((staged_trace_fri_search_queries budgets 0 + 2) +
     (ro_checked_staged_after_first_root_hash_query_budget_for budgets + (0+0)))
   (ro_checked_staged_first_root_query_head_program A)"
   unfolding ro_checked_staged_first_root_query_head_program_def
   apply (rule hash_range_budget_bind)
    apply (rule hash_range_budget_ro_staged_first_trace_fri_root_prefix_program[OF nonempty wf controlled])
   apply (rule hash_range_budget_bind)
    apply (rule hash_range_budget_ro_checked_staged_after_first_trace_fri_root_prefix[OF nonempty wf controlled])
   apply (rule hash_range_budget_bind)
    apply (rule hash_range_budget_get)
   apply (rule hash_range_budget_return)
   done
 show ?thesis using raw ro_checked_staged_query_head_budget_split[OF nonempty wf] by simp
qed


lemma ro_checked_staged_query_head_plus_tail_budget:
 "ro_checked_staged_query_head_hash_query_budget_for budgets +
   (sum_list (query_opening_budgets budgets) + rounds +
     rounds * ro_checked_query_round_transcript_bound) =
   ro_checked_staged_transcript_hash_query_budget_for budgets"
 by (simp add: ro_checked_staged_query_head_hash_query_budget_for_def
   ro_checked_staged_transcript_hash_query_budget_for_def algebra_simps)

lemma ro_checked_staged_query_head_plus_opening_budget:
 "ro_checked_staged_query_head_hash_query_budget_for budgets + sum_list (query_opening_budgets budgets) =
   staged_attacker_query_budget budgets + 4 + 2 * ceil_log clength +
   2 * length spec + 2 * ceil_log (maxDegree + 1)"
 by (simp add: ro_checked_staged_query_head_hash_query_budget_for_def staged_attacker_query_budget_def algebra_simps)

lemma ro_checked_staged_query_start_output_budget:
 assumes nonempty: "0 < ceil_log clength"
   and wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and head: "Some ((prefix_with_state, data, query_start), t) \<in>
     set_dist (execute (ro_checked_staged_first_root_query_head_program A)
       adversary_initial_state)"
 shows "card (hash_map_output_values query_start) \<le> ro_checked_staged_query_head_hash_query_budget_for budgets"
proof -
 have eq: "t = query_start"
   by (rule ro_checked_staged_first_root_query_head_program_state[OF head])
 have raw: "card (hash_map_output_values query_start) \<le>
     card (hash_map_output_values adversary_initial_state) + ro_checked_staged_query_head_hash_query_budget_for budgets"
   using hash_range_budget_ro_checked_staged_first_root_query_head_program[OF nonempty wf controlled] head eq
   unfolding hash_range_budget_def by blast
 show ?thesis using raw by simp
qed

lemma ro_checked_staged_clean_query_start_domain_budget:
 assumes nonempty: "0 < ceil_log clength"
   and wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and head: "Some ((prefix_with_state, data, query_start), t) \<in>
     set_dist (execute (ro_checked_staged_first_root_query_head_program A)
       adversary_initial_state)"
   and ext: "query_start \<le> later"
   and clean: "\<not> hash_map_output_collision later"
 shows "card (fmdom' (HashMap query_start)) \<le> ro_checked_staged_query_head_hash_query_budget_for budgets"
proof -
 have prefix_clean: "\<not> hash_map_output_collision query_start"
   using clean ext hash_map_output_collision_mono by blast
 show ?thesis
   by (rule order_trans[
     OF card_fmdom_le_hash_map_output_values_if_no_collision[OF prefix_clean]
       ro_checked_staged_query_start_output_budget[OF nonempty wf controlled head]])
qed


lemma ro_checked_staged_clean_query_start_merkle_target_budget:
 assumes nonempty: "0 < ceil_log clength"
   and wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and head: "Some ((prefix_with_state, data, query_start), t) \<in>
     set_dist (execute (ro_checked_staged_first_root_query_head_program A)
       adversary_initial_state)"
   and ext: "query_start \<le> later"
   and clean: "\<not> hash_map_output_collision later"
   and finite_roots: "finite roots"
 shows "card (merkle_prefix_path_targets roots query_start) \<le>
   card roots + 2 * ro_checked_staged_query_head_hash_query_budget_for budgets"
proof -
 have domain: "card (fmdom' (HashMap query_start)) \<le> ro_checked_staged_query_head_hash_query_budget_for budgets"
   by (rule ro_checked_staged_clean_query_start_domain_budget[OF nonempty wf controlled head ext clean])
 have targets: "card (merkle_prefix_path_targets roots query_start) \<le>
   card roots + 2 * card (fmdom' (HashMap query_start))"
   by (rule card_merkle_prefix_path_targets_le[OF finite_roots])
 show ?thesis using domain targets by linarith
qed

lemma ro_checked_staged_clean_query_start_merkle_target_value:
 assumes nonempty: "0 < ceil_log clength"
   and wf: "staged_budget_wellformed budgets"
   and controlled: "staged_adversary_controlled budgets A"
   and head: "Some ((prefix_with_state, data, query_start), t) \<in>
     set_dist (execute (ro_checked_staged_first_root_query_head_program A)
       adversary_initial_state)"
   and ext: "query_start \<le> later"
   and clean: "\<not> hash_map_output_collision later"
   and finite_roots: "finite roots"
 shows "hash_target_budget_value (merkle_prefix_path_targets roots query_start) tail \<le>
   nnreal (tail * (card roots + 2 * ro_checked_staged_query_head_hash_query_budget_for budgets)) / nnreal size"
 unfolding hash_target_budget_value_def
 apply (rule nnreal_nat_divide_right_mono)
 using ro_checked_staged_clean_query_start_merkle_target_budget[OF nonempty wf controlled head ext clean finite_roots]
 by (rule mult_left_mono) simp

end

end
