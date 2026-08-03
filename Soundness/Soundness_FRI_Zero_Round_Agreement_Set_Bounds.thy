(*  Title:      Stark/Soundness_FRI_Zero_Round_Agreement_Set_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Zero_Round_Agreement_Set_Bounds
  imports Soundness_FRI_Zero_Round_Query_List_Bounds
begin

text \<open>
  Global agreement-set bound for the zero-round trace FRI target.

  The verifier-local event @{term trace_fri_zero_round_query_list_target_hit}
  is existential in a candidate table and final value.  The query-list target
  depends on these witnesses only through the agreement set inside
  @{term query_sample_space}.  This layer replaces the arbitrary-list
  existential by a finite union over agreement sets, preserving the exact
  query-list product accounting for each fixed set.
\<close>

context soundness
begin

definition fri_zero_round_first_query_index_lists_for_set
  :: "nat set \<Rightarrow> nat list set"
where
  "fri_zero_round_first_query_index_lists_for_set S =
    {query_idxs \<in> fri_query_index_list_space. query_idxs ! 0 \<in> S}"

definition fri_zero_round_small_agreement_sets :: "nat set set"
where
  "fri_zero_round_small_agreement_sets =
    {S. S \<subseteq> query_sample_space \<and> card S < query_sample_space_size}"

definition trace_fri_zero_round_agreement_set_target_error_for
where
  "trace_fri_zero_round_agreement_set_target_error_for budgets =
    (\<Sum>S \<in> fri_zero_round_small_agreement_sets.
      nnreal (card (fri_zero_round_first_query_index_lists_for_set S)) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (fri_zero_round_first_query_index_lists_for_set S))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget))"

lemma finite_fri_zero_round_small_agreement_sets[simp]:
  "finite fri_zero_round_small_agreement_sets"
proof -
  have "fri_zero_round_small_agreement_sets \<subseteq> Pow query_sample_space"
    unfolding fri_zero_round_small_agreement_sets_def by blast
  then show ?thesis
    by (rule finite_subset) simp
qed

lemma fri_zero_round_first_query_index_lists_for_set_subset:
  "fri_zero_round_first_query_index_lists_for_set S
    \<subseteq> fri_query_index_list_space"
  unfolding fri_zero_round_first_query_index_lists_for_set_def by blast

lemma trace_fri_zero_round_table_target_eq_agreement_set_target:
  "fri_zero_round_first_query_index_lists table final =
    fri_zero_round_first_query_index_lists_for_set
      (fri_final_value_agreement_set table final)"
  unfolding fri_zero_round_first_query_index_lists_def
    fri_zero_round_first_query_index_lists_for_set_def
  by simp

lemma checked_staged_security_trace_fri_zero_round_agreement_set_target_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and S_in: "S \<in> fri_zero_round_small_agreement_sets"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          trace_fri_query_index_list_set_hit s
            (fri_zero_round_first_query_index_lists_for_set S)))
      adversary_initial_state \<le>
      nnreal (card (fri_zero_round_first_query_index_lists_for_set S)) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (fri_zero_round_first_query_index_lists_for_set S))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule checked_staged_security_trace_fri_query_index_list_set_hit_exact_product_bound
      [OF wf controlled fri_zero_round_first_query_index_lists_for_set_subset])

lemma checked_staged_security_trace_fri_zero_round_query_list_target_bound_from_agreement_sets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_query_list_target_hit)
      adversary_initial_state \<le>
      trace_fri_zero_round_agreement_set_target_error_for budgets"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?A = "fri_zero_round_small_agreement_sets"
  let ?P =
    "\<lambda>S. staged_security_with_data_state_verifier_event
      (\<lambda>s.
        trace_fri_query_index_list_set_hit s
          (fri_zero_round_first_query_index_lists_for_set S))"
  have event_le:
    "wp_event ?M
      (staged_security_with_data_state_verifier_event
        trace_fri_zero_round_query_list_target_hit)
      adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. \<exists>S \<in> ?A. ?P S out)
        adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and hit:
      "staged_security_with_data_state_verifier_event
        trace_fri_zero_round_query_list_target_hit out"
    show "\<exists>S\<in>?A. ?P S out"
    proof (cases out)
      case None
      then show ?thesis
        using hit unfolding staged_security_with_data_state_verifier_event_def
          trace_fri_zero_round_query_list_target_hit_def
        by simp
    next
      case (Some out_data)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases out_data, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      have local_hit:
        "trace_fri_zero_round_query_list_target_hit ?s
          (Some (result, final_state))"
        using hit unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
      then obtain trace_table trace_final where query_hit:
        "trace_fri_query_index_list_set_hit ?s
          (fri_zero_round_first_query_index_lists trace_table trace_final)
          (Some (result, final_state))"
        and small:
          "card (fri_final_value_agreement_set trace_table trace_final)
            < query_sample_space_size"
        by (rule trace_fri_zero_round_query_list_target_hitE)
      let ?S = "fri_final_value_agreement_set trace_table trace_final"
      have S_in: "?S \<in> ?A"
        unfolding fri_zero_round_small_agreement_sets_def
        using fri_final_value_agreement_set_subset small by simp
      have query_hit':
        "trace_fri_query_index_list_set_hit ?s
          (fri_zero_round_first_query_index_lists_for_set ?S)
          (Some (result, final_state))"
        using query_hit
        by (simp add:
            trace_fri_zero_round_table_target_eq_agreement_set_target)
      have "?P ?S out"
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        using query_hit' by simp
      show ?thesis
        using S_in \<open>?P ?S out\<close> by blast
    qed
  qed
  have union_bound:
    "wp_event ?M (\<lambda>out. \<exists>S \<in> ?A. ?P S out)
      adversary_initial_state \<le>
      (\<Sum>S \<in> ?A.
        nnreal (card (fri_zero_round_first_query_index_lists_for_set S)) *
          (1 / nnreal (card query_sample_space)) ^ rounds +
        hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (fri_zero_round_first_query_index_lists_for_set S))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget))"
  proof (rule wp_event_finite_UN_bound)
    show "finite ?A"
      by simp
  next
    fix S
    assume S_in: "S \<in> ?A"
    show "wp_event ?M (?P S) adversary_initial_state \<le>
      nnreal (card (fri_zero_round_first_query_index_lists_for_set S)) *
        (1 / nnreal (card query_sample_space)) ^ rounds +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (fri_zero_round_first_query_index_lists_for_set S))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
      by (rule checked_staged_security_trace_fri_zero_round_agreement_set_target_bound
          [OF wf controlled S_in])
  qed
  show ?thesis
    by (rule order_trans[OF event_le])
      (use union_bound in
        \<open>simp add: trace_fri_zero_round_agreement_set_target_error_for_def\<close>)
qed

end

end
