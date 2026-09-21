(*  Title:      Stark/Soundness_FRI_Prechallenge_Query_Product.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Prechallenge_Query_Product
  imports
    Soundness_FRI_Prechallenge_Conceptual_Witness
    Soundness_FRI_Query_List_Exact_Product
begin

text \<open>
  Exact query-list accounting for prefix-fixed conceptual trace tables.
  The relation-fiber bound retains the raw sampler fibers and bounds each
  position by the exact floor/remainder envelope instead of replacing the
  bad-index set by the full sample space.
\<close>

context soundness
begin

lemma card_query_index_raw_preimage_floor_remainder:
  assumes subset: "B \<subseteq> query_sample_space"
  shows
    "card (query_index_raw_preimage B) =
      (size div query_sample_space_size) * card B +
        card (B \<inter> {..<size mod query_sample_space_size})"
  by (rule card_query_index_raw_preimage_exact[OF subset])

lemma query_index_raw_list_position_values_base_agreement_subset:
  assumes i_bound: "i < rounds"
  shows
    "query_index_raw_list_position_values
        (trace_table_base_agreement_query_lists trace_table trace_table') i
      \<subseteq>
     query_index_raw_preimage
       (trace_table_base_agreement_indices trace_table trace_table')"
proof
  fix raw
  assume raw_in:
    "raw \<in>
      query_index_raw_list_position_values
        (trace_table_base_agreement_query_lists trace_table trace_table') i"
  from raw_in obtain raws where raws_in:
      "raws \<in>
        query_index_raw_list_preimage
          (trace_table_base_agreement_query_lists trace_table trace_table')"
    and raw_eq: "raw = raws ! i"
    unfolding query_index_raw_list_position_values_def
    using i_bound by blast
  have raws_len: "length raws = rounds"
    and mapped_in:
      "map (\<lambda>x. index (to_nat x)) raws \<in>
        trace_table_base_agreement_query_lists trace_table trace_table'"
    using raws_in
    unfolding query_index_raw_list_preimage_def by blast+
  have mapped_subset:
    "set (map (\<lambda>x. index (to_nat x)) raws) \<subseteq>
      trace_table_base_agreement_indices trace_table trace_table'"
    using mapped_in
    unfolding trace_table_base_agreement_query_lists_def by blast
  have i_len: "i < length raws"
    using i_bound raws_len by simp
  have mapped_nth:
    "map (\<lambda>x. index (to_nat x)) raws ! i =
      index (to_nat raw)"
    using raw_eq i_len by simp
  have mapped_mem:
    "map (\<lambda>x. index (to_nat x)) raws ! i \<in>
      set (map (\<lambda>x. index (to_nat x)) raws)"
    by (rule nth_mem) (use i_len in simp)
  have
    "index (to_nat raw) \<in>
      trace_table_base_agreement_indices trace_table trace_table'"
    by (rule set_mp[OF mapped_subset])
      (use mapped_mem mapped_nth in simp)
  then show
    "raw \<in>
      query_index_raw_preimage
        (trace_table_base_agreement_indices trace_table trace_table')"
    unfolding query_index_raw_preimage_def by simp
qed

lemma card_query_index_raw_list_position_values_base_agreement_le:
  assumes i_bound: "i < rounds"
  shows
    "card
      (query_index_raw_list_position_values
        (trace_table_base_agreement_query_lists trace_table trace_table') i)
      \<le>
     query_raw_preimage_card_envelope
       (card (trace_table_base_agreement_indices trace_table trace_table'))"
proof -
  let ?A =
    "trace_table_base_agreement_indices trace_table trace_table'"
  have pos_subset:
    "query_index_raw_list_position_values
        (trace_table_base_agreement_query_lists trace_table trace_table') i
      \<subseteq> query_index_raw_preimage ?A"
    by (rule
        query_index_raw_list_position_values_base_agreement_subset
          [OF i_bound])
  have card_le:
    "card
      (query_index_raw_list_position_values
        (trace_table_base_agreement_query_lists trace_table trace_table') i)
      \<le> card (query_index_raw_preimage ?A)"
    by (rule card_mono[OF _ pos_subset]) simp
  have raw_card:
    "card (query_index_raw_preimage ?A) \<le>
      query_raw_preimage_card_envelope (card ?A)"
    by (rule card_query_index_raw_preimage_le_query_envelope)
      (rule trace_table_base_agreement_indices_subset)
  show ?thesis
    by (rule order_trans[OF card_le raw_card])
qed

lemma query_index_raw_list_relation_fiber_bound_base_agreement_le:
  "query_index_raw_list_relation_fiber_bound
      (trace_table_base_agreement_query_lists trace_table trace_table')
    \<le>
   rounds *
     query_raw_preimage_card_envelope
       (card (trace_table_base_agreement_indices trace_table trace_table'))"
proof -
  have
    "(\<Sum>i<rounds.
      card
        (query_index_raw_list_position_values
          (trace_table_base_agreement_query_lists trace_table trace_table')
          i))
      \<le>
     (\<Sum>i<rounds.
      query_raw_preimage_card_envelope
        (card
          (trace_table_base_agreement_indices trace_table trace_table')))"
  proof (rule sum_mono)
    fix i
    assume i_in: "i \<in> {..<rounds}"
    have i_bound: "i < rounds"
      using i_in by simp
    show
      "card
        (query_index_raw_list_position_values
          (trace_table_base_agreement_query_lists trace_table trace_table')
          i)
        \<le>
       query_raw_preimage_card_envelope
         (card
           (trace_table_base_agreement_indices trace_table trace_table'))"
      by (rule
          card_query_index_raw_list_position_values_base_agreement_le
            [OF i_bound])
  qed
  then show ?thesis
    unfolding query_index_raw_list_relation_fiber_bound_def
    by simp
qed

lemma query_index_raw_list_relation_fiber_bound_base_agreement_parameter_le:
  assumes trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows
    "query_index_raw_list_relation_fiber_bound
        (trace_table_base_agreement_query_lists trace_table trace_table')
      \<le>
     rounds * query_raw_preimage_card_envelope clength"
proof -
  have general:
    "query_index_raw_list_relation_fiber_bound
        (trace_table_base_agreement_query_lists trace_table trace_table')
      \<le>
     rounds *
       query_raw_preimage_card_envelope
         (card
           (trace_table_base_agreement_indices trace_table trace_table'))"
    by (rule
        query_index_raw_list_relation_fiber_bound_base_agreement_le)
  have agreement_le:
    "card
        (trace_table_base_agreement_indices trace_table trace_table')
      \<le> clength"
    using trace_table_base_agreement_indices_card_bound
        [OF trace_low trace'_low distinct]
    by simp
  have envelope_le:
    "query_raw_preimage_card_envelope
        (card
          (trace_table_base_agreement_indices trace_table trace_table'))
      \<le> query_raw_preimage_card_envelope clength"
    by (rule query_raw_preimage_card_envelope_mono[OF agreement_le])
  have
    "rounds *
       query_raw_preimage_card_envelope
         (card
           (trace_table_base_agreement_indices trace_table trace_table'))
      \<le>
     rounds * query_raw_preimage_card_envelope clength"
    using envelope_le by simp
  then show ?thesis
    by (rule order_trans[OF general])
qed

theorem checked_staged_security_trace_fri_base_agreement_query_lists_parameter_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_low: "trace_table_low_degree trace_table"
    and trace'_low: "trace_table_low_degree trace_table'"
    and distinct: "trace_table \<noteq> trace_table'"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s
          (trace_table_base_agreement_query_lists
            trace_table trace_table')))
      adversary_initial_state
      \<le>
     nnreal (clength ^ rounds) *
       (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds +
     hash_relation_budget_value
       (rounds * query_raw_preimage_card_envelope clength)
       (staged_attacker_query_budget budgets +
         staged_challenge_query_budget)"
proof -
  let ?Q =
    "trace_table_base_agreement_query_lists trace_table trace_table'"
  have exact:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_index_list_set_hit s ?Q))
      adversary_initial_state
      \<le>
     nnreal (card ?Q) *
       (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds +
     hash_relation_budget_value
       (query_index_raw_list_relation_fiber_bound ?Q)
       (staged_attacker_query_budget budgets +
         staged_challenge_query_budget)"
    by (rule
        checked_staged_security_trace_fri_query_index_list_set_hit_exact_product_bound
          [OF wf controlled
            trace_table_base_agreement_query_lists_subset])
  have product:
    "nnreal (card ?Q) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds
      \<le>
     nnreal (clength ^ rounds) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule
        trace_table_base_agreement_query_lists_exact_product_bound
          [OF trace_low trace'_low distinct])
  have fiber:
    "query_index_raw_list_relation_fiber_bound ?Q
      \<le>
     rounds * query_raw_preimage_card_envelope clength"
    by (rule
        query_index_raw_list_relation_fiber_bound_base_agreement_parameter_le
          [OF trace_low trace'_low distinct])
  have relation:
    "hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound ?Q)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)
      \<le>
     hash_relation_budget_value
       (rounds * query_raw_preimage_card_envelope clength)
       (staged_attacker_query_budget budgets +
         staged_challenge_query_budget)"
    by (rule hash_relation_budget_value_mono_left[OF fiber])
  show ?thesis
    by (rule order_trans[OF exact])
      (intro add_mono product relation)
qed

end

end
