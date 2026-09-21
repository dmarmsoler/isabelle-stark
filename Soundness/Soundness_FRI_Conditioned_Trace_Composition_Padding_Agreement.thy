theory Soundness_FRI_Conditioned_Trace_Composition_Padding_Agreement
  imports
    Stark.Soundness_FRI_Conditioned_Composition_Padding_Agreement
    Stark.Soundness_FRI_RO_Actual_Query_Trace_Composition_Boundary
begin

context soundness
begin

definition trace_composition_query_index_bound_for :: "nat \<Rightarrow> nat"
where
  "trace_composition_query_index_bound_for d =
    (query_agreement_bound_for d +
      (powers - 1) * query_sample_space_size +
      (\<Sum>k \<in> {1..<powers}. k * scale)) div powers"

lemma trace_composition_accepted_indices_card_bound_semantic_for:
  assumes lengths: "length original = length candidate"
    and trace_low: "trace_table_low_degree candidate"
    and composition_low:
      "composition_table_low_degree composition_degree_bound composition"
    and composition_bad:
      "\<not> composition_table_low_degree maxDegree composition"
  shows
    "card (trace_composition_accepted_indices
        original candidate composition as) \<le>
      query_agreement_bound_for composition_degree_bound +
        (\<Sum>k \<in> {1..<powers}.
          ((query_sample_space_size -
            card (trace_table_base_agreement_indices original candidate)) +
            k * scale))"
proof -
  let ?accepted =
    "trace_composition_accepted_indices original candidate composition as"
  let ?agreement = "query_agreement_indices candidate composition as"
  let ?boundary = "trace_power_boundary_indices original candidate"
  have union_subset: "?accepted \<subseteq> ?agreement \<union> ?boundary"
    by (rule trace_composition_accepted_indices_subset[OF lengths])
  have finite_union: "finite (?agreement \<union> ?boundary)"
    unfolding query_agreement_indices_def query_sample_space_def
    by (rule finite_UnI; simp add:
      finite_subset[OF trace_power_boundary_indices_subset_query_sample_space])
  have accepted_union: "card ?accepted \<le> card (?agreement \<union> ?boundary)"
    by (rule card_mono[OF finite_union union_subset])
  have union_sum:
      "card (?agreement \<union> ?boundary) \<le>
        card ?agreement + card ?boundary"
    by (rule card_Un_le)
  have agreement_bound:
      "card ?agreement \<le>
        query_agreement_bound_for composition_degree_bound"
    by (rule
      query_agreement_indices_card_bound_for_if_composition_not_low_max[
        OF trace_low composition_low composition_bad])
  have boundary_bound:
      "card ?boundary \<le>
        (\<Sum>k \<in> {1..<powers}.
          ((query_sample_space_size -
            card (trace_table_base_agreement_indices original candidate)) +
            k * scale))"
    by (rule trace_power_boundary_indices_card_bound)
  show ?thesis
    by (rule order_trans[OF accepted_union])
      (rule order_trans[OF union_sum add_mono[OF agreement_bound boundary_bound]])
qed

lemma trace_composition_accepted_indices_card_bound_for:
  assumes lengths: "length original = length candidate"
    and trace_low: "trace_table_low_degree candidate"
    and composition_low:
      "composition_table_low_degree composition_degree_bound composition"
    and composition_bad:
      "\<not> composition_table_low_degree maxDegree composition"
  shows
    "card (trace_composition_accepted_indices
        original candidate composition as) \<le>
      trace_composition_query_index_bound_for composition_degree_bound"
proof -
  let ?accepted =
    "trace_composition_accepted_indices original candidate composition as"
  let ?A = "trace_table_base_agreement_indices original candidate"
  let ?K = "query_agreement_bound_for composition_degree_bound"
  let ?tail = "\<Sum>k \<in> {1..<powers}. k * scale"
  have accepted_le_A: "card ?accepted \<le> card ?A"
    by (rule trace_composition_accepted_indices_card_le_base_agreement)
  have A_subset: "?A \<subseteq> query_sample_space"
    unfolding trace_table_base_agreement_indices_def by auto
  have A_le_space: "card ?A \<le> query_sample_space_size"
  proof -
    have "card ?A \<le> card query_sample_space"
      by (rule card_mono[OF finite_query_sample_space A_subset])
    then show ?thesis by simp
  qed
  have accepted_semantic:
      "card ?accepted \<le>
        ?K + (\<Sum>k \<in> {1..<powers}.
          ((query_sample_space_size - card ?A) + k * scale))"
    by (rule trace_composition_accepted_indices_card_bound_semantic_for[
      OF lengths trace_low composition_low composition_bad])
  have sum_eq:
      "(\<Sum>k \<in> {1..<powers}.
          ((query_sample_space_size - card ?A) + k * scale)) =
        (powers - 1) * (query_sample_space_size - card ?A) + ?tail"
    by (simp add: sum.distrib mult.commute)
  have accepted_upper:
      "card ?accepted \<le>
        ?K + (powers - 1) * (query_sample_space_size - card ?A) + ?tail"
    using accepted_semantic sum_eq by simp
  have sub_add:
      "query_sample_space_size - card ?A + card ?A =
        query_sample_space_size"
    using A_le_space by simp
  have powers_eq: "powers = (powers - 1) + 1"
    using powers_pos by arith
  have multiplied_base:
      "(powers - 1) * card ?accepted \<le> (powers - 1) * card ?A"
    using accepted_le_A by (rule mult_le_mono2)
  have partition:
      "(powers - 1) * card ?A +
        (powers - 1) * (query_sample_space_size - card ?A) =
       (powers - 1) * query_sample_space_size"
  proof -
    have "(powers - 1) * card ?A +
        (powers - 1) * (query_sample_space_size - card ?A) =
      (powers - 1) * (card ?A +
        (query_sample_space_size - card ?A))"
      by (simp add: distrib_left)
    also have "... = (powers - 1) * query_sample_space_size"
      using sub_add by (simp add: add.commute)
    finally show ?thesis .
  qed
  have weighted:
      "powers * card ?accepted \<le>
        ?K + (powers - 1) * query_sample_space_size + ?tail"
  proof -
    have components:
        "(powers - 1) * card ?accepted + card ?accepted \<le>
          (powers - 1) * card ?A +
            (?K + (powers - 1) *
              (query_sample_space_size - card ?A) + ?tail)"
      by (rule add_mono[OF multiplied_base accepted_upper])
    have left_eq:
        "powers * card ?accepted =
          (powers - 1) * card ?accepted + card ?accepted"
      using powers_eq by (metis distrib_right mult_1_left)
    have right_eq:
        "(powers - 1) * card ?A +
          (?K + (powers - 1) *
            (query_sample_space_size - card ?A) + ?tail) =
         ?K + (powers - 1) * query_sample_space_size + ?tail"
      using partition by arith
    show ?thesis using components left_eq right_eq by simp
  qed
  show ?thesis
    unfolding trace_composition_query_index_bound_for_def
    using powers_pos weighted
    by (simp add: less_eq_div_iff_mult_less_eq mult.commute)
qed

definition trace_composition_padding_query_lists
where
  "trace_composition_padding_query_lists original candidate composition as d =
    (if trace_table_low_degree candidate \<and>
        composition_table_low_degree d composition \<and>
        \<not> composition_table_low_degree maxDegree composition
     then query_index_lists_over
       (trace_composition_accepted_indices original candidate composition as)
     else {})"

lemma trace_composition_padding_query_lists_subset:
  "trace_composition_padding_query_lists original candidate composition as d
    \<subseteq> fri_query_index_list_space"
proof (cases "trace_table_low_degree candidate \<and>
    composition_table_low_degree d composition \<and>
    \<not> composition_table_low_degree maxDegree composition")
  case True
  then show ?thesis
    unfolding trace_composition_padding_query_lists_def
    by (simp add: query_index_lists_over_subset_fri_query_index_list_space
      trace_composition_accepted_indices_subset_query_sample_space)
next
  case False
  then show ?thesis
    unfolding trace_composition_padding_query_lists_def
    by (simp only: if_not_P[OF False] if_False empty_subsetI)
qed

lemma card_trace_composition_padding_query_lists:
  assumes lengths: "length original = length candidate"
  shows
    "card (trace_composition_padding_query_lists
        original candidate composition as d) \<le>
      trace_composition_query_index_bound_for d ^ rounds"
proof (cases "trace_table_low_degree candidate \<and>
    composition_table_low_degree d composition \<and>
    \<not> composition_table_low_degree maxDegree composition")
  case True
  then have trace_low: "trace_table_low_degree candidate"
    and composition_low: "composition_table_low_degree d composition"
    and composition_bad:
      "\<not> composition_table_low_degree maxDegree composition"
    by blast+
  have finite_indices:
      "finite (trace_composition_accepted_indices
        original candidate composition as)"
    by (rule finite_subset[
      OF trace_composition_accepted_indices_subset_query_sample_space
        finite_query_sample_space])
  have card_eq:
      "card (trace_composition_padding_query_lists
          original candidate composition as d) =
        card (trace_composition_accepted_indices
          original candidate composition as) ^ rounds"
    unfolding trace_composition_padding_query_lists_def if_P[OF True]
    by (rule card_query_index_lists_over[OF finite_indices])
  have indices_bound:
      "card (trace_composition_accepted_indices
          original candidate composition as) \<le>
        trace_composition_query_index_bound_for d"
    by (rule trace_composition_accepted_indices_card_bound_for[
      OF lengths trace_low composition_low composition_bad])
  show ?thesis
    unfolding card_eq by (rule power_mono[OF indices_bound]) simp
next
  case False
  then show ?thesis
    unfolding trace_composition_padding_query_lists_def
    by (simp only: if_not_P[OF False] if_False card.empty zero_le)
qed

lemma trace_composition_padding_query_lists_raw_relation_fiber_bound:
  assumes lengths: "length original = length candidate"
  shows
    "query_index_raw_list_relation_fiber_bound
      (trace_composition_padding_query_lists
        original candidate composition as d) \<le>
      rounds * query_raw_preimage_card_envelope
        (rounds * (trace_composition_query_index_bound_for d ^ rounds))"
proof (rule query_index_raw_list_relation_fiber_bound_by_card)
  show "trace_composition_padding_query_lists
      original candidate composition as d \<subseteq> fri_query_index_list_space"
    by (rule trace_composition_padding_query_lists_subset)
  show "card (trace_composition_padding_query_lists
      original candidate composition as d) \<le>
      trace_composition_query_index_bound_for d ^ rounds"
    by (rule card_trace_composition_padding_query_lists[OF lengths])
qed

lemma trace_composition_padding_query_lists_strict:
  assumes lengths: "length original = length candidate"
    and bound_lt:
      "trace_composition_query_index_bound_for d < query_sample_space_size"
    and rounds_pos: "0 < rounds"
  shows
    "card (trace_composition_padding_query_lists
        original candidate composition as d) <
      card fri_query_index_list_space"
proof -
  have "card (trace_composition_padding_query_lists
        original candidate composition as d) \<le>
      trace_composition_query_index_bound_for d ^ rounds"
    by (rule card_trace_composition_padding_query_lists[OF lengths])
  also have "... < query_sample_space_size ^ rounds"
    by (rule power_strict_mono[OF bound_lt _ rounds_pos]) simp
  also have "... = card fri_query_index_list_space"
    unfolding card_fri_query_index_list_space card_query_sample_space by simp
  finally show ?thesis .
qed

end
end