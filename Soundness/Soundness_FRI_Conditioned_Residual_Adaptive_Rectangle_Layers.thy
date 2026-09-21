theory Soundness_FRI_Conditioned_Residual_Adaptive_Rectangle_Layers
  imports Soundness_FRI_Query_Head_Adaptive_Rectangle_Family
begin

context soundness
begin

definition fri_conditioned_residual_layer_query_indices
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow> nat \<Rightarrow> nat set"
where
  "fri_conditioned_residual_layer_query_indices roots challenges layers i =
    fri_conditioned_query_indices roots i
      (fri_conditioned_agreement_indices i
        (layers ! i) (layers ! Suc i) (challenges ! i))"

lemma fri_conditioned_residual_layer_query_indices_subset:
  "fri_conditioned_residual_layer_query_indices roots challenges layers i
    \<subseteq> query_sample_space"
  unfolding fri_conditioned_residual_layer_query_indices_def
  by (rule fri_conditioned_query_indices_subset)

lemma fri_conditioned_quantitative_residual_query_lists_rectangle_cover:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "fri_conditioned_quantitative_residual_query_lists d roots challenges
        final_value prefix_state
      \<subseteq>
      (\<Union>i<length challenges.
        fri_conditioned_query_lists
          (fri_conditioned_residual_layer_query_indices roots challenges
            (fri_builder_conceptual_layers roots prefix_state final_value) i))"
  proof
  let ?layers =
    "fri_builder_conceptual_layers roots prefix_state final_value"
  fix qs
  assume qs_in:
    "qs \<in>
      fri_conditioned_quantitative_residual_query_lists d roots challenges
        final_value prefix_state"
  then obtain i where i_bound: "i < length challenges"
    and qs_space: "qs \<in> fri_query_index_list_space"
    and residual:
      "qs \<in> fri_conditioned_residual_query_lists roots challenges ?layers i"
    unfolding fri_conditioned_quantitative_residual_query_lists_def
    by blast
  have layer_bound: "i < length roots"
    using i_bound lengths by simp
  have layer_subset:
    "fri_conditioned_residual_query_lists roots challenges ?layers i \<inter>
        fri_query_index_list_space
      \<subseteq>
      fri_conditioned_query_lists
        (fri_conditioned_residual_layer_query_indices roots challenges
          ?layers i)"
    unfolding fri_conditioned_residual_layer_query_indices_def
    by (rule fri_conditioned_residual_query_lists_restricted_subset[
          OF eval_power roots_le layer_bound])
  have rectangle:
    "qs \<in>
      fri_conditioned_query_lists
        (fri_conditioned_residual_layer_query_indices roots challenges
          ?layers i)"
    by (rule set_mp[OF layer_subset]) (use residual qs_space in blast)
  show
    "qs \<in>
      (\<Union>i<length challenges.
        fri_conditioned_query_lists
          (fri_conditioned_residual_layer_query_indices roots challenges
            ?layers i))"
    using i_bound rectangle by blast
qed


definition fri_conditioned_residual_active_layers
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "fri_conditioned_residual_active_layers d roots challenges
      final_value prefix_state =
    {i. i < length challenges \<and>
      challenges ! i \<notin>
        fri_conditioned_bad_challenges d
          (\<lambda>j _. fri_builder_conceptual_layers roots prefix_state
            final_value ! j)
          i (take i challenges) \<and>
      \<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i
          (fri_builder_conceptual_layers roots prefix_state
            final_value ! i)) \<and>
      fri_table_low_degree_on
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i)
          (fri_builder_conceptual_layers roots prefix_state
            final_value ! Suc i))}"

lemma finite_fri_conditioned_residual_active_layers[simp]:
  "finite
    (fri_conditioned_residual_active_layers d roots challenges
      final_value prefix_state)"
  unfolding fri_conditioned_residual_active_layers_def
  by (rule finite_subset[OF _ finite_lessThan[of "length challenges"]])
    auto

lemma fri_conditioned_quantitative_residual_query_lists_active_rectangle_cover:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "fri_conditioned_quantitative_residual_query_lists d roots challenges
        final_value prefix_state
      \<subseteq>
      (\<Union>i\<in>fri_conditioned_residual_active_layers d roots challenges
          final_value prefix_state.
        fri_conditioned_query_lists
          (fri_conditioned_residual_layer_query_indices roots challenges
            (fri_builder_conceptual_layers roots prefix_state final_value) i))"
  proof
  let ?layers =
    "fri_builder_conceptual_layers roots prefix_state final_value"
  fix qs
  assume qs_in:
    "qs \<in>
      fri_conditioned_quantitative_residual_query_lists d roots challenges
        final_value prefix_state"
  then obtain i where i_bound: "i < length challenges"
    and not_bad:
      "challenges ! i \<notin>
        fri_conditioned_bad_challenges d (\<lambda>j _. ?layers ! j)
          i (take i challenges)"
    and current_not_low:
      "\<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i (?layers ! i))"
    and next_low:
      "fri_table_low_degree_on
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i) (?layers ! Suc i))"
    and qs_space: "qs \<in> fri_query_index_list_space"
    and residual:
      "qs \<in> fri_conditioned_residual_query_lists roots challenges ?layers i"
    unfolding fri_conditioned_quantitative_residual_query_lists_def
    by blast
  have active:
    "i \<in> fri_conditioned_residual_active_layers d roots challenges
      final_value prefix_state"
    using i_bound not_bad current_not_low next_low
    unfolding fri_conditioned_residual_active_layers_def
    by simp
  have layer_bound: "i < length roots"
    using i_bound lengths by simp
  have layer_subset:
    "fri_conditioned_residual_query_lists roots challenges ?layers i \<inter>
        fri_query_index_list_space
      \<subseteq>
      fri_conditioned_query_lists
        (fri_conditioned_residual_layer_query_indices roots challenges
          ?layers i)"
    unfolding fri_conditioned_residual_layer_query_indices_def
    by (rule fri_conditioned_residual_query_lists_restricted_subset[
          OF eval_power roots_le layer_bound])
  have rectangle:
    "qs \<in>
      fri_conditioned_query_lists
        (fri_conditioned_residual_layer_query_indices roots challenges
          ?layers i)"
    by (rule set_mp[OF layer_subset]) (use residual qs_space in blast)
  show
    "qs \<in>
      (\<Union>i\<in>fri_conditioned_residual_active_layers d roots challenges
          final_value prefix_state.
        fri_conditioned_query_lists
          (fri_conditioned_residual_layer_query_indices roots challenges
            ?layers i))"
    using active rectangle by blast
qed


lemma card_fri_conditioned_residual_layer_query_indices_active:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and lengths: "length challenges = length roots"
    and active:
      "i \<in> fri_conditioned_residual_active_layers d roots challenges
        final_value prefix_state"
  shows
    "card
      (fri_conditioned_residual_layer_query_indices roots challenges
        (fri_builder_conceptual_layers roots prefix_state final_value) i)
      \<le>
      modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) - 1)"
  proof -
  let ?layers =
    "fri_builder_conceptual_layers roots prefix_state final_value"
  from active have i_bound: "i < length challenges"
    and not_bad:
      "challenges ! i \<notin>
        fri_conditioned_bad_challenges d (\<lambda>j _. ?layers ! j)
          i (take i challenges)"
    and current_not_low:
      "\<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i (?layers ! i))"
    and next_low:
      "fri_table_low_degree_on
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i) (?layers ! Suc i))"
    unfolding fri_conditioned_residual_active_layers_def
    by auto
  have root_i: "i < length roots"
    using i_bound lengths by simp
  have root_le: "length roots \<le> N"
    using round_count rounds_le lengths by simp
  have current_cover:
    "length (fri_canonical_domain_at i) \<le> length (?layers ! i)"
    by (rule fri_builder_conceptual_layers_cover)
      (use i_bound lengths in simp)
  have next_cover:
    "length (fri_canonical_domain_at (Suc i)) \<le>
      length (?layers ! Suc i)"
    by (rule fri_builder_conceptual_layers_cover)
      (use i_bound lengths in simp)
  have agreement_card:
    "card
      (fri_conditioned_agreement_indices i
        (?layers ! i) (?layers ! Suc i) (challenges ! i)) \<le>
      length (fri_canonical_domain_at (Suc i)) - 1"
    by (rule card_fri_conditioned_agreement_indices_strict[
          where N=N and d=d and committed="\<lambda>j _. ?layers ! j"
            and prefix="take i challenges",
          OF eval_power])
      (use round_count rounds_le current_cover next_cover
        current_not_low next_low not_bad i_bound in simp_all)
  have modulus_pos:
    "0 < length (fri_canonical_domain_at (Suc i))"
    by (rule fri_canonical_domain_at_pos[OF eval_power])
      (use round_count rounds_le i_bound in simp)
  show ?thesis
    unfolding fri_conditioned_residual_layer_query_indices_def
    by (rule card_fri_conditioned_query_indices[
          OF modulus_pos fri_conditioned_agreement_indices_subset
            agreement_card])
qed


definition fri_conditioned_residual_rectangle_layer_raw_card_bound
  :: "nat \<Rightarrow> nat"
where
  "fri_conditioned_residual_rectangle_layer_raw_card_bound i =
    query_raw_preimage_card_envelope
      (modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) - 1))"

definition ro_checked_staged_conditioned_residual_rectangle_error_adaptive
  :: "nat \<Rightarrow> staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_residual_rectangle_error_adaptive d budgets =
    (\<Sum>i<ceil_log (Suc d).
      (nnreal
          (fri_conditioned_residual_rectangle_layer_raw_card_bound i) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets))"

lemma fri_conditioned_residual_active_layer_probability_sum_le:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "(\<Sum>i\<in>fri_conditioned_residual_active_layers d roots challenges
        final_value prefix_state.
      (nnreal
          (query_raw_preimage_card_envelope
            (card
              (fri_conditioned_residual_layer_query_indices roots challenges
                (fri_builder_conceptual_layers roots prefix_state final_value)
                i))) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets))
    \<le> ro_checked_staged_conditioned_residual_rectangle_error_adaptive
        d budgets"
proof -
  let ?A =
    "fri_conditioned_residual_active_layers d roots challenges
      final_value prefix_state"
  let ?B = "{..<ceil_log (Suc d)}"
  let ?f =
    "\<lambda>i.
      (nnreal
          (query_raw_preimage_card_envelope
            (card
              (fri_conditioned_residual_layer_query_indices roots challenges
                (fri_builder_conceptual_layers roots prefix_state final_value)
                i))) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets)"
  let ?g =
    "\<lambda>i.
      (nnreal
          (fri_conditioned_residual_rectangle_layer_raw_card_bound i) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets)"
  have subset: "?A \<subseteq> ?B"
    using round_count
    unfolding fri_conditioned_residual_active_layers_def
    by auto
  have local: "(\<Sum>i\<in>?A. ?f i) \<le> (\<Sum>i\<in>?A. ?g i)"
  proof (rule sum_mono)
    fix i
    assume i_active: "i \<in> ?A"
    let ?I =
      "fri_conditioned_residual_layer_query_indices roots challenges
        (fri_builder_conceptual_layers roots prefix_state final_value) i"
    let ?E =
      "modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) - 1)"
    have I_card: "card ?I \<le> ?E"
      by (rule
          card_fri_conditioned_residual_layer_query_indices_active[
            OF eval_power round_count rounds_le lengths i_active])
    have raw_card:
      "query_raw_preimage_card_envelope (card ?I) \<le>
        query_raw_preimage_card_envelope ?E"
      by (rule query_raw_preimage_card_envelope_mono[OF I_card])
    have fraction_le:
      "nnreal (query_raw_preimage_card_envelope (card ?I)) /
          nnreal size
        \<le>
        nnreal (query_raw_preimage_card_envelope ?E) / nnreal size"
      by (rule nnreal_nat_divide_right_mono[OF raw_card])
    show "?f i \<le> ?g i"
      unfolding
        fri_conditioned_residual_rectangle_layer_raw_card_bound_def
        Let_def
      by (rule power_mono[OF fraction_le]) simp
  qed
  have extend: "(\<Sum>i\<in>?A. ?g i) \<le> (\<Sum>i\<in>?B. ?g i)"
    by (rule sum_mono2) (use subset in auto)
  show ?thesis
    unfolding
      ro_checked_staged_conditioned_residual_rectangle_error_adaptive_def
      Let_def
    by (rule order_trans[OF local extend])
qed

end
end
