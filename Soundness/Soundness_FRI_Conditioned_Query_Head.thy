theory Soundness_FRI_Conditioned_Query_Head
  imports
    Stark.Soundness_FRI_Conditioned_Quantitative_Split
    Stark.Soundness_FRI_RO_Actual_Query_Trace_Composition_Query_Bound
begin

context soundness
begin

definition fri_conditioned_quantitative_residual_query_lists
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f protocol_channel \<Rightarrow>
      nat list set"
where
  "fri_conditioned_quantitative_residual_query_lists d roots challenges
      final_value prefix_state =
    {qs \<in> fri_query_index_list_space.
      \<exists>i < length challenges.
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
              final_value ! Suc i)) \<and>
        qs \<in> fri_conditioned_residual_query_lists roots challenges
          (fri_builder_conceptual_layers roots prefix_state final_value) i}"


definition fri_conditioned_quantitative_residual_query_lists_at
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f protocol_channel \<Rightarrow> nat \<Rightarrow>
      nat list set"
where
  "fri_conditioned_quantitative_residual_query_lists_at d roots challenges
      final_value prefix_state i =
    {qs \<in> fri_query_index_list_space.
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
            final_value ! Suc i)) \<and>
      qs \<in> fri_conditioned_residual_query_lists roots challenges
        (fri_builder_conceptual_layers roots prefix_state final_value) i}"

lemma fri_conditioned_quantitative_residual_query_lists_union:
  "fri_conditioned_quantitative_residual_query_lists d roots challenges
      final_value prefix_state =
    (\<Union>i < length challenges.
      fri_conditioned_quantitative_residual_query_lists_at d roots challenges
        final_value prefix_state i)"
  unfolding fri_conditioned_quantitative_residual_query_lists_def
    fri_conditioned_quantitative_residual_query_lists_at_def
  by auto

lemma fri_builder_conceptual_layers_cover:
  assumes j_bound: "j \<le> length roots"
  shows
    "length (fri_canonical_domain_at j) \<le>
      length (fri_builder_conceptual_layers roots prefix_state
        final_value ! j)"
proof (cases "j < length roots")
  case True
  then show ?thesis
    unfolding fri_builder_conceptual_layers_at[OF True] by simp
next
  case False
  then have j_eq: "j = length roots"
    using j_bound by simp
  show ?thesis
    unfolding j_eq
      fri_builder_conceptual_layers_final[
        of roots prefix_state final_value]
    by simp
qed

lemma card_fri_conditioned_quantitative_residual_query_lists_at:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and lengths: "length challenges = length roots"
    and i_bound: "i < length challenges"
  shows
    "card
      (fri_conditioned_quantitative_residual_query_lists_at d roots challenges
        final_value prefix_state i) \<le>
      (modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
proof (cases
    "challenges ! i \<notin>
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
            final_value ! Suc i))")
  case False
  then have empty:
      "fri_conditioned_quantitative_residual_query_lists_at d roots challenges
        final_value prefix_state i = {}"
    unfolding fri_conditioned_quantitative_residual_query_lists_at_def
    by auto
  show ?thesis unfolding empty by simp
next
  case True
  let ?layers =
    "fri_builder_conceptual_layers roots prefix_state final_value"
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
      (use round_count rounds_le current_cover next_cover True i_bound
        in simp_all)
  have modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
    by (rule fri_canonical_domain_at_pos[OF eval_power])
      (use round_count rounds_le i_bound in simp)
  have residual_card:
      "card
        (fri_conditioned_residual_query_lists roots challenges ?layers i \<inter>
          fri_query_index_list_space) \<le>
        (modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i)))
          (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
    by (rule card_fri_conditioned_residual_restricted[
        OF eval_power root_le root_i agreement_card modulus_pos])
  have set_eq:
      "fri_conditioned_quantitative_residual_query_lists_at d roots challenges
          final_value prefix_state i =
        fri_conditioned_residual_query_lists roots challenges ?layers i \<inter>
          fri_query_index_list_space"
    using True
    unfolding fri_conditioned_quantitative_residual_query_lists_at_def
    by auto
  show ?thesis
    unfolding set_eq
    by (rule residual_card)
qed


definition fri_conditioned_residual_query_list_card_bound :: "nat \<Rightarrow> nat"
where
  "fri_conditioned_residual_query_list_card_bound d =
    (\<Sum>i < ceil_log (Suc d).
      (modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds)"

lemma card_fri_conditioned_quantitative_residual_query_lists:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "card
      (fri_conditioned_quantitative_residual_query_lists d roots challenges
        final_value prefix_state) \<le>
      fri_conditioned_residual_query_list_card_bound d"
proof -
  let ?S =
    "\<lambda>i. fri_conditioned_quantitative_residual_query_lists_at d roots
      challenges final_value prefix_state i"
  have finite_each: "\<And>i. finite (?S i)"
    unfolding fri_conditioned_quantitative_residual_query_lists_at_def
    by (rule finite_subset[OF _ finite_fri_query_index_list_space]) auto
  have union_card:
      "card (\<Union>i < length challenges. ?S i) \<le>
        (\<Sum>i < length challenges. card (?S i))"
    by (rule card_UN_le) (simp add: finite_each)
  have local:
      "\<And>i. i < length challenges \<Longrightarrow>
        card (?S i) \<le>
          (modulo_preimage_card_envelope query_sample_space_size
            (length (fri_canonical_domain_at (Suc i)))
            (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
    by (rule card_fri_conditioned_quantitative_residual_query_lists_at[
        OF eval_power round_count rounds_le lengths])
  have sum_bound:
      "(\<Sum>i < length challenges. card (?S i)) \<le>
        (\<Sum>i < length challenges.
          (modulo_preimage_card_envelope query_sample_space_size
            (length (fri_canonical_domain_at (Suc i)))
            (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds)"
  proof (rule sum_mono)
    fix i
    assume i_mem: "i \<in> {..<length challenges}"
    have i_bound: "i < length challenges"
      using i_mem by simp
    show
        "card (?S i) \<le>
          (modulo_preimage_card_envelope query_sample_space_size
            (length (fri_canonical_domain_at (Suc i)))
            (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
      by (rule local[OF i_bound])
  qed
  have combined:
      "card (\<Union>i < length challenges. ?S i) \<le>
        (\<Sum>i < length challenges.
          (modulo_preimage_card_envelope query_sample_space_size
            (length (fri_canonical_domain_at (Suc i)))
            (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds)"
    by (rule order_trans[OF union_card sum_bound])
  show ?thesis
    using combined round_count
    unfolding fri_conditioned_quantitative_residual_query_lists_union
      fri_conditioned_residual_query_list_card_bound_def
    by simp
qed

lemma fri_conditioned_quantitative_residual_query_lists_not_full:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and lengths: "length challenges = length roots"
    and strict:
      "fri_conditioned_residual_query_list_card_bound d <
        query_sample_space_size ^ rounds"
  shows
    "fri_conditioned_quantitative_residual_query_lists d roots challenges
      final_value prefix_state \<noteq> fri_query_index_list_space"
proof
  assume equality:
      "fri_conditioned_quantitative_residual_query_lists d roots challenges
        final_value prefix_state = fri_query_index_list_space"
  have card_le:
      "card
        (fri_conditioned_quantitative_residual_query_lists d roots challenges
          final_value prefix_state) \<le>
        fri_conditioned_residual_query_list_card_bound d"
    by (rule card_fri_conditioned_quantitative_residual_query_lists[
        OF eval_power round_count rounds_le lengths])
  have full_card:
      "card fri_query_index_list_space = query_sample_space_size ^ rounds"
    using card_fri_query_index_list_space
    unfolding card_query_sample_space by simp
  show False
    using card_le strict equality full_card by simp
qed

definition query_list_value_union :: "nat list set \<Rightarrow> nat set"
where
  "query_list_value_union Q = (\<Union>qs \<in> Q. set qs)"

lemma query_list_value_union_subset:
  assumes subset: "Q \<subseteq> fri_query_index_list_space"
  shows "query_list_value_union Q \<subseteq> query_sample_space"
  using subset
  unfolding query_list_value_union_def fri_query_index_list_space_def
  by auto

lemma card_query_list_value_union:
  assumes subset: "Q \<subseteq> fri_query_index_list_space"
  shows "card (query_list_value_union Q) \<le> rounds * card Q"
proof -
  have finite_Q: "finite Q"
    by (rule finite_subset[OF subset finite_fri_query_index_list_space])
  have union_card:
      "card (\<Union>qs \<in> Q. set qs) \<le> (\<Sum>qs \<in> Q. card (set qs))"
    by (rule card_UN_le) (use finite_Q in simp_all)
  have each:
      "\<And>qs. qs \<in> Q \<Longrightarrow> card (set qs) \<le> rounds"
  proof -
    fix qs
    assume "qs \<in> Q"
    then have "length qs = rounds"
      using subset
      unfolding fri_query_index_list_space_def by auto
    have "card (set qs) \<le> length qs"
      by (rule card_length)
    also have "... = rounds"
      by (rule \<open>length qs = rounds\<close>)
    finally show "card (set qs) \<le> rounds" .
  qed
  have sum_bound:
      "(\<Sum>qs \<in> Q. card (set qs)) \<le> (\<Sum>qs \<in> Q. rounds)"
    by (rule sum_mono) (auto intro: each)
  show ?thesis
    unfolding query_list_value_union_def
    using order_trans[OF union_card sum_bound] finite_Q
    by (simp add: mult.commute)
qed

lemma query_index_raw_list_position_values_subset_union:
  assumes subset: "Q \<subseteq> fri_query_index_list_space"
    and i_bound: "i < rounds"
  shows
    "query_index_raw_list_position_values Q i \<subseteq>
      query_index_raw_preimage (query_list_value_union Q)"
proof
  fix raw
  assume raw_in: "raw \<in> query_index_raw_list_position_values Q i"
  then obtain raws where raws_in:
      "raws \<in> query_index_raw_list_preimage Q"
    and raw_eq: "raw = raws ! i"
    unfolding query_index_raw_list_position_values_def
    using i_bound by blast
  have raws_len: "length raws = rounds"
    and mapped_in: "map (\<lambda>x. index (to_nat x)) raws \<in> Q"
    using raws_in
    unfolding query_index_raw_list_preimage_def by blast+
  have i_len: "i < length raws"
    using i_bound raws_len by simp
  have mapped_nth:
      "map (\<lambda>x. index (to_nat x)) raws ! i = index (to_nat raw)"
    using raw_eq i_len by simp
  have mapped_mem:
      "map (\<lambda>x. index (to_nat x)) raws ! i \<in>
        set (map (\<lambda>x. index (to_nat x)) raws)"
    by (rule nth_mem) (use i_len in simp)
  have index_mem:
      "index (to_nat raw) \<in> set (map (\<lambda>x. index (to_nat x)) raws)"
    using mapped_mem mapped_nth by simp
  have index_union:
      "index (to_nat raw) \<in> query_list_value_union Q"
    unfolding query_list_value_union_def
    apply (rule UN_I)
     apply (rule mapped_in)
    by (rule index_mem)
  show "raw \<in> query_index_raw_preimage (query_list_value_union Q)"
    using index_union
    unfolding query_index_raw_preimage_def by simp
qed

lemma query_index_raw_list_relation_fiber_bound_by_card:
  assumes subset: "Q \<subseteq> fri_query_index_list_space"
    and card_bound: "card Q \<le> K"
  shows
    "query_index_raw_list_relation_fiber_bound Q \<le>
      rounds *
        query_raw_preimage_card_envelope (rounds * K)"
proof -
  let ?I = "query_list_value_union Q"
  have I_subset: "?I \<subseteq> query_sample_space"
    by (rule query_list_value_union_subset[OF subset])
  have scaled: "rounds * card Q \<le> rounds * K"
    using card_bound by simp
  have I_card: "card ?I \<le> rounds * K"
    by (rule order_trans[
        OF card_query_list_value_union[OF subset] scaled])
  have raw_card:
      "card (query_index_raw_preimage ?I) \<le>
        query_raw_preimage_card_envelope (rounds * K)"
  proof -
    have base:
        "card (query_index_raw_preimage ?I) \<le>
          query_raw_preimage_card_envelope (card ?I)"
      by (rule card_query_index_raw_preimage_le_query_envelope[OF I_subset])
    have mono:
        "query_raw_preimage_card_envelope (card ?I) \<le>
          query_raw_preimage_card_envelope (rounds * K)"
      by (rule query_raw_preimage_card_envelope_mono[OF I_card])
    show ?thesis
      by (rule order_trans[OF base mono])
  qed
  have per_position:
      "\<And>i. i < rounds \<Longrightarrow>
        card (query_index_raw_list_position_values Q i) \<le>
          query_raw_preimage_card_envelope (rounds * K)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have position_subset:
        "query_index_raw_list_position_values Q i \<subseteq>
          query_index_raw_preimage ?I"
      by (rule query_index_raw_list_position_values_subset_union[
        OF subset i_bound])
    have card_le:
        "card (query_index_raw_list_position_values Q i) \<le>
          card (query_index_raw_preimage ?I)"
      by (rule card_mono[OF _ position_subset]) simp
    show
        "card (query_index_raw_list_position_values Q i) \<le>
          query_raw_preimage_card_envelope (rounds * K)"
      by (rule order_trans[OF card_le raw_card])
  qed
  have sum_bound:
      "(\<Sum>i < rounds. card (query_index_raw_list_position_values Q i)) \<le>
        (\<Sum>i < rounds.
          query_raw_preimage_card_envelope (rounds * K))"
    by (rule sum_mono) (auto intro: per_position)
  show ?thesis
    unfolding query_index_raw_list_relation_fiber_bound_def
    using sum_bound by simp
qed

lemma fri_conditioned_quantitative_residual_query_lists_subset:
  "fri_conditioned_quantitative_residual_query_lists d roots challenges
      final_value prefix_state \<subseteq> fri_query_index_list_space"
  unfolding fri_conditioned_quantitative_residual_query_lists_def by auto

lemma finite_fri_conditioned_quantitative_residual_query_lists[simp]:
  "finite
    (fri_conditioned_quantitative_residual_query_lists d roots challenges
      final_value prefix_state)"
  by (rule finite_subset[
      OF fri_conditioned_quantitative_residual_query_lists_subset
        finite_fri_query_index_list_space])

lemma
  fri_conditioned_quantitative_residual_query_lists_relation_fiber_bound:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_count: "length challenges = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and lengths: "length challenges = length roots"
  shows
    "query_index_raw_list_relation_fiber_bound
      (fri_conditioned_quantitative_residual_query_lists d roots challenges
        final_value prefix_state) \<le>
      rounds *
        query_raw_preimage_card_envelope
          (rounds * fri_conditioned_residual_query_list_card_bound d)"
proof (rule query_index_raw_list_relation_fiber_bound_by_card)
  show
      "fri_conditioned_quantitative_residual_query_lists d roots challenges
        final_value prefix_state \<subseteq> fri_query_index_list_space"
    by (rule fri_conditioned_quantitative_residual_query_lists_subset)
  show
      "card
        (fri_conditioned_quantitative_residual_query_lists d roots challenges
          final_value prefix_state) \<le>
        fri_conditioned_residual_query_list_card_bound d"
    by (rule card_fri_conditioned_quantitative_residual_query_lists[
        OF eval_power round_count rounds_le lengths])
qed

end

end
