(*  Title:      Stark/Soundness_Conceptual_Query_Target.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Conceptual_Query_Target
  imports
    Soundness_Conceptual_Query_Prefix
    Soundness_Aligned_Partial_Query_Prefix
begin

text \<open>
  Prefix-fixed query targets built from conceptual Merkle tables.

  This layer deliberately uses only the query-prefix state.  It therefore
  supports the dynamic query-index probability bound, but it does not claim
  that openings first authenticated after the query challenge agree with these
  tables.  That later-opening bridge is a separate proof obligation.
\<close>

context soundness
begin

definition staged_query_prefix_conceptual_query_target
  :: "'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "staged_query_prefix_conceptual_query_target prefix prefix_state =
    query_sampling_success_space
      (query_prefix_trace_conceptual_table prefix prefix_state)
      (query_prefix_composition_conceptual_table prefix prefix_state)
      (sqp_alphas prefix)"

definition staged_query_prefix_conceptual_default_query_target
  :: "'f list \<Rightarrow> 'f list \<Rightarrow>
      'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "staged_query_prefix_conceptual_default_query_target trace_default
      composition_default prefix prefix_state =
    query_sampling_success_space
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default)
      (query_prefix_composition_conceptual_table_with_default prefix
        prefix_state composition_default)
      (sqp_alphas prefix)"

definition staged_query_prefix_conceptual_empty_query_target
  :: "'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "staged_query_prefix_conceptual_empty_query_target prefix prefix_state =
    query_sampling_success_space
      (query_prefix_trace_conceptual_table prefix prefix_state)
      (replicate (scale * clength) (sqp_composition_final prefix))
      (sqp_alphas prefix)"

lemma staged_query_prefix_conceptual_query_target_subset:
  "staged_query_prefix_conceptual_query_target prefix prefix_state \<subseteq>
    query_sample_space"
  unfolding staged_query_prefix_conceptual_query_target_def
  by (rule query_sampling_success_space_subset)

lemma staged_query_prefix_conceptual_default_query_target_subset:
  "staged_query_prefix_conceptual_default_query_target trace_default
      composition_default prefix prefix_state \<subseteq>
    query_sample_space"
  unfolding staged_query_prefix_conceptual_default_query_target_def
  by (rule query_sampling_success_space_subset)

lemma staged_query_prefix_conceptual_empty_query_target_subset:
  "staged_query_prefix_conceptual_empty_query_target prefix prefix_state
    \<subseteq> query_sample_space"
  unfolding staged_query_prefix_conceptual_empty_query_target_def
  by (rule query_sampling_success_space_subset)

lemma staged_query_prefix_conceptual_query_target_fraction_bound:
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (staged_query_prefix_conceptual_query_target prefix prefix_state))) /
      nnreal size \<le> query_error_bound"
  unfolding staged_query_prefix_conceptual_query_target_def
  by (rule query_sampling_success_space_envelope_fraction_bound)

lemma staged_query_prefix_conceptual_default_query_target_fraction_bound:
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (staged_query_prefix_conceptual_default_query_target trace_default
            composition_default prefix prefix_state))) /
      nnreal size \<le> query_error_bound"
  unfolding staged_query_prefix_conceptual_default_query_target_def
  by (rule query_sampling_success_space_envelope_fraction_bound)

lemma staged_query_prefix_conceptual_empty_query_target_fraction_bound:
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (staged_query_prefix_conceptual_empty_query_target prefix
            prefix_state))) /
      nnreal size \<le> query_error_bound"
  unfolding staged_query_prefix_conceptual_empty_query_target_def
  by (rule query_sampling_success_space_envelope_fraction_bound)

lemma query_prefix_trace_conceptual_table_with_default_eq_if_agrees:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
    and len: "length trace_default = scale * clength"
    and agrees:
      "\<And>i v. i < scale * clength \<Longrightarrow>
        authenticated_value_at prefix_state (sqp_trace_root prefix)
          (scale * clength) i v \<Longrightarrow>
        trace_default ! i = v"
  shows
    "query_prefix_trace_conceptual_table_with_default prefix prefix_state
      trace_default = trace_default"
  unfolding query_prefix_trace_conceptual_table_with_default_def
  by (rule conceptual_table_with_default_eq_if_agrees_with_authenticated_values
      [OF clean len agrees])

lemma query_prefix_composition_conceptual_table_with_default_eq_if_agrees:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
    and len: "length composition_default = scale * clength"
    and agrees:
      "\<And>i v. i < scale * clength \<Longrightarrow>
        authenticated_value_at prefix_state
          (hd (sqp_composition_fri_roots prefix)) (scale * clength) i v \<Longrightarrow>
        composition_default ! i = v"
  shows
    "query_prefix_composition_conceptual_table_with_default prefix
      prefix_state composition_default = composition_default"
  unfolding query_prefix_composition_conceptual_table_with_default_def
  by (rule conceptual_table_with_default_eq_if_agrees_with_authenticated_values
      [OF clean len agrees])

lemma
  staged_query_prefix_candidate_pair_query_target_from_prefix_subset_conceptual_default_if_agrees:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
    and trace_len: "length trace_table = scale * clength"
    and composition_len: "length composition_table = scale * clength"
    and trace_agrees:
      "\<And>i v. i < scale * clength \<Longrightarrow>
        authenticated_value_at prefix_state (sqp_trace_root prefix)
          (scale * clength) i v \<Longrightarrow>
        trace_table ! i = v"
    and composition_agrees:
      "\<And>i v. i < scale * clength \<Longrightarrow>
        authenticated_value_at prefix_state
          (hd (sqp_composition_fri_roots prefix)) (scale * clength) i v \<Longrightarrow>
        composition_table ! i = v"
  shows
    "staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
      composition_table prefix prefix_state \<subseteq>
     staged_query_prefix_conceptual_default_query_target trace_table
      composition_table prefix prefix_state"
proof -
  have trace_eq:
    "query_prefix_trace_conceptual_table_with_default prefix prefix_state
      trace_table = trace_table"
    by (rule query_prefix_trace_conceptual_table_with_default_eq_if_agrees
        [OF clean trace_len trace_agrees])
  have composition_eq:
    "query_prefix_composition_conceptual_table_with_default prefix
      prefix_state composition_table = composition_table"
    by (rule
        query_prefix_composition_conceptual_table_with_default_eq_if_agrees
        [OF clean composition_len composition_agrees])
  show ?thesis
    unfolding staged_query_prefix_candidate_pair_query_target_from_prefix_def
      staged_query_prefix_conceptual_default_query_target_def
    using trace_eq composition_eq by simp
qed

definition query_prefix_trace_default_agrees_with_authenticated_values
  :: "'f list \<Rightarrow> 'f staged_query_prefix_data \<Rightarrow>
      'f protocol_channel \<Rightarrow> bool"
where
  "query_prefix_trace_default_agrees_with_authenticated_values trace_default
      prefix prefix_state \<longleftrightarrow>
    (\<forall>i v. i < scale * clength \<longrightarrow>
      authenticated_value_at prefix_state (sqp_trace_root prefix)
        (scale * clength) i v \<longrightarrow>
      trace_default ! i = v)"

definition query_prefix_composition_default_agrees_with_authenticated_values
  :: "'f list \<Rightarrow> 'f staged_query_prefix_data \<Rightarrow>
      'f protocol_channel \<Rightarrow> bool"
where
  "query_prefix_composition_default_agrees_with_authenticated_values
      composition_default prefix prefix_state \<longleftrightarrow>
    (\<forall>i v. i < scale * clength \<longrightarrow>
      authenticated_value_at prefix_state
        (hd (sqp_composition_fri_roots prefix)) (scale * clength) i v \<longrightarrow>
      composition_default ! i = v)"

definition query_prefix_candidate_defaults_agree_with_authenticated_values
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f staged_query_prefix_data \<Rightarrow>
      'f protocol_channel \<Rightarrow> bool"
where
  "query_prefix_candidate_defaults_agree_with_authenticated_values
      trace_default composition_default prefix prefix_state \<longleftrightarrow>
    query_prefix_trace_default_agrees_with_authenticated_values trace_default
      prefix prefix_state \<and>
    query_prefix_composition_default_agrees_with_authenticated_values
      composition_default prefix prefix_state"

lemma query_prefix_trace_default_agrees_with_authenticated_valuesD:
  assumes
    "query_prefix_trace_default_agrees_with_authenticated_values trace_default
      prefix prefix_state"
    and "i < scale * clength"
    and
      "authenticated_value_at prefix_state (sqp_trace_root prefix)
        (scale * clength) i v"
  shows "trace_default ! i = v"
  using assms
  unfolding query_prefix_trace_default_agrees_with_authenticated_values_def
  by blast

lemma query_prefix_composition_default_agrees_with_authenticated_valuesD:
  assumes
    "query_prefix_composition_default_agrees_with_authenticated_values
      composition_default prefix prefix_state"
    and "i < scale * clength"
    and
      "authenticated_value_at prefix_state
        (hd (sqp_composition_fri_roots prefix)) (scale * clength) i v"
  shows "composition_default ! i = v"
  using assms
  unfolding
    query_prefix_composition_default_agrees_with_authenticated_values_def
  by blast

lemma
  staged_query_prefix_candidate_pair_query_target_from_prefix_subset_conceptual_default_if_prefix_agrees:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
    and trace_len: "length trace_table = scale * clength"
    and composition_len: "length composition_table = scale * clength"
    and agrees:
      "query_prefix_candidate_defaults_agree_with_authenticated_values
        trace_table composition_table prefix prefix_state"
  shows
    "staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
      composition_table prefix prefix_state \<subseteq>
     staged_query_prefix_conceptual_default_query_target trace_table
      composition_table prefix prefix_state"
proof (rule
    staged_query_prefix_candidate_pair_query_target_from_prefix_subset_conceptual_default_if_agrees
    [OF clean trace_len composition_len])
  fix i v
  assume i_bound: "i < scale * clength"
    and auth:
      "authenticated_value_at prefix_state (sqp_trace_root prefix)
        (scale * clength) i v"
  have trace_agrees:
    "query_prefix_trace_default_agrees_with_authenticated_values trace_table
      prefix prefix_state"
    using agrees
    unfolding
      query_prefix_candidate_defaults_agree_with_authenticated_values_def
    by simp
  show "trace_table ! i = v"
    by (rule
        query_prefix_trace_default_agrees_with_authenticated_valuesD
        [OF trace_agrees i_bound auth])
next
  fix i v
  assume i_bound: "i < scale * clength"
    and auth:
      "authenticated_value_at prefix_state
        (hd (sqp_composition_fri_roots prefix)) (scale * clength) i v"
  have composition_agrees:
    "query_prefix_composition_default_agrees_with_authenticated_values
      composition_table prefix prefix_state"
    using agrees
    unfolding
      query_prefix_candidate_defaults_agree_with_authenticated_values_def
    by simp
  show "composition_table ! i = v"
    by (rule
        query_prefix_composition_default_agrees_with_authenticated_valuesD
        [OF composition_agrees i_bound auth])
qed

definition query_prefix_candidate_defaults_agree_at_query
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> bool"
where
  "query_prefix_candidate_defaults_agree_at_query trace_table
      composition_table idx prefix prefix_state \<longleftrightarrow>
    (\<forall>j \<in> set (powers_scaled idx).
      query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_table ! j = trace_table ! j) \<and>
    query_prefix_composition_conceptual_table_with_default prefix prefix_state
      composition_table ! idx = composition_table ! idx"

lemma query_prefix_candidate_pair_query_hit_imp_conceptual_default_if_agrees_at_query:
  assumes hit:
      "idx \<in>
        staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
          composition_table prefix prefix_state"
    and trace_len: "length trace_table = scale * clength"
    and composition_len: "length composition_table = scale * clength"
    and agrees:
      "query_prefix_candidate_defaults_agree_at_query trace_table
        composition_table idx prefix prefix_state"
    and default_trace_low:
      "trace_table_low_degree
        (query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_table)"
    and default_composition_low:
      "composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_table)"
    and default_not_all:
      "\<not> all_queries_consistent
        (query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_table)
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_table)
        (sqp_alphas prefix)"
  shows
    "idx \<in>
      staged_query_prefix_conceptual_default_query_target trace_table
        composition_table prefix prefix_state"
proof -
  let ?trace_default =
    "query_prefix_trace_conceptual_table_with_default prefix prefix_state
      trace_table"
  let ?composition_default =
    "query_prefix_composition_conceptual_table_with_default prefix
      prefix_state composition_table"
  have trace_len_eq: "length trace_table = length ?trace_default"
    using trace_len by simp
  have composition_len_eq:
    "length composition_table = length ?composition_default"
    using composition_len by simp
  have trace_values:
    "map ((!) trace_table) (powers_scaled idx) =
      map ((!) ?trace_default) (powers_scaled idx)"
  proof (rule nth_equalityI)
    show
      "length (map ((!) trace_table) (powers_scaled idx)) =
       length (map ((!) ?trace_default) (powers_scaled idx))"
      by simp
  next
    fix k
    assume k_bound:
      "k < length (map ((!) trace_table) (powers_scaled idx))"
    then have ps_bound: "k < length (powers_scaled idx)"
      by simp
    have ps_mem: "powers_scaled idx ! k \<in> set (powers_scaled idx)"
      by (rule nth_mem[OF ps_bound])
    have eq:
      "?trace_default ! (powers_scaled idx ! k) =
        trace_table ! (powers_scaled idx ! k)"
      using agrees ps_mem
      unfolding query_prefix_candidate_defaults_agree_at_query_def
      by blast
    show
      "map ((!) trace_table) (powers_scaled idx) ! k =
       map ((!) ?trace_default) (powers_scaled idx) ! k"
      using ps_bound eq by simp
  qed
  have composition_value:
    "composition_table ! idx = ?composition_default ! idx"
    using agrees
    unfolding query_prefix_candidate_defaults_agree_at_query_def
    by simp
  have qc_iff:
    "query_consistent_at trace_table composition_table (sqp_alphas prefix)
        idx \<longleftrightarrow>
     query_consistent_at ?trace_default ?composition_default
        (sqp_alphas prefix) idx"
    by (rule query_consistent_at_cong_opened_values
        [OF trace_len_eq composition_len_eq trace_values composition_value])
  have qc:
    "query_consistent_at trace_table composition_table (sqp_alphas prefix)
      idx"
    using hit
    unfolding staged_query_prefix_candidate_pair_query_target_from_prefix_def
      query_sampling_success_space_def query_agreement_indices_def
    by (cases
        "trace_table_low_degree trace_table \<and>
          composition_table_low_degree maxDegree composition_table \<and>
          \<not> all_queries_consistent trace_table composition_table
            (sqp_alphas prefix)")
      auto
  have query_idx: "idx \<in> query_sample_space"
    using hit query_sampling_success_space_subset
    unfolding staged_query_prefix_candidate_pair_query_target_from_prefix_def
    by blast
  have default_qc:
    "query_consistent_at ?trace_default ?composition_default
      (sqp_alphas prefix) idx"
    using qc qc_iff by simp
  show ?thesis
    using query_idx default_qc default_trace_low default_composition_low
      default_not_all
    unfolding staged_query_prefix_candidate_pair_query_target_from_prefix_def
      staged_query_prefix_conceptual_default_query_target_def
      query_sampling_success_space_def query_agreement_indices_def
    by auto
qed

lemma query_prefix_candidate_defaults_agree_at_query_from_prefix_authenticated_openings:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
    and i_bound: "i < rounds"
    and trace_prefix:
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) trace_openings prefix_state"
    and composition_prefix:
      "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) composition_openings prefix_state"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (sqp_alphas prefix) idx"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and composition_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
  shows
    "query_prefix_candidate_defaults_agree_at_query trace_table
      composition_table idx prefix prefix_state"
proof -
  let ?trace_openingss = "(replicate rounds []) [i := trace_openings]"
  let ?composition_openingss =
    "(replicate rounds []) [i := composition_openings]"
  have trace_agrees:
    "table_agrees_with_authenticated_openings trace_table
      (scale * clength) trace_openings"
  proof -
    have all:
      "\<forall>ia<rounds.
        table_agrees_with_authenticated_openings trace_table
          (scale * clength) (?trace_openingss ! ia)"
      using trace_candidate
      unfolding partial_trace_table_candidate_def by blast
    have at_i:
      "table_agrees_with_authenticated_openings trace_table
        (scale * clength) (?trace_openingss ! i)"
      using all i_bound by blast
    have "?trace_openingss ! i = trace_openings"
      using i_bound by simp
    then show ?thesis
      using at_i by simp
  qed
  have composition_agrees:
    "table_agrees_with_authenticated_openings composition_table
      (scale * clength) composition_openings"
  proof -
    have all:
      "\<forall>ia<rounds.
        table_agrees_with_authenticated_openings composition_table
          (scale * clength) (?composition_openingss ! ia)"
      using composition_candidate
      unfolding partial_composition_table_candidate_def by blast
    have at_i:
      "table_agrees_with_authenticated_openings composition_table
        (scale * clength) (?composition_openingss ! i)"
      using all i_bound by blast
    have "?composition_openingss ! i = composition_openings"
      using i_bound by simp
    then show ?thesis
      using at_i by simp
  qed
  have trace_indices:
    "map opening_index trace_openings = powers_scaled idx"
    using consistent unfolding partial_query_openings_consistent_def by simp
  have composition_indices:
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    using consistent unfolding partial_query_openings_consistent_def by simp
  have composition_nonempty: "composition_openings \<noteq> []"
    using consistent unfolding partial_query_openings_consistent_def by simp
  have trace_point:
    "\<And>j. j \<in> set (powers_scaled idx) \<Longrightarrow>
      query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_table ! j =
      trace_table ! j"
  proof -
    fix j
    assume j_in: "j \<in> set (powers_scaled idx)"
    then obtain opn where opn_in: "opn \<in> set trace_openings"
      and opn_idx: "opening_index opn = j"
      using trace_indices
      by (metis (mono_tags, lifting) in_set_conv_nth length_map nth_map)
    have conceptual:
      "query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_table ! opening_index opn =
       opening_value opn"
      by (rule
          query_prefix_trace_conceptual_table_with_default_agrees_with_partial_authenticated_table
          [OF clean trace_prefix opn_in])
    have table:
      "trace_table ! opening_index opn = opening_value opn"
      using trace_agrees opn_in
      unfolding table_agrees_with_authenticated_openings_def by blast
    show
      "query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_table ! j =
       trace_table ! j"
      using conceptual table opn_idx by simp
  qed
  have composition_point:
    "query_prefix_composition_conceptual_table_with_default prefix
      prefix_state composition_table ! idx =
     composition_table ! idx"
  proof -
    have opn0_in: "composition_openings ! 0 \<in> set composition_openings"
      using composition_nonempty by simp
    have opn0_idx: "opening_index (composition_openings ! 0) = idx"
      using composition_indices composition_nonempty
      by (cases composition_openings) simp_all
    have conceptual:
      "query_prefix_composition_conceptual_table_with_default prefix
        prefix_state composition_table ! opening_index (composition_openings ! 0) =
       opening_value (composition_openings ! 0)"
      by (rule
          query_prefix_composition_conceptual_table_with_default_agrees_with_partial_authenticated_table
          [OF clean composition_prefix opn0_in])
    have table:
      "composition_table ! opening_index (composition_openings ! 0) =
       opening_value (composition_openings ! 0)"
      using composition_agrees opn0_in
      unfolding table_agrees_with_authenticated_openings_def by blast
    show ?thesis
      using conceptual table opn0_idx by simp
  qed
  show ?thesis
    unfolding query_prefix_candidate_defaults_agree_at_query_def
    using trace_point composition_point by blast
qed

lemma query_prefix_current_openings_imp_conceptual_default_query_target:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
    and i_bound: "i < rounds"
    and trace_prefix:
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) trace_openings prefix_state"
    and composition_prefix:
      "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) composition_openings prefix_state"
    and consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        (sqp_alphas prefix) idx"
    and trace_candidate:
      "partial_trace_table_candidate trace_table
        ((replicate rounds []) [i := trace_openings])"
    and composition_candidate:
      "partial_composition_table_candidate composition_table
        ((replicate rounds []) [i := composition_openings])"
    and default_trace_low:
      "trace_table_low_degree
        (query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_table)"
    and default_composition_low:
      "composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_table)"
    and default_not_all:
      "\<not> all_queries_consistent
        (query_prefix_trace_conceptual_table_with_default prefix prefix_state
          trace_table)
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_table)
        (sqp_alphas prefix)"
  shows
    "idx \<in>
      staged_query_prefix_conceptual_default_query_target trace_table
        composition_table prefix prefix_state"
proof -
  let ?trace_openingss = "(replicate rounds []) [i := trace_openings]"
  let ?composition_openingss =
    "(replicate rounds []) [i := composition_openings]"
  let ?trace_default =
    "query_prefix_trace_conceptual_table_with_default prefix prefix_state
      trace_table"
  let ?composition_default =
    "query_prefix_composition_conceptual_table_with_default prefix
      prefix_state composition_table"
  have trace_len: "length trace_table = scale * clength"
    using trace_candidate unfolding partial_trace_table_candidate_def
    by simp
  have composition_len: "length composition_table = scale * clength"
    using composition_candidate
    unfolding partial_composition_table_candidate_def by simp
  have idx_sample: "idx \<in> query_sample_space"
    using consistent unfolding partial_query_openings_consistent_def by simp
  have round:
    "partial_query_round_consistent ?trace_openingss ?composition_openingss
      (sqp_alphas prefix) i idx"
    using i_bound consistent
    unfolding partial_query_round_consistent_def
      partial_query_openings_consistent_def
    by simp
  have candidate_consistent:
    "query_consistent_at trace_table composition_table (sqp_alphas prefix)
      idx"
    by (rule partial_query_round_consistent_imp_query_consistent_at
        [OF trace_candidate composition_candidate round])
  have agrees:
    "query_prefix_candidate_defaults_agree_at_query trace_table
      composition_table idx prefix prefix_state"
    by (rule
        query_prefix_candidate_defaults_agree_at_query_from_prefix_authenticated_openings
        [OF clean i_bound trace_prefix composition_prefix consistent
          trace_candidate composition_candidate])
  have trace_len_eq: "length trace_table = length ?trace_default"
    using trace_len by simp
  have composition_len_eq:
    "length composition_table = length ?composition_default"
    using composition_len by simp
  have trace_values_eq:
    "map ((!) trace_table) (powers_scaled idx) =
      map ((!) ?trace_default) (powers_scaled idx)"
  proof (rule nth_equalityI)
    show
      "length (map ((!) trace_table) (powers_scaled idx)) =
       length (map ((!) ?trace_default) (powers_scaled idx))"
      by simp
  next
    fix k
    assume k_bound:
      "k < length (map ((!) trace_table) (powers_scaled idx))"
    then have ps_bound: "k < length (powers_scaled idx)"
      by simp
    have ps_mem: "powers_scaled idx ! k \<in> set (powers_scaled idx)"
      by (rule nth_mem[OF ps_bound])
    have eq:
      "?trace_default ! (powers_scaled idx ! k) =
        trace_table ! (powers_scaled idx ! k)"
      using agrees ps_mem
      unfolding query_prefix_candidate_defaults_agree_at_query_def
      by blast
    show
      "map ((!) trace_table) (powers_scaled idx) ! k =
       map ((!) ?trace_default) (powers_scaled idx) ! k"
      using ps_bound eq by simp
  qed
  have composition_value_eq:
    "composition_table ! idx = ?composition_default ! idx"
    using agrees
    unfolding query_prefix_candidate_defaults_agree_at_query_def by simp
  have qc_iff:
    "query_consistent_at trace_table composition_table (sqp_alphas prefix)
        idx \<longleftrightarrow>
     query_consistent_at ?trace_default ?composition_default
        (sqp_alphas prefix) idx"
    by (rule query_consistent_at_cong_opened_values
        [OF trace_len_eq composition_len_eq trace_values_eq
          composition_value_eq])
  have default_consistent:
    "query_consistent_at ?trace_default ?composition_default
      (sqp_alphas prefix) idx"
    using candidate_consistent qc_iff by simp
  show ?thesis
    unfolding staged_query_prefix_conceptual_default_query_target_def
      query_sampling_success_space_def query_agreement_indices_def
    using idx_sample default_consistent default_trace_low
      default_composition_low default_not_all by simp
qed

lemma trace_table_agrees_with_prefix_authenticated_values_if_final_merkle_bound:
  assumes ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision final_state"
    and bind:
      "merkle_root_binds_table (sqp_trace_root prefix) trace_table
        final_state"
    and len: "length trace_table = scale * clength"
    and i_bound: "i < scale * clength"
    and auth:
      "authenticated_value_at prefix_state (sqp_trace_root prefix)
        (scale * clength) i v"
  shows "trace_table ! i = v"
proof -
  from authenticated_value_atE[OF auth] obtain opn where
    opn_auth_prefix: "authenticated_opening_in prefix_state opn"
    and root: "opening_root opn = sqp_trace_root prefix"
    and opn_len: "opening_length opn = scale * clength"
    and idx: "opening_index opn = i"
    and val: "opening_value opn = v"
    by blast
  have opn_auth_final: "authenticated_opening_in final_state opn"
    by (rule authenticated_opening_in_mono[OF opn_auth_prefix ext])
  obtain n where len_pow: "length trace_table = 2 ^ n"
    using len eval_domain_length_power by (metis mult.commute)
  have agrees:
    "opening_index opn < length trace_table \<and>
      trace_table ! opening_index opn = opening_value opn"
    by (rule merkle_bound_table_agrees_with_authenticated_opening_if_clean
        [OF bind len_pow opn_auth_final root _ clean])
      (use len opn_len in simp)
  then show ?thesis
    using idx val by simp
qed

lemma composition_table_agrees_with_prefix_authenticated_values_if_final_merkle_bound:
  assumes ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision final_state"
    and bind:
      "merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
        composition_table final_state"
    and len: "length composition_table = scale * clength"
    and i_bound: "i < scale * clength"
    and auth:
      "authenticated_value_at prefix_state
        (hd (sqp_composition_fri_roots prefix)) (scale * clength) i v"
  shows "composition_table ! i = v"
proof -
  from authenticated_value_atE[OF auth] obtain opn where
    opn_auth_prefix: "authenticated_opening_in prefix_state opn"
    and root:
      "opening_root opn = hd (sqp_composition_fri_roots prefix)"
    and opn_len: "opening_length opn = scale * clength"
    and idx: "opening_index opn = i"
    and val: "opening_value opn = v"
    by blast
  have opn_auth_final: "authenticated_opening_in final_state opn"
    by (rule authenticated_opening_in_mono[OF opn_auth_prefix ext])
  obtain n where len_pow: "length composition_table = 2 ^ n"
    using len eval_domain_length_power by (metis mult.commute)
  have agrees:
    "opening_index opn < length composition_table \<and>
      composition_table ! opening_index opn = opening_value opn"
    by (rule merkle_bound_table_agrees_with_authenticated_opening_if_clean
        [OF bind len_pow opn_auth_final root _ clean])
      (use len opn_len in simp)
  then show ?thesis
    using idx val by simp
qed

lemma
  staged_query_prefix_candidate_pair_query_target_from_prefix_subset_conceptual_default_if_final_merkle_bound:
  assumes prefix_clean: "\<not> hash_map_output_collision prefix_state"
    and final_clean: "\<not> hash_map_output_collision final_state"
    and ext: "prefix_state \<le> final_state"
    and trace_bind:
      "merkle_root_binds_table (sqp_trace_root prefix) trace_table
        final_state"
    and composition_bind:
      "merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
        composition_table final_state"
    and trace_len: "length trace_table = scale * clength"
    and composition_len: "length composition_table = scale * clength"
  shows
    "staged_query_prefix_candidate_pair_query_target_from_prefix trace_table
      composition_table prefix prefix_state \<subseteq>
     staged_query_prefix_conceptual_default_query_target trace_table
      composition_table prefix prefix_state"
proof (rule
    staged_query_prefix_candidate_pair_query_target_from_prefix_subset_conceptual_default_if_agrees
    [OF prefix_clean trace_len composition_len])
  fix i v
  assume i_bound: "i < scale * clength"
    and auth:
      "authenticated_value_at prefix_state (sqp_trace_root prefix)
        (scale * clength) i v"
  show "trace_table ! i = v"
    by (rule
        trace_table_agrees_with_prefix_authenticated_values_if_final_merkle_bound
        [OF ext final_clean trace_bind trace_len i_bound auth])
next
  fix i v
  assume i_bound: "i < scale * clength"
    and auth:
      "authenticated_value_at prefix_state
        (hd (sqp_composition_fri_roots prefix)) (scale * clength) i v"
  show "composition_table ! i = v"
    by (rule
        composition_table_agrees_with_prefix_authenticated_values_if_final_merkle_bound
        [OF ext final_clean composition_bind composition_len i_bound auth])
qed

lemma
  staged_query_prefix_candidate_opening_query_target_from_prefix_subset_conceptual:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
    and trace_len: "length trace_openings = rounds"
    and composition_len: "length composition_openings = rounds"
    and trace_tables:
      "\<And>j. j < rounds \<Longrightarrow>
        partial_authenticated_table (sqp_trace_root prefix)
          (scale * clength) (trace_openings ! j) prefix_state"
    and composition_tables:
      "\<And>j. j < rounds \<Longrightarrow>
        partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
          (scale * clength) (composition_openings ! j) prefix_state"
    and trace_low:
      "trace_table_low_degree
        (query_prefix_trace_conceptual_table prefix prefix_state)"
    and composition_low:
      "composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table prefix prefix_state)"
    and not_all:
      "\<not> all_queries_consistent
        (query_prefix_trace_conceptual_table prefix prefix_state)
        (query_prefix_composition_conceptual_table prefix prefix_state)
        (sqp_alphas prefix)"
  shows
    "staged_query_prefix_candidate_opening_query_target_from_prefix
      trace_openings composition_openings i prefix prefix_state \<subseteq>
     staged_query_prefix_conceptual_query_target prefix prefix_state"
proof -
  have trace_candidate:
    "partial_trace_table_candidate
      (query_prefix_trace_conceptual_table prefix prefix_state)
      trace_openings"
    by (rule query_prefix_trace_conceptual_table_partial_trace_candidate
        [OF clean trace_len trace_tables])
  have composition_candidate:
    "partial_composition_table_candidate
      (query_prefix_composition_conceptual_table prefix prefix_state)
      composition_openings"
    by (rule
        query_prefix_composition_conceptual_table_partial_composition_candidate
        [OF clean composition_len composition_tables])
  show ?thesis
    unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
      staged_query_prefix_conceptual_query_target_def
    by (rule partial_query_success_indices_at_subset_query_sampling_success_space
        [OF trace_candidate composition_candidate trace_low composition_low
          not_all])
qed

lemma
  staged_query_prefix_candidate_opening_query_target_from_prefix_subset_conceptual_default:
  assumes clean: "\<not> hash_map_output_collision prefix_state"
    and trace_len: "length trace_openings = rounds"
    and composition_len: "length composition_openings = rounds"
    and trace_tables:
      "\<And>j. j < rounds \<Longrightarrow>
        partial_authenticated_table (sqp_trace_root prefix)
          (scale * clength) (trace_openings ! j) prefix_state"
    and composition_tables:
      "\<And>j. j < rounds \<Longrightarrow>
        partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
          (scale * clength) (composition_openings ! j) prefix_state"
    and trace_low:
      "trace_table_low_degree
        (query_prefix_trace_conceptual_table_with_default prefix
          prefix_state trace_default)"
    and composition_low:
      "composition_table_low_degree maxDegree
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default)"
    and not_all:
      "\<not> all_queries_consistent
        (query_prefix_trace_conceptual_table_with_default prefix
          prefix_state trace_default)
        (query_prefix_composition_conceptual_table_with_default prefix
          prefix_state composition_default)
        (sqp_alphas prefix)"
  shows
    "staged_query_prefix_candidate_opening_query_target_from_prefix
      trace_openings composition_openings i prefix prefix_state \<subseteq>
     staged_query_prefix_conceptual_default_query_target trace_default
      composition_default prefix prefix_state"
proof -
  have trace_candidate:
    "partial_trace_table_candidate
      (query_prefix_trace_conceptual_table_with_default prefix prefix_state
        trace_default)
      trace_openings"
    by (rule
        query_prefix_trace_conceptual_table_with_default_partial_trace_candidate
        [OF clean trace_len trace_tables])
  have composition_candidate:
    "partial_composition_table_candidate
      (query_prefix_composition_conceptual_table_with_default prefix
        prefix_state composition_default)
      composition_openings"
    by (rule
        query_prefix_composition_conceptual_table_with_default_partial_composition_candidate
        [OF clean composition_len composition_tables])
  show ?thesis
    unfolding staged_query_prefix_candidate_opening_query_target_from_prefix_def
      staged_query_prefix_conceptual_default_query_target_def
    by (rule partial_query_success_indices_at_subset_query_sampling_success_space
        [OF trace_candidate composition_candidate trace_low composition_low
          not_all])
qed

lemma checked_staged_query_prefix_conceptual_query_target_hit_bound:
  fixes C :: prob
  assumes raw_bound: "query_index_raw_preimage_bound"
    and prefix_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s) \<Longrightarrow>
        query_future_fresh prefix_state"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_conceptual_query_target) s \<le>
      query_error_bound"
proof (rule checked_staged_query_prefix_dynamic_index_hit_bound[OF raw_bound])
  fix prefix prefix_state
  assume support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i) s)"
  have future: "query_future_fresh prefix_state"
    by (rule prefix_bound[OF support])
  show
    "query_future_fresh prefix_state \<and>
     staged_query_prefix_conceptual_query_target prefix prefix_state
       \<subseteq> query_sample_space \<and>
     nnreal
       (query_raw_preimage_card_envelope
         (card
           (staged_query_prefix_conceptual_query_target prefix prefix_state))) /
       nnreal size \<le> query_error_bound"
    using future
      staged_query_prefix_conceptual_query_target_subset[of prefix prefix_state]
      staged_query_prefix_conceptual_query_target_fraction_bound
    by blast
qed

lemma checked_staged_query_prefix_conceptual_query_target_hit_bound_from_sampler:
  assumes prefix_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s) \<Longrightarrow>
        query_future_fresh prefix_state"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_conceptual_query_target) s \<le>
      query_error_bound"
  by (rule checked_staged_query_prefix_conceptual_query_target_hit_bound
      [OF query_index_raw_preimage_bound_from_sampler_wellformed
        prefix_bound])

lemma checked_staged_query_prefix_conceptual_default_query_target_hit_bound:
  fixes C :: prob
  assumes raw_bound: "query_index_raw_preimage_bound"
    and prefix_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s) \<Longrightarrow>
        query_future_fresh prefix_state"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_conceptual_default_query_target trace_default
          composition_default)) s \<le>
      query_error_bound"
proof (rule checked_staged_query_prefix_dynamic_index_hit_bound[OF raw_bound])
  fix prefix prefix_state
  assume support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i) s)"
  have future: "query_future_fresh prefix_state"
    by (rule prefix_bound[OF support])
  show
    "query_future_fresh prefix_state \<and>
     staged_query_prefix_conceptual_default_query_target trace_default
       composition_default prefix prefix_state \<subseteq> query_sample_space \<and>
     nnreal
       (query_raw_preimage_card_envelope
         (card
           (staged_query_prefix_conceptual_default_query_target trace_default
             composition_default prefix prefix_state))) /
       nnreal size \<le> query_error_bound"
    using future
      staged_query_prefix_conceptual_default_query_target_subset
      staged_query_prefix_conceptual_default_query_target_fraction_bound
    by blast
qed

lemma checked_staged_query_prefix_conceptual_default_query_target_hit_bound_from_sampler:
  assumes prefix_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s) \<Longrightarrow>
        query_future_fresh prefix_state"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_conceptual_default_query_target trace_default
          composition_default)) s \<le>
      query_error_bound"
  by (rule
      checked_staged_query_prefix_conceptual_default_query_target_hit_bound
      [OF query_index_raw_preimage_bound_from_sampler_wellformed
        prefix_bound])

lemma checked_staged_query_prefix_conceptual_empty_query_target_hit_bound:
  fixes C :: prob
  assumes raw_bound: "query_index_raw_preimage_bound"
    and prefix_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s) \<Longrightarrow>
        query_future_fresh prefix_state"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_conceptual_empty_query_target) s \<le>
      query_error_bound"
proof (rule checked_staged_query_prefix_dynamic_index_hit_bound[OF raw_bound])
  fix prefix prefix_state
  assume support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i) s)"
  have future: "query_future_fresh prefix_state"
    by (rule prefix_bound[OF support])
  show
    "query_future_fresh prefix_state \<and>
     staged_query_prefix_conceptual_empty_query_target prefix prefix_state
       \<subseteq> query_sample_space \<and>
     nnreal
       (query_raw_preimage_card_envelope
         (card
           (staged_query_prefix_conceptual_empty_query_target prefix
             prefix_state))) /
       nnreal size \<le> query_error_bound"
    using future
      staged_query_prefix_conceptual_empty_query_target_subset
      staged_query_prefix_conceptual_empty_query_target_fraction_bound
    by blast
qed

lemma checked_staged_query_prefix_conceptual_empty_query_target_hit_bound_from_sampler:
  assumes prefix_bound:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i) s) \<Longrightarrow>
        query_future_fresh prefix_state"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_conceptual_empty_query_target) s \<le>
      query_error_bound"
  by (rule checked_staged_query_prefix_conceptual_empty_query_target_hit_bound
      [OF query_index_raw_preimage_bound_from_sampler_wellformed
        prefix_bound])

lemma checked_staged_query_prefix_conceptual_query_target_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_conceptual_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state staged_query_prefix_conceptual_query_target)
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
      (rule
        checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

lemma checked_staged_query_prefix_conceptual_default_query_target_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_conceptual_default_query_target trace_default
          composition_default))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state
        (staged_query_prefix_conceptual_default_query_target trace_default
          composition_default))
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
      (rule
        checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

lemma checked_staged_query_prefix_conceptual_empty_query_target_prehit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_conceptual_empty_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
proof (rule checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
  show "HashMap adversary_initial_state = fmempty"
    by (simp add: adversary_initial_state_def)
  show "hash_relation_program
      (checked_staged_query_prefix_dynamic_index_prehit_relation A i
        adversary_initial_state
        staged_query_prefix_conceptual_empty_query_target)
      size (staged_query_search_queries budgets i + 1)
      (checked_staged_query_prefix_receive_with_state A i)"
    by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
        [OF wf controlled i_bound])
      (rule
        checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
qed

lemma checked_staged_query_prefix_conceptual_query_target_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_conceptual_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_conceptual_query_target)
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_conceptual_query_target)
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    show
      "staged_query_prefix_conceptual_query_target prefix prefix_state
        \<subseteq> query_sample_space \<and>
       nnreal
        (query_raw_preimage_card_envelope
          (card
            (staged_query_prefix_conceptual_query_target prefix
              prefix_state))) /
        nnreal size \<le> query_error_bound"
      using staged_query_prefix_conceptual_query_target_subset
        staged_query_prefix_conceptual_query_target_fraction_bound
      by blast
  qed
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_conceptual_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
    by (rule checked_staged_query_prefix_conceptual_query_target_prehit_bound
        [OF wf controlled])
      (use i_bound in simp)
  show ?thesis
    by (rule order_trans[OF hit_bound])
      (intro add_mono prehit_bound order_refl)
qed

lemma checked_staged_query_prefix_conceptual_default_query_target_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_conceptual_default_query_target trace_default
          composition_default))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_conceptual_default_query_target trace_default
          composition_default))
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_conceptual_default_query_target trace_default
          composition_default))
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    show
      "staged_query_prefix_conceptual_default_query_target trace_default
        composition_default prefix prefix_state \<subseteq> query_sample_space \<and>
       nnreal
        (query_raw_preimage_card_envelope
          (card
            (staged_query_prefix_conceptual_default_query_target trace_default
              composition_default prefix prefix_state))) /
        nnreal size \<le> query_error_bound"
      using staged_query_prefix_conceptual_default_query_target_subset
        staged_query_prefix_conceptual_default_query_target_fraction_bound
      by blast
  qed
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        (staged_query_prefix_conceptual_default_query_target trace_default
          composition_default))
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
    by (rule
        checked_staged_query_prefix_conceptual_default_query_target_prehit_bound
        [OF wf controlled])
      (use i_bound in simp)
  show ?thesis
    by (rule order_trans[OF hit_bound])
      (intro add_mono prehit_bound order_refl)
qed

lemma checked_staged_query_prefix_conceptual_empty_query_target_hit_bound_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_conceptual_empty_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_conceptual_empty_query_target)
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_conceptual_empty_query_target)
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    show
      "staged_query_prefix_conceptual_empty_query_target prefix prefix_state
        \<subseteq> query_sample_space \<and>
       nnreal
        (query_raw_preimage_card_envelope
          (card
            (staged_query_prefix_conceptual_empty_query_target prefix
              prefix_state))) /
        nnreal size \<le> query_error_bound"
      using staged_query_prefix_conceptual_empty_query_target_subset
        staged_query_prefix_conceptual_empty_query_target_fraction_bound
      by blast
  qed
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_conceptual_empty_query_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
    by (rule
        checked_staged_query_prefix_conceptual_empty_query_target_prehit_bound
        [OF wf controlled])
      (use i_bound in simp)
  show ?thesis
    by (rule order_trans[OF hit_bound])
      (intro add_mono prehit_bound order_refl)
qed

definition checked_staged_security_with_query_prefix_conceptual_target_hit
where
  "checked_staged_security_with_query_prefix_conceptual_target_hit out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_dynamic_index_hit
      staged_query_prefix_conceptual_query_target out"

definition checked_staged_security_with_query_prefix_conceptual_default_target_hit
where
  "checked_staged_security_with_query_prefix_conceptual_default_target_hit
      trace_default composition_default out \<longleftrightarrow>
    checked_staged_security_with_query_prefix_dynamic_index_hit
      (staged_query_prefix_conceptual_default_query_target trace_default
        composition_default) out"

definition checked_staged_security_with_query_prefix_conceptual_empty_target_hit
where
  "checked_staged_security_with_query_prefix_conceptual_empty_target_hit out
    \<longleftrightarrow>
    checked_staged_security_with_query_prefix_dynamic_index_hit
      staged_query_prefix_conceptual_empty_query_target out"

lemma checked_staged_security_with_query_prefix_conceptual_target_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      checked_staged_security_with_query_prefix_conceptual_target_hit
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
  unfolding checked_staged_security_with_query_prefix_conceptual_target_hit_def
  by (rule checked_staged_security_with_query_prefix_dynamic_index_hit_bound)
    (rule checked_staged_query_prefix_conceptual_query_target_hit_bound_from_budgets
      [OF wf controlled i_bound])

lemma checked_staged_security_with_query_prefix_conceptual_default_target_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_conceptual_default_target_hit
        trace_default composition_default)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
  unfolding
    checked_staged_security_with_query_prefix_conceptual_default_target_hit_def
  by (rule checked_staged_security_with_query_prefix_dynamic_index_hit_bound)
    (rule
      checked_staged_query_prefix_conceptual_default_query_target_hit_bound_from_budgets
      [OF wf controlled i_bound])

lemma checked_staged_security_with_query_prefix_conceptual_empty_target_hit_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      checked_staged_security_with_query_prefix_conceptual_empty_target_hit
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
  unfolding
    checked_staged_security_with_query_prefix_conceptual_empty_target_hit_def
  by (rule checked_staged_security_with_query_prefix_dynamic_index_hit_bound)
    (rule
      checked_staged_query_prefix_conceptual_empty_query_target_hit_bound_from_budgets
      [OF wf controlled i_bound])

end

end
