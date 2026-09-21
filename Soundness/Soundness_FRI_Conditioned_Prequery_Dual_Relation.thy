theory Soundness_FRI_Conditioned_Prequery_Dual_Relation
  imports
    Stark.Soundness_FRI_Conditioned_Prequery_Header
    Stark.Soundness_FRI_Conditioned_Query_Challenge_Dual
begin

context soundness
begin

definition ro_conditioned_trace_challenge_evidence_at
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f \<Rightarrow> bool"
where
  "ro_conditioned_trace_challenge_evidence_at M fr roots i b \<longleftrightarrow>
    i < length roots \<and>
    (\<exists>final.
      ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state) (fr # take (Suc i) roots) final \<and>
      fmlookup M (TraceFriChallenge i final) = Some b)"

definition ro_conditioned_composition_challenge_evidence_at
  :: "(('f protocol_hash_input, 'f) fmap) \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      'f \<Rightarrow> bool"
where
  "ro_conditioned_composition_challenge_evidence_at M
      fr trace_roots trace_final as dg roots i b \<longleftrightarrow>
    i < length roots \<and>
    (\<exists>final.
      ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots i)
        final \<and>
      fmlookup M (CompositionFriChallenge i final) = Some b)"

lemma ro_conditioned_trace_challenge_evidence_at_unique:
  assumes left:
      "ro_conditioned_trace_challenge_evidence_at M fr roots i b"
    and right:
      "ro_conditioned_trace_challenge_evidence_at M fr roots i b'"
  shows "b = b'"
proof -
  from left obtain left_final where
    left_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state) (fr # take (Suc i) roots)
        left_final"
    and left_lookup:
      "fmlookup M (TraceFriChallenge i left_final) = Some b"
    unfolding ro_conditioned_trace_challenge_evidence_at_def by blast
  from right obtain right_final where
    right_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state) (fr # take (Suc i) roots)
        right_final"
    and right_lookup:
      "fmlookup M (TraceFriChallenge i right_final) = Some b'"
    unfolding ro_conditioned_trace_challenge_evidence_at_def by blast
  have "left_final = right_final"
    by (rule ro_absorb_lookup_chain_functional[
      OF left_chain right_chain])
  then show ?thesis using left_lookup right_lookup by simp
qed

lemma ro_conditioned_composition_challenge_evidence_at_unique:
  assumes left:
      "ro_conditioned_composition_challenge_evidence_at M
        fr trace_roots trace_final as dg roots i b"
    and right:
      "ro_conditioned_composition_challenge_evidence_at M
        fr trace_roots trace_final as dg roots i b'"
  shows "b = b'"
proof -
  from left obtain left_final where
    left_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots i)
        left_final"
    and left_lookup:
      "fmlookup M (CompositionFriChallenge i left_final) = Some b"
    unfolding ro_conditioned_composition_challenge_evidence_at_def by blast
  from right obtain right_final where
    right_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (composition_fri_challenge_prefix_messages
          fr trace_roots trace_final as dg roots i)
        right_final"
    and right_lookup:
      "fmlookup M (CompositionFriChallenge i right_final) = Some b'"
    unfolding ro_conditioned_composition_challenge_evidence_at_def by blast
  have "left_final = right_final"
    by (rule ro_absorb_lookup_chain_functional[
      OF left_chain right_chain])
  then show ?thesis using left_lookup right_lookup by simp
qed

lemma ro_conditioned_trace_challenge_evidence_imp_at:
  assumes evidence:
      "ro_conditioned_trace_challenge_evidence M fr roots challenges"
    and i_bound: "i < length roots"
  shows
    "ro_conditioned_trace_challenge_evidence_at M fr roots i
      (challenges ! i)"
  using evidence i_bound
  unfolding ro_conditioned_trace_challenge_evidence_def
    ro_conditioned_trace_challenge_evidence_at_def
  by blast

lemma ro_conditioned_composition_challenge_evidence_imp_at:
  assumes evidence:
      "ro_conditioned_composition_challenge_evidence M
        fr trace_roots trace_final as dg roots challenges"
    and i_bound: "i < length roots"
  shows
    "ro_conditioned_composition_challenge_evidence_at M
      fr trace_roots trace_final as dg roots i (challenges ! i)"
  using evidence i_bound
  unfolding ro_conditioned_composition_challenge_evidence_def
    ro_conditioned_composition_challenge_evidence_at_def
  by blast

definition ro_conditioned_trace_residual_query_lists_at_value
where
  "ro_conditioned_trace_residual_query_lists_at_value M
      roots b final_value i =
    fri_conditioned_quantitative_residual_query_lists_at_value
      (clength - 1) roots b final_value (channel_for_hash_map M) i"

definition ro_conditioned_composition_residual_query_lists_at_value
where
  "ro_conditioned_composition_residual_query_lists_at_value M
      dg roots b final_value i =
    (if to_nat dg \<le> maxDegree then
      fri_conditioned_quantitative_residual_query_lists_at_value
        (to_nat dg) roots b final_value (channel_for_hash_map M) i
     else {})"

definition ro_conditioned_trace_degenerate_query_lists_at
where
  "ro_conditioned_trace_degenerate_query_lists_at M
      roots final_value i round_idx =
    fri_conditioned_quantitative_degenerate_query_lists_at
      (clength - 1) roots final_value (channel_for_hash_map M)
      i round_idx"

definition ro_conditioned_composition_degenerate_query_lists_at
where
  "ro_conditioned_composition_degenerate_query_lists_at M
      dg roots final_value i round_idx =
    (if to_nat dg \<le> maxDegree then
      fri_conditioned_quantitative_degenerate_query_lists_at
        (to_nat dg) roots final_value (channel_for_hash_map M)
        i round_idx
     else {})"

definition ro_conditioned_trace_challenge_values_at
where
  "ro_conditioned_trace_challenge_values_at M fr roots i =
    {b. ro_conditioned_trace_challenge_evidence_at M fr roots i b}"

definition ro_conditioned_composition_challenge_values_at
where
  "ro_conditioned_composition_challenge_values_at M
      fr trace_roots trace_final as dg roots i =
    {b. ro_conditioned_composition_challenge_evidence_at M
      fr trace_roots trace_final as dg roots i b}"

lemma card_ro_conditioned_trace_challenge_values_at_le_one:
  "card (ro_conditioned_trace_challenge_values_at M fr roots i) \<le> 1"
proof -
  have finite:
      "finite (ro_conditioned_trace_challenge_values_at M fr roots i)"
    by simp
  have unique:
      "\<forall>b \<in> ro_conditioned_trace_challenge_values_at M fr roots i.
       \<forall>b' \<in> ro_conditioned_trace_challenge_values_at M fr roots i.
       b = b'"
    unfolding ro_conditioned_trace_challenge_values_at_def
    using ro_conditioned_trace_challenge_evidence_at_unique
    by blast
  show ?thesis
    using card_le_Suc0_iff_eq[OF finite] unique by simp
qed

lemma card_ro_conditioned_composition_challenge_values_at_le_one:
  "card
    (ro_conditioned_composition_challenge_values_at M
      fr trace_roots trace_final as dg roots i) \<le> 1"
proof -
  let ?B =
    "ro_conditioned_composition_challenge_values_at M
      fr trace_roots trace_final as dg roots i"
  have finite: "finite ?B" by simp
  have unique: "\<forall>b \<in> ?B. \<forall>b' \<in> ?B. b = b'"
    unfolding ro_conditioned_composition_challenge_values_at_def
    using ro_conditioned_composition_challenge_evidence_at_unique
    by blast
  show ?thesis
    using card_le_Suc0_iff_eq[OF finite] unique by simp
qed

definition ro_conditioned_trace_residual_query_lists_at
where
  "ro_conditioned_trace_residual_query_lists_at M fr roots final_value i =
    (\<Union>b \<in> ro_conditioned_trace_challenge_values_at M fr roots i.
      ro_conditioned_trace_residual_query_lists_at_value M
        roots b final_value i)"

definition ro_conditioned_composition_residual_query_lists_at
where
  "ro_conditioned_composition_residual_query_lists_at M
      fr trace_roots trace_final as dg roots final_value i =
    (\<Union>b \<in> ro_conditioned_composition_challenge_values_at M
        fr trace_roots trace_final as dg roots i.
      ro_conditioned_composition_residual_query_lists_at_value M
        dg roots b final_value i)"

lemma card_ro_conditioned_trace_residual_query_lists_at:
  assumes roots_len: "length roots = ceil_log clength"
    and i_bound: "i < length roots"
  shows
    "card
      (ro_conditioned_trace_residual_query_lists_at M fr roots
        final_value i) \<le>
      (modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
proof (cases
    "ro_conditioned_trace_challenge_values_at M fr roots i = {}")
  case True
  then show ?thesis
    unfolding ro_conditioned_trace_residual_query_lists_at_def by simp
next
  case False
  then obtain b where b:
      "b \<in> ro_conditioned_trace_challenge_values_at M fr roots i"
    by blast
  have values_eq:
      "ro_conditioned_trace_challenge_values_at M fr roots i = {b}"
  proof
    show
      "ro_conditioned_trace_challenge_values_at M fr roots i \<subseteq> {b}"
      using b
      unfolding ro_conditioned_trace_challenge_values_at_def
      using ro_conditioned_trace_challenge_evidence_at_unique
      by blast
    show
      "{b} \<subseteq> ro_conditioned_trace_challenge_values_at M fr roots i"
      using b by simp
  qed
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have round_count:
      "length roots = ceil_log (Suc (clength - 1))"
    using roots_len clength_pos by simp
  have rounds_le: "ceil_log (Suc (clength - 1)) \<le> N"
    using ceil_log_clength_le_eval_power[OF eval_power] clength_pos
    by simp
  have local:
      "card
        (ro_conditioned_trace_residual_query_lists_at_value M
          roots b final_value i) \<le>
        (modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i)))
          (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
    unfolding ro_conditioned_trace_residual_query_lists_at_value_def
    by (rule
      card_fri_conditioned_quantitative_residual_query_lists_at_value[
        OF eval_power round_count rounds_le i_bound])
  show ?thesis
    unfolding ro_conditioned_trace_residual_query_lists_at_def values_eq
    using local by simp
qed

lemma card_ro_conditioned_composition_residual_query_lists_at:
  assumes roots_len: "length roots = ceil_log (Suc (to_nat dg))"
    and degree_bound: "to_nat dg \<le> maxDegree"
    and i_bound: "i < length roots"
  shows
    "card
      (ro_conditioned_composition_residual_query_lists_at M
        fr trace_roots trace_final as dg roots final_value i) \<le>
      (modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
proof (cases
    "ro_conditioned_composition_challenge_values_at M
      fr trace_roots trace_final as dg roots i = {}")
  case True
  then show ?thesis
    unfolding ro_conditioned_composition_residual_query_lists_at_def
    by simp
next
  case False
  let ?B =
    "ro_conditioned_composition_challenge_values_at M
      fr trace_roots trace_final as dg roots i"
  from False obtain b where b: "b \<in> ?B" by blast
  have values_eq: "?B = {b}"
  proof
    show "?B \<subseteq> {b}"
      using b
      unfolding ro_conditioned_composition_challenge_values_at_def
      using ro_conditioned_composition_challenge_evidence_at_unique
      by blast
    show "{b} \<subseteq> ?B" using b by simp
  qed
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have rounds_le: "ceil_log (Suc (to_nat dg)) \<le> N"
    by (rule ceil_log_reachable_degree_le_eval_power[
      OF eval_power degree_bound])
  have local:
      "card
        (ro_conditioned_composition_residual_query_lists_at_value M
          dg roots b final_value i) \<le>
        (modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i)))
          (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
    unfolding
      ro_conditioned_composition_residual_query_lists_at_value_def
      if_P[OF degree_bound]
    by (rule
      card_fri_conditioned_quantitative_residual_query_lists_at_value[
        OF eval_power roots_len rounds_le i_bound])
  show ?thesis
    unfolding
      ro_conditioned_composition_residual_query_lists_at_def values_eq
    using local by simp
qed

definition ro_conditioned_trace_residual_query_lists
where
  "ro_conditioned_trace_residual_query_lists M fr roots final_value =
    (\<Union>i < length roots.
      ro_conditioned_trace_residual_query_lists_at M fr roots
        final_value i)"

definition ro_conditioned_composition_residual_query_lists
where
  "ro_conditioned_composition_residual_query_lists M
      fr trace_roots trace_final as dg roots final_value =
    (\<Union>i < length roots.
      ro_conditioned_composition_residual_query_lists_at M
        fr trace_roots trace_final as dg roots final_value i)"

definition ro_conditioned_combined_residual_query_lists
where
  "ro_conditioned_combined_residual_query_lists M
      fr trace_roots trace_final as dg composition_roots
      composition_final =
    ro_conditioned_trace_residual_query_lists M
        fr trace_roots trace_final \<union>
      ro_conditioned_composition_residual_query_lists M
        fr trace_roots trace_final as dg composition_roots
        composition_final"

lemma ro_conditioned_trace_residual_query_lists_subset:
  "ro_conditioned_trace_residual_query_lists M fr roots final_value \<subseteq>
    fri_query_index_list_space"
  unfolding ro_conditioned_trace_residual_query_lists_def
    ro_conditioned_trace_residual_query_lists_at_def
    ro_conditioned_trace_residual_query_lists_at_value_def
    ro_conditioned_trace_challenge_values_at_def
    fri_conditioned_quantitative_residual_query_lists_at_value_def Let_def
  by auto

lemma ro_conditioned_composition_residual_query_lists_subset:
  "ro_conditioned_composition_residual_query_lists M
      fr trace_roots trace_final as dg roots final_value \<subseteq>
    fri_query_index_list_space"
  unfolding ro_conditioned_composition_residual_query_lists_def
    ro_conditioned_composition_residual_query_lists_at_def
    ro_conditioned_composition_residual_query_lists_at_value_def
    ro_conditioned_composition_challenge_values_at_def
    fri_conditioned_quantitative_residual_query_lists_at_value_def Let_def
  by auto

lemma ro_conditioned_combined_residual_query_lists_subset:
  "ro_conditioned_combined_residual_query_lists M
      fr trace_roots trace_final as dg composition_roots
      composition_final \<subseteq> fri_query_index_list_space"
  unfolding ro_conditioned_combined_residual_query_lists_def
  using ro_conditioned_trace_residual_query_lists_subset
    ro_conditioned_composition_residual_query_lists_subset
  by blast

lemma card_ro_conditioned_trace_residual_query_lists:
  assumes roots_len: "length roots = ceil_log clength"
  shows
    "card
      (ro_conditioned_trace_residual_query_lists M fr roots final_value) \<le>
      fri_conditioned_residual_query_list_card_bound (clength - 1)"
proof -
  let ?S =
    "\<lambda>i. ro_conditioned_trace_residual_query_lists_at M fr roots
      final_value i"
  have finite_each: "\<And>i. finite (?S i)"
    unfolding ro_conditioned_trace_residual_query_lists_at_def
      ro_conditioned_trace_residual_query_lists_at_value_def
      fri_conditioned_quantitative_residual_query_lists_at_value_def
      Let_def
    by (rule finite_subset[OF _ finite_fri_query_index_list_space])
      auto
  have union_card:
      "card (\<Union>i < length roots. ?S i) \<le>
        (\<Sum>i < length roots. card (?S i))"
    by (rule card_UN_le) (simp add: finite_each)
  have local:
      "\<And>i. i < length roots \<Longrightarrow>
        card (?S i) \<le>
          (modulo_preimage_card_envelope query_sample_space_size
            (length (fri_canonical_domain_at (Suc i)))
            (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
    by (rule card_ro_conditioned_trace_residual_query_lists_at[
      OF roots_len])
  have sum_bound:
      "(\<Sum>i < length roots. card (?S i)) \<le>
        (\<Sum>i < length roots.
          (modulo_preimage_card_envelope query_sample_space_size
            (length (fri_canonical_domain_at (Suc i)))
            (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds)"
    by (rule sum_mono) (use local in auto)
  show ?thesis
    unfolding ro_conditioned_trace_residual_query_lists_def
      fri_conditioned_residual_query_list_card_bound_def
    using union_card sum_bound roots_len clength_pos
    by simp
qed

lemma card_ro_conditioned_composition_residual_query_lists:
  assumes roots_len: "length roots = ceil_log (Suc (to_nat dg))"
    and degree_bound: "to_nat dg \<le> maxDegree"
  shows
    "card
      (ro_conditioned_composition_residual_query_lists M
        fr trace_roots trace_final as dg roots final_value) \<le>
      fri_conditioned_residual_query_list_card_bound (to_nat dg)"
proof -
  let ?S =
    "\<lambda>i. ro_conditioned_composition_residual_query_lists_at M
      fr trace_roots trace_final as dg roots final_value i"
  have finite_each: "\<And>i. finite (?S i)"
    unfolding ro_conditioned_composition_residual_query_lists_at_def
      ro_conditioned_composition_residual_query_lists_at_value_def
      fri_conditioned_quantitative_residual_query_lists_at_value_def
      Let_def
    by (rule finite_subset[OF _ finite_fri_query_index_list_space])
      auto
  have union_card:
      "card (\<Union>i < length roots. ?S i) \<le>
        (\<Sum>i < length roots. card (?S i))"
    by (rule card_UN_le) (simp add: finite_each)
  have local:
      "\<And>i. i < length roots \<Longrightarrow>
        card (?S i) \<le>
          (modulo_preimage_card_envelope query_sample_space_size
            (length (fri_canonical_domain_at (Suc i)))
            (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
    by (rule card_ro_conditioned_composition_residual_query_lists_at[
      OF roots_len degree_bound])
  have sum_bound:
      "(\<Sum>i < length roots. card (?S i)) \<le>
        (\<Sum>i < length roots.
          (modulo_preimage_card_envelope query_sample_space_size
            (length (fri_canonical_domain_at (Suc i)))
            (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds)"
    by (rule sum_mono) (use local in auto)
  show ?thesis
    unfolding ro_conditioned_composition_residual_query_lists_def
      fri_conditioned_residual_query_list_card_bound_def
    using union_card sum_bound roots_len
    by simp
qed

lemma card_ro_conditioned_combined_residual_query_lists:
  assumes trace_len: "length trace_roots = ceil_log clength"
    and composition_len:
      "length composition_roots = ceil_log (Suc (to_nat dg))"
    and degree_bound: "to_nat dg \<le> maxDegree"
  shows
    "card
      (ro_conditioned_combined_residual_query_lists M
        fr trace_roots trace_final as dg composition_roots
        composition_final) \<le>
      fri_conditioned_residual_query_list_card_bound (clength - 1) +
        fri_conditioned_residual_query_list_card_bound maxDegree"
proof -
  have trace:
      "card
        (ro_conditioned_trace_residual_query_lists M
          fr trace_roots trace_final) \<le>
        fri_conditioned_residual_query_list_card_bound (clength - 1)"
    by (rule card_ro_conditioned_trace_residual_query_lists[OF trace_len])
  have composition0:
      "card
        (ro_conditioned_composition_residual_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final) \<le>
        fri_conditioned_residual_query_list_card_bound (to_nat dg)"
    by (rule card_ro_conditioned_composition_residual_query_lists[
      OF composition_len degree_bound])
  have composition:
      "card
        (ro_conditioned_composition_residual_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final) \<le>
        fri_conditioned_residual_query_list_card_bound maxDegree"
    by (rule order_trans[OF composition0])
      (rule fri_conditioned_residual_query_list_card_bound_mono[
        OF degree_bound])
  have union:
      "card
        (ro_conditioned_trace_residual_query_lists M
            fr trace_roots trace_final \<union>
          ro_conditioned_composition_residual_query_lists M
            fr trace_roots trace_final as dg composition_roots
            composition_final) \<le>
        card
          (ro_conditioned_trace_residual_query_lists M
            fr trace_roots trace_final) +
        card
          (ro_conditioned_composition_residual_query_lists M
            fr trace_roots trace_final as dg composition_roots
            composition_final)"
    by (rule card_Un_le)
  show ?thesis
    unfolding ro_conditioned_combined_residual_query_lists_def
    by (rule order_trans[OF union]) (use trace composition in simp)
qed

lemma
  ro_conditioned_combined_residual_query_lists_relation_fiber_bound:
  assumes trace_len: "length trace_roots = ceil_log clength"
    and composition_len:
      "length composition_roots = ceil_log (Suc (to_nat dg))"
    and degree_bound: "to_nat dg \<le> maxDegree"
  shows
    "query_index_raw_list_relation_fiber_bound
      (ro_conditioned_combined_residual_query_lists M
        fr trace_roots trace_final as dg composition_roots
        composition_final) \<le>
      rounds *
        query_raw_preimage_card_envelope
          (rounds *
            (fri_conditioned_residual_query_list_card_bound (clength - 1) +
             fri_conditioned_residual_query_list_card_bound maxDegree))"
proof (rule query_index_raw_list_relation_fiber_bound_by_card)
  show
    "ro_conditioned_combined_residual_query_lists M
        fr trace_roots trace_final as dg composition_roots
        composition_final \<subseteq> fri_query_index_list_space"
    by (rule ro_conditioned_combined_residual_query_lists_subset)
  show
    "card
      (ro_conditioned_combined_residual_query_lists M
        fr trace_roots trace_final as dg composition_roots
        composition_final) \<le>
      fri_conditioned_residual_query_list_card_bound (clength - 1) +
        fri_conditioned_residual_query_list_card_bound maxDegree"
    by (rule card_ro_conditioned_combined_residual_query_lists[
      OF trace_len composition_len degree_bound])
qed

definition ro_conditioned_trace_degenerate_raw_values
where
  "ro_conditioned_trace_degenerate_raw_values M roots final_value =
    (\<Union>i < length roots.
      fri_conditioned_quantitative_degenerate_raw_values_at
        (clength - 1) roots final_value (channel_for_hash_map M) i)"

definition ro_conditioned_composition_degenerate_raw_values
where
  "ro_conditioned_composition_degenerate_raw_values M
      dg roots final_value =
    (if to_nat dg \<le> maxDegree then
      (\<Union>i < length roots.
        fri_conditioned_quantitative_degenerate_raw_values_at
          (to_nat dg) roots final_value (channel_for_hash_map M) i)
     else {})"

definition ro_conditioned_combined_degenerate_raw_values
where
  "ro_conditioned_combined_degenerate_raw_values M
      trace_roots trace_final dg composition_roots composition_final =
    ro_conditioned_trace_degenerate_raw_values M
        trace_roots trace_final \<union>
      ro_conditioned_composition_degenerate_raw_values M
        dg composition_roots composition_final"

lemma card_ro_conditioned_trace_degenerate_raw_values:
  assumes roots_len: "length roots = ceil_log clength"
  shows
    "card
      (ro_conditioned_trace_degenerate_raw_values M roots final_value) \<le>
      fri_conditioned_degenerate_raw_value_card_bound (clength - 1)"
proof -
  let ?S =
    "\<lambda>i. fri_conditioned_quantitative_degenerate_raw_values_at
      (clength - 1) roots final_value (channel_for_hash_map M) i"
  have finite_each: "\<And>i. finite (?S i)" by simp
  have union_card:
      "card (\<Union>i < length roots. ?S i) \<le>
        (\<Sum>i < length roots. card (?S i))"
    by (rule card_UN_le) (simp add: finite_each)
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have round_count:
      "length roots = ceil_log (Suc (clength - 1))"
    using roots_len clength_pos by simp
  have rounds_le: "ceil_log (Suc (clength - 1)) \<le> N"
    using ceil_log_clength_le_eval_power[OF eval_power] clength_pos
    by simp
  have local:
      "\<And>i. i < length roots \<Longrightarrow>
        card (?S i) \<le>
          query_raw_preimage_card_envelope
            (modulo_preimage_card_envelope query_sample_space_size
              (length (fri_canonical_domain_at (Suc i)))
              (length (fri_canonical_domain_at (Suc i)) - 1))"
    by (rule
      card_fri_conditioned_quantitative_degenerate_raw_values_at[
        OF eval_power round_count rounds_le])
  have sum_bound:
      "(\<Sum>i < length roots. card (?S i)) \<le>
        (\<Sum>i < length roots.
          query_raw_preimage_card_envelope
            (modulo_preimage_card_envelope query_sample_space_size
              (length (fri_canonical_domain_at (Suc i)))
              (length (fri_canonical_domain_at (Suc i)) - 1)))"
    by (rule sum_mono) (use local in auto)
  show ?thesis
    unfolding ro_conditioned_trace_degenerate_raw_values_def
      fri_conditioned_degenerate_raw_value_card_bound_def
    using union_card sum_bound round_count
    by simp
qed

lemma card_ro_conditioned_composition_degenerate_raw_values:
  assumes roots_len: "length roots = ceil_log (Suc (to_nat dg))"
    and degree_bound: "to_nat dg \<le> maxDegree"
  shows
    "card
      (ro_conditioned_composition_degenerate_raw_values M
        dg roots final_value) \<le>
      fri_conditioned_degenerate_raw_value_card_bound (to_nat dg)"
proof -
  let ?S =
    "\<lambda>i. fri_conditioned_quantitative_degenerate_raw_values_at
      (to_nat dg) roots final_value (channel_for_hash_map M) i"
  have finite_each: "\<And>i. finite (?S i)" by simp
  have union_card:
      "card (\<Union>i < length roots. ?S i) \<le>
        (\<Sum>i < length roots. card (?S i))"
    by (rule card_UN_le) (simp add: finite_each)
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have rounds_le: "ceil_log (Suc (to_nat dg)) \<le> N"
    by (rule ceil_log_reachable_degree_le_eval_power[
      OF eval_power degree_bound])
  have local:
      "\<And>i. i < length roots \<Longrightarrow>
        card (?S i) \<le>
          query_raw_preimage_card_envelope
            (modulo_preimage_card_envelope query_sample_space_size
              (length (fri_canonical_domain_at (Suc i)))
              (length (fri_canonical_domain_at (Suc i)) - 1))"
    by (rule
      card_fri_conditioned_quantitative_degenerate_raw_values_at[
        OF eval_power roots_len rounds_le])
  have sum_bound:
      "(\<Sum>i < length roots. card (?S i)) \<le>
        (\<Sum>i < length roots.
          query_raw_preimage_card_envelope
            (modulo_preimage_card_envelope query_sample_space_size
              (length (fri_canonical_domain_at (Suc i)))
              (length (fri_canonical_domain_at (Suc i)) - 1)))"
    by (rule sum_mono) (use local in auto)
  show ?thesis
    unfolding ro_conditioned_composition_degenerate_raw_values_def
      if_P[OF degree_bound]
      fri_conditioned_degenerate_raw_value_card_bound_def
    using union_card sum_bound roots_len
    by simp
qed

lemma card_ro_conditioned_combined_degenerate_raw_values:
  assumes trace_len: "length trace_roots = ceil_log clength"
    and composition_len:
      "length composition_roots = ceil_log (Suc (to_nat dg))"
    and degree_bound: "to_nat dg \<le> maxDegree"
  shows
    "card
      (ro_conditioned_combined_degenerate_raw_values M
        trace_roots trace_final dg composition_roots composition_final) \<le>
      fri_conditioned_degenerate_raw_value_card_bound (clength - 1) +
        fri_conditioned_degenerate_raw_value_card_bound maxDegree"
proof -
  have trace:
      "card
        (ro_conditioned_trace_degenerate_raw_values M
          trace_roots trace_final) \<le>
        fri_conditioned_degenerate_raw_value_card_bound (clength - 1)"
    by (rule card_ro_conditioned_trace_degenerate_raw_values[
      OF trace_len])
  have composition0:
      "card
        (ro_conditioned_composition_degenerate_raw_values M
          dg composition_roots composition_final) \<le>
        fri_conditioned_degenerate_raw_value_card_bound (to_nat dg)"
    by (rule card_ro_conditioned_composition_degenerate_raw_values[
      OF composition_len degree_bound])
  have composition:
      "card
        (ro_conditioned_composition_degenerate_raw_values M
          dg composition_roots composition_final) \<le>
        fri_conditioned_degenerate_raw_value_card_bound maxDegree"
    by (rule order_trans[OF composition0])
      (rule fri_conditioned_degenerate_raw_value_card_bound_mono[
        OF degree_bound])
  have union:
      "card
        (ro_conditioned_trace_degenerate_raw_values M
            trace_roots trace_final \<union>
          ro_conditioned_composition_degenerate_raw_values M
            dg composition_roots composition_final) \<le>
        card
          (ro_conditioned_trace_degenerate_raw_values M
            trace_roots trace_final) +
        card
          (ro_conditioned_composition_degenerate_raw_values M
            dg composition_roots composition_final)"
    by (rule card_Un_le)
  show ?thesis
    unfolding ro_conditioned_combined_degenerate_raw_values_def
    by (rule order_trans[OF union]) (use trace composition in simp)
qed

lemma fri_conditioned_quantitative_degenerate_query_list_raw_value:
  fixes prefix_state :: "'f protocol_channel"
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_count: "length roots = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and i_bound: "i < length roots"
    and qs:
      "query_idxs \<in>
        fri_conditioned_quantitative_degenerate_query_lists_at d roots
          final_value prefix_state i round_idx"
    and raw_index:
      "index (to_nat raw) = query_idxs ! round_idx"
  shows
    "raw \<in> fri_conditioned_quantitative_degenerate_raw_values_at d roots
      final_value prefix_state i"
proof -
  let ?layers =
    "fri_builder_conceptual_layers roots prefix_state final_value"
  have transition:
      "\<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i (?layers ! i)) \<and>
       fri_table_low_degree_on
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i) (?layers ! Suc i))"
    using qs
    unfolding fri_conditioned_quantitative_degenerate_query_lists_at_def
      Let_def
    by blast
  have round_bound: "round_idx < length query_idxs"
    using qs
    unfolding fri_conditioned_quantitative_degenerate_query_lists_at_def
      Let_def
    by blast
  have qs_space: "set query_idxs \<subseteq> query_sample_space"
    using qs
    unfolding fri_conditioned_quantitative_degenerate_query_lists_at_def
      fri_query_index_list_space_def Let_def
    by blast
  have query_mem: "query_idxs ! round_idx \<in> set query_idxs"
    by (rule nth_mem[OF round_bound])
  have query_space: "query_idxs ! round_idx \<in> query_sample_space"
    using qs_space query_mem by blast
  have agreement:
      "fri_evidence_next_idx roots query_idxs round_idx i \<in>
        fri_conditioned_degenerate_agreement_indices i
          (?layers ! i) (?layers ! Suc i)"
    using qs
    unfolding fri_conditioned_quantitative_degenerate_query_lists_at_def
      Let_def
    by blast
  have roots_le: "length roots \<le> N"
    using round_count rounds_le by simp
  have evidence_at:
      "fri_evidence_next_idx roots query_idxs round_idx i =
        query_idxs ! round_idx mod
          length (fri_canonical_domain_at (Suc i))"
    by (rule fri_evidence_next_idx_at[
      OF eval_power roots_le i_bound round_bound])
  have index_in:
      "index (to_nat raw) \<in>
        fri_conditioned_query_indices roots i
          (fri_conditioned_degenerate_agreement_indices i
            (?layers ! i) (?layers ! Suc i))"
    unfolding fri_conditioned_query_indices_def
    using raw_index query_space agreement evidence_at
    by simp
  show ?thesis
    unfolding
      fri_conditioned_quantitative_degenerate_raw_values_at_def
      Let_def if_P[OF transition] query_index_raw_preimage_def
    using index_in by simp
qed


definition ro_conditioned_residual_absorbed_query_relation
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool)"
where
  "ro_conditioned_residual_absorbed_query_relation M x y \<longleftrightarrow>
    (let s = channel_for_hash_map M in
      \<not> hash_map_output_collision s \<and>
      PState adversary_initial_state \<notin> hash_map_output_values s \<and>
      (\<exists>fr trace_roots trace_final as dg
          composition_roots composition_final
          query_chunks raws query_start final j.
        length trace_roots = ceil_log clength \<and>
        length as = length spec \<and>
        length composition_roots = ceil_log (Suc (to_nat dg)) \<and>
        to_nat dg \<le> maxDegree \<and>
        ro_absorb_lookup_chain s (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final)
          query_start \<and>
        ro_absorb_lookup_chain s query_start
          (List.concat (take j query_chunks)) final \<and>
        length raws = rounds \<and>
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_conditioned_combined_residual_query_lists M
            fr trace_roots trace_final as dg composition_roots
            composition_final \<and>
        j < rounds \<and>
        x = QueryIndexChallenge j final \<and>
        y = raws ! j))"

lemma ro_conditioned_residual_absorbed_query_relationD:
  assumes rel:
    "ro_conditioned_residual_absorbed_query_relation M x y"
  obtains fr trace_roots trace_final as dg
      composition_roots composition_final
      query_chunks raws query_start final j where
    "\<not> hash_map_output_collision (channel_for_hash_map M)"
    "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map M)"
    "length trace_roots = ceil_log clength"
    "length as = length spec"
    "length composition_roots = ceil_log (Suc (to_nat dg))"
    "to_nat dg \<le> maxDegree"
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state)
      (verifier_header_messages fr trace_roots trace_final as dg
        composition_roots composition_final)
      query_start"
    "ro_absorb_lookup_chain (channel_for_hash_map M) query_start
      (List.concat (take j query_chunks)) final"
    "length raws = rounds"
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
      ro_conditioned_combined_residual_query_lists M
        fr trace_roots trace_final as dg composition_roots
        composition_final"
    "j < rounds"
    "x = QueryIndexChallenge j final"
    "y = raws ! j"
  using rel
  unfolding ro_conditioned_residual_absorbed_query_relation_def Let_def
  by blast

definition ro_conditioned_residual_query_raw_relation_fiber_bound :: nat
where
  "ro_conditioned_residual_query_raw_relation_fiber_bound =
    rounds *
      query_raw_preimage_card_envelope
        (rounds *
          (fri_conditioned_residual_query_list_card_bound (clength - 1) +
           fri_conditioned_residual_query_list_card_bound maxDegree))"



lemma transcript_absorb_lookup_query_index_update[simp]:
  "fmlookup
      (HashMap
        (channel_for_hash_map
          (fmupd (QueryIndexChallenge c st) y M)))
      (TranscriptAbsorb i message) =
    fmlookup (HashMap (channel_for_hash_map M))
      (TranscriptAbsorb i message)"
  unfolding channel_for_hash_map_def by simp


lemma ro_conditioned_residual_absorbed_query_relation_direct_fiber_card_bound:
  "card {y.
      hash_state_relation_direct_activation
        ro_conditioned_residual_absorbed_query_relation M x y}
    \<le> ro_conditioned_residual_query_raw_relation_fiber_bound"
proof (cases "{y.
    hash_state_relation_direct_activation
      ro_conditioned_residual_absorbed_query_relation M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
      "hash_state_relation_direct_activation
        ro_conditioned_residual_absorbed_query_relation M x y0"
    by blast
  have rel0:
      "ro_conditioned_residual_absorbed_query_relation
        (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from ro_conditioned_residual_absorbed_query_relationD[OF rel0]
  obtain fr0 trace_roots0 trace_final0 as0 dg0
      composition_roots0 composition_final0
      query_chunks0 raws0 query_start0 final0 j0 where
    clean0:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y0 M))"
    and no_initial0:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y0 M))"
    and trace_len0: "length trace_roots0 = ceil_log clength"
    and alpha_len0: "length as0 = length spec"
    and composition_len0:
      "length composition_roots0 = ceil_log (Suc (to_nat dg0))"
    and degree_bound0: "to_nat dg0 \<le> maxDegree"
    and header_chain0:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state)
        (verifier_header_messages fr0 trace_roots0 trace_final0 as0 dg0
          composition_roots0 composition_final0)
        query_start0"
    and query_chain0:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y0 M))
        query_start0 (List.concat (take j0 query_chunks0)) final0"
    and raws_len0: "length raws0 = rounds"
    and raws_in0:
      "map (\<lambda>raw. index (to_nat raw)) raws0 \<in>
        ro_conditioned_combined_residual_query_lists (fmupd x y0 M)
          fr0 trace_roots0 trace_final0 as0 dg0 composition_roots0
          composition_final0"
    and j0_bound: "j0 < rounds"
    and x0: "x = QueryIndexChallenge j0 final0"
    and y0_eq: "y0 = raws0 ! j0"
    .
  let ?Q0 =
    "ro_conditioned_combined_residual_query_lists (fmupd x y0 M)
      fr0 trace_roots0 trace_final0 as0 dg0 composition_roots0
      composition_final0"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          ro_conditioned_residual_absorbed_query_relation M x y}
        \<subseteq> query_index_raw_list_position_values ?Q0 j0"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          ro_conditioned_residual_absorbed_query_relation M x y}"
    have rely:
        "ro_conditioned_residual_absorbed_query_relation
          (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from ro_conditioned_residual_absorbed_query_relationD[OF rely]
    obtain fr trace_roots trace_final as dg
        composition_roots composition_final
        query_chunks raws query_start final j where
      clean:
        "\<not> hash_map_output_collision
          (channel_for_hash_map (fmupd x y M))"
      and no_initial:
        "PState adversary_initial_state \<notin>
          hash_map_output_values (channel_for_hash_map (fmupd x y M))"
      and trace_len: "length trace_roots = ceil_log clength"
      and alpha_len: "length as = length spec"
      and composition_len:
        "length composition_roots = ceil_log (Suc (to_nat dg))"
      and degree_bound: "to_nat dg \<le> maxDegree"
      and header_chain:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y M))
          (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final)
          query_start"
      and query_chain:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y M))
          query_start (List.concat (take j query_chunks)) final"
      and raws_len: "length raws = rounds"
      and raws_in:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_conditioned_combined_residual_query_lists (fmupd x y M)
            fr trace_roots trace_final as dg composition_roots
            composition_final"
      and j_bound: "j < rounds"
      and x_eq: "x = QueryIndexChallenge j final"
      and y_eq: "y = raws ! j"
      .
    have j_eq: "j = j0"
      and final_eq: "final = final0"
      using x_eq x0 by simp_all
    have full0:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (verifier_header_messages fr0 trace_roots0 trace_final0 as0 dg0
              composition_roots0 composition_final0 @
            List.concat (take j0 query_chunks0))
          final0"
      by (rule ro_absorb_lookup_chain_append[
          OF header_chain0 query_chain0])
    have header_chain_base:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final)
          query_start"
      using header_chain unfolding x0 by simp
    have query_chain_base:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          query_start (List.concat (take j0 query_chunks)) final0"
      using query_chain j_eq final_eq unfolding x0 by simp
    have header_chain_ref:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final)
          query_start"
      using header_chain_base unfolding x0 by simp
    have query_chain_ref:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          query_start (List.concat (take j0 query_chunks)) final0"
      using query_chain_base unfolding x0 by simp
    have full:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
              composition_roots composition_final @
            List.concat (take j0 query_chunks))
          final0"
      by (rule ro_absorb_lookup_chain_append[
          OF header_chain_ref query_chain_ref])
    have messages_eq:
        "verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final @
          List.concat (take j0 query_chunks) =
         verifier_header_messages fr0 trace_roots0 trace_final0 as0 dg0
            composition_roots0 composition_final0 @
          List.concat (take j0 query_chunks0)"
      by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[
          OF clean0 no_initial0 full full0])
    have composition_len_plus:
        "length composition_roots = ceil_log (to_nat dg + 1)"
      using composition_len by simp
    have composition_len0_plus:
        "length composition_roots0 = ceil_log (to_nat dg0 + 1)"
      using composition_len0 by simp
    have header_eq:
        "verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final =
         verifier_header_messages fr0 trace_roots0 trace_final0 as0 dg0
            composition_roots0 composition_final0"
      by (rule verifier_header_messages_prefix_eq_from_append_eq[
          OF trace_len trace_len0 alpha_len alpha_len0
            composition_len_plus composition_len0_plus messages_eq])
    have fields_eq:
        "fr = fr0 \<and> trace_roots = trace_roots0 \<and>
         trace_final = trace_final0 \<and> as = as0 \<and> dg = dg0 \<and>
         composition_roots = composition_roots0 \<and>
         composition_final = composition_final0"
      by (rule verifier_header_messages_relevant_fields_eq[
          OF trace_len trace_len0 alpha_len alpha_len0
            composition_len_plus composition_len0_plus header_eq])
    have Q_eq:
        "ro_conditioned_combined_residual_query_lists (fmupd x y M)
            fr trace_roots trace_final as dg composition_roots
            composition_final =
          ?Q0"
      using fields_eq
      unfolding x0
      by (simp add:
        ro_conditioned_combined_residual_query_lists_def
        ro_conditioned_trace_residual_query_lists_def
        ro_conditioned_composition_residual_query_lists_def
        ro_conditioned_trace_residual_query_lists_at_def
        ro_conditioned_composition_residual_query_lists_at_def
        ro_conditioned_trace_challenge_values_at_def
        ro_conditioned_composition_challenge_values_at_def
        ro_conditioned_trace_challenge_evidence_at_def
        ro_conditioned_composition_challenge_evidence_at_def
        ro_conditioned_trace_residual_query_lists_at_value_def
        ro_conditioned_composition_residual_query_lists_at_value_def
        fri_conditioned_quantitative_residual_query_lists_at_value_def
        fri_builder_conceptual_layers_def)
    have raws_preimage:
        "raws \<in> query_index_raw_list_preimage ?Q0"
      unfolding query_index_raw_list_preimage_def
      using raws_len raws_in Q_eq by simp
    show "y \<in> query_index_raw_list_position_values ?Q0 j0"
      unfolding query_index_raw_list_position_values_def
      using raws_preimage y_eq j_eq j0_bound by blast
  qed
  have finite_Q0:
      "finite (query_index_raw_list_position_values ?Q0 j0)"
    by simp
  have card_le:
      "card {y.
        hash_state_relation_direct_activation
          ro_conditioned_residual_absorbed_query_relation M x y}
        \<le> card (query_index_raw_list_position_values ?Q0 j0)"
    by (rule card_mono[OF finite_Q0 subset])
  have position_le:
      "card (query_index_raw_list_position_values ?Q0 j0) \<le>
        query_index_raw_list_relation_fiber_bound ?Q0"
  proof -
    have nonnegative:
        "card (query_index_raw_list_position_values ?Q0 j0) \<le>
          (\<Sum>i < rounds.
            card (query_index_raw_list_position_values ?Q0 i))"
      by (rule member_le_sum) (use j0_bound in simp_all)
    show ?thesis
      using nonnegative
      unfolding query_index_raw_list_relation_fiber_bound_def .
  qed
  have relation_le:
      "query_index_raw_list_relation_fiber_bound ?Q0 \<le>
        ro_conditioned_residual_query_raw_relation_fiber_bound"
    unfolding ro_conditioned_residual_query_raw_relation_fiber_bound_def
    by (rule
        ro_conditioned_combined_residual_query_lists_relation_fiber_bound[
          OF trace_len0 composition_len0 degree_bound0])
  show ?thesis
    by (rule order_trans[OF card_le])
      (rule order_trans[OF position_le relation_le])
qed



definition ro_conditioned_degenerate_absorbed_query_relation
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool)"
where
  "ro_conditioned_degenerate_absorbed_query_relation M x y \<longleftrightarrow>
    (let s = channel_for_hash_map M in
      \<not> hash_map_output_collision s \<and>
      PState adversary_initial_state \<notin> hash_map_output_values s \<and>
      (\<exists>fr trace_roots trace_final as dg
          composition_roots composition_final
          query_chunks raws query_start final j.
        length trace_roots = ceil_log clength \<and>
        length as = length spec \<and>
        length composition_roots = ceil_log (Suc (to_nat dg)) \<and>
        to_nat dg \<le> maxDegree \<and>
        ro_absorb_lookup_chain s (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final)
          query_start \<and>
        ro_absorb_lookup_chain s query_start
          (List.concat (take j query_chunks)) final \<and>
        length raws = rounds \<and>
        ((\<exists>i < length trace_roots.
            map (\<lambda>raw. index (to_nat raw)) raws \<in>
              ro_conditioned_trace_degenerate_query_lists_at M
                trace_roots trace_final i j) \<or>
         (\<exists>i < length composition_roots.
            map (\<lambda>raw. index (to_nat raw)) raws \<in>
              ro_conditioned_composition_degenerate_query_lists_at M
                dg composition_roots composition_final i j)) \<and>
        j < rounds \<and>
        x = QueryIndexChallenge j final \<and>
        y = raws ! j))"

lemma ro_conditioned_degenerate_absorbed_query_relationD:
  assumes rel:
    "ro_conditioned_degenerate_absorbed_query_relation M x y"
  obtains fr trace_roots trace_final as dg
      composition_roots composition_final
      query_chunks raws query_start final j where
    "\<not> hash_map_output_collision (channel_for_hash_map M)"
    "PState adversary_initial_state \<notin>
      hash_map_output_values (channel_for_hash_map M)"
    "length trace_roots = ceil_log clength"
    "length as = length spec"
    "length composition_roots = ceil_log (Suc (to_nat dg))"
    "to_nat dg \<le> maxDegree"
    "ro_absorb_lookup_chain (channel_for_hash_map M)
      (PState adversary_initial_state)
      (verifier_header_messages fr trace_roots trace_final as dg
        composition_roots composition_final)
      query_start"
    "ro_absorb_lookup_chain (channel_for_hash_map M) query_start
      (List.concat (take j query_chunks)) final"
    "length raws = rounds"
    "(\<exists>i < length trace_roots.
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_conditioned_trace_degenerate_query_lists_at M
            trace_roots trace_final i j) \<or>
     (\<exists>i < length composition_roots.
        map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_conditioned_composition_degenerate_query_lists_at M
            dg composition_roots composition_final i j)"
    "j < rounds"
    "x = QueryIndexChallenge j final"
    "y = raws ! j"
  using rel
  unfolding ro_conditioned_degenerate_absorbed_query_relation_def Let_def
  by blast



lemma ro_conditioned_trace_degenerate_query_raw_value:
  assumes roots_len: "length roots = ceil_log clength"
    and i_bound: "i < length roots"
    and degenerate:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_conditioned_trace_degenerate_query_lists_at M
          roots final_value i round_idx"
    and raws_len: "length raws = rounds"
    and round_bound: "round_idx < rounds"
  shows
    "raws ! round_idx \<in>
      ro_conditioned_trace_degenerate_raw_values M roots final_value"
proof -
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have round_count:
      "length roots = ceil_log (Suc (clength - 1))"
    using roots_len clength_pos by simp
  have rounds_le: "ceil_log (Suc (clength - 1)) \<le> N"
    using ceil_log_clength_le_eval_power[OF eval_power] clength_pos
    by simp
  have raw_index:
      "index (to_nat (raws ! round_idx)) =
        map (\<lambda>raw. index (to_nat raw)) raws ! round_idx"
    using raws_len round_bound by simp
  have degenerate':
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        fri_conditioned_quantitative_degenerate_query_lists_at
          (clength - 1) roots final_value (channel_for_hash_map M)
          i round_idx"
    using degenerate
    unfolding ro_conditioned_trace_degenerate_query_lists_at_def .
  have raw:
      "raws ! round_idx \<in>
        fri_conditioned_quantitative_degenerate_raw_values_at
          (clength - 1) roots final_value (channel_for_hash_map M) i"
    by (rule
      fri_conditioned_quantitative_degenerate_query_list_raw_value[
        OF eval_power round_count rounds_le i_bound degenerate'
          raw_index])
  show ?thesis
    unfolding ro_conditioned_trace_degenerate_raw_values_def
    using i_bound raw by blast
qed

lemma ro_conditioned_composition_degenerate_query_raw_value:
  assumes roots_len: "length roots = ceil_log (Suc (to_nat dg))"
    and degree_bound: "to_nat dg \<le> maxDegree"
    and i_bound: "i < length roots"
    and degenerate:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_conditioned_composition_degenerate_query_lists_at M
          dg roots final_value i round_idx"
    and raws_len: "length raws = rounds"
    and round_bound: "round_idx < rounds"
  shows
    "raws ! round_idx \<in>
      ro_conditioned_composition_degenerate_raw_values M
        dg roots final_value"
proof -
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have rounds_le: "ceil_log (Suc (to_nat dg)) \<le> N"
    by (rule ceil_log_reachable_degree_le_eval_power[
      OF eval_power degree_bound])
  have raw_index:
      "index (to_nat (raws ! round_idx)) =
        map (\<lambda>raw. index (to_nat raw)) raws ! round_idx"
    using raws_len round_bound by simp
  have degenerate':
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        fri_conditioned_quantitative_degenerate_query_lists_at
          (to_nat dg) roots final_value (channel_for_hash_map M)
          i round_idx"
    using degenerate degree_bound
    unfolding ro_conditioned_composition_degenerate_query_lists_at_def
      if_P[OF degree_bound] by simp
  have raw:
      "raws ! round_idx \<in>
        fri_conditioned_quantitative_degenerate_raw_values_at
          (to_nat dg) roots final_value (channel_for_hash_map M) i"
    by (rule
      fri_conditioned_quantitative_degenerate_query_list_raw_value[
        OF eval_power roots_len rounds_le i_bound degenerate'
          raw_index])
  show ?thesis
    unfolding ro_conditioned_composition_degenerate_raw_values_def
      if_P[OF degree_bound]
    using i_bound raw by blast
qed



definition ro_conditioned_degenerate_query_raw_relation_fiber_bound :: nat
where
  "ro_conditioned_degenerate_query_raw_relation_fiber_bound =
    fri_conditioned_degenerate_raw_value_card_bound (clength - 1) +
    fri_conditioned_degenerate_raw_value_card_bound maxDegree"

lemma ro_conditioned_degenerate_absorbed_query_relation_direct_fiber_card_bound:
  "card {y.
      hash_state_relation_direct_activation
        ro_conditioned_degenerate_absorbed_query_relation M x y}
    \<le> ro_conditioned_degenerate_query_raw_relation_fiber_bound"
proof (cases "{y.
    hash_state_relation_direct_activation
      ro_conditioned_degenerate_absorbed_query_relation M x y} = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
      "hash_state_relation_direct_activation
        ro_conditioned_degenerate_absorbed_query_relation M x y0"
    by blast
  have rel0:
      "ro_conditioned_degenerate_absorbed_query_relation
        (fmupd x y0 M) x y0"
    using y0
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
    by blast
  from ro_conditioned_degenerate_absorbed_query_relationD[OF rel0]
  obtain fr0 trace_roots0 trace_final0 as0 dg0
      composition_roots0 composition_final0
      query_chunks0 raws0 query_start0 final0 j0 where
    clean0:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (fmupd x y0 M))"
    and no_initial0:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map (fmupd x y0 M))"
    and trace_len0: "length trace_roots0 = ceil_log clength"
    and alpha_len0: "length as0 = length spec"
    and composition_len0:
      "length composition_roots0 = ceil_log (Suc (to_nat dg0))"
    and degree_bound0: "to_nat dg0 \<le> maxDegree"
    and header_chain0:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y0 M))
        (PState adversary_initial_state)
        (verifier_header_messages fr0 trace_roots0 trace_final0 as0 dg0
          composition_roots0 composition_final0)
        query_start0"
    and query_chain0:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (fmupd x y0 M))
        query_start0 (List.concat (take j0 query_chunks0)) final0"
    and raws_len0: "length raws0 = rounds"
    and degenerate0:
      "(\<exists>i < length trace_roots0.
          map (\<lambda>raw. index (to_nat raw)) raws0 \<in>
            ro_conditioned_trace_degenerate_query_lists_at
              (fmupd x y0 M) trace_roots0 trace_final0 i j0) \<or>
       (\<exists>i < length composition_roots0.
          map (\<lambda>raw. index (to_nat raw)) raws0 \<in>
            ro_conditioned_composition_degenerate_query_lists_at
              (fmupd x y0 M) dg0 composition_roots0 composition_final0
              i j0)"
    and j0_bound: "j0 < rounds"
    and x0: "x = QueryIndexChallenge j0 final0"
    and y0_eq: "y0 = raws0 ! j0"
    .
  let ?R0 =
    "ro_conditioned_combined_degenerate_raw_values (fmupd x y0 M)
      trace_roots0 trace_final0 dg0 composition_roots0
      composition_final0"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          ro_conditioned_degenerate_absorbed_query_relation M x y}
        \<subseteq> ?R0"
  proof
    fix y
    assume y:
      "y \<in> {y.
        hash_state_relation_direct_activation
          ro_conditioned_degenerate_absorbed_query_relation M x y}"
    have rely:
        "ro_conditioned_degenerate_absorbed_query_relation
          (fmupd x y M) x y"
      using y
      unfolding hash_state_relation_direct_activation_def
        hash_state_relation_active_def
      by blast
    from ro_conditioned_degenerate_absorbed_query_relationD[OF rely]
    obtain fr trace_roots trace_final as dg
        composition_roots composition_final
        query_chunks raws query_start final j where
      clean:
        "\<not> hash_map_output_collision
          (channel_for_hash_map (fmupd x y M))"
      and no_initial:
        "PState adversary_initial_state \<notin>
          hash_map_output_values (channel_for_hash_map (fmupd x y M))"
      and trace_len: "length trace_roots = ceil_log clength"
      and alpha_len: "length as = length spec"
      and composition_len:
        "length composition_roots = ceil_log (Suc (to_nat dg))"
      and degree_bound: "to_nat dg \<le> maxDegree"
      and header_chain:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y M))
          (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final)
          query_start"
      and query_chain:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y M))
          query_start (List.concat (take j query_chunks)) final"
      and raws_len: "length raws = rounds"
      and degenerate:
        "(\<exists>i < length trace_roots.
            map (\<lambda>raw. index (to_nat raw)) raws \<in>
              ro_conditioned_trace_degenerate_query_lists_at
                (fmupd x y M) trace_roots trace_final i j) \<or>
         (\<exists>i < length composition_roots.
            map (\<lambda>raw. index (to_nat raw)) raws \<in>
              ro_conditioned_composition_degenerate_query_lists_at
                (fmupd x y M) dg composition_roots composition_final i j)"
      and j_bound: "j < rounds"
      and x_eq: "x = QueryIndexChallenge j final"
      and y_eq: "y = raws ! j"
      .
    have j_eq: "j = j0"
      and final_eq: "final = final0"
      using x_eq x0 by simp_all
    have full0:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (verifier_header_messages fr0 trace_roots0 trace_final0 as0 dg0
              composition_roots0 composition_final0 @
            List.concat (take j0 query_chunks0))
          final0"
      by (rule ro_absorb_lookup_chain_append[
          OF header_chain0 query_chain0])
    have header_chain_base:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final)
          query_start"
      using header_chain unfolding x0 by simp
    have query_chain_base:
        "ro_absorb_lookup_chain (channel_for_hash_map M)
          query_start (List.concat (take j0 query_chunks)) final0"
      using query_chain j_eq final_eq unfolding x0 by simp
    have header_chain_ref:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final)
          query_start"
      using header_chain_base unfolding x0 by simp
    have query_chain_ref:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          query_start (List.concat (take j0 query_chunks)) final0"
      using query_chain_base unfolding x0 by simp
    have full:
        "ro_absorb_lookup_chain
          (channel_for_hash_map (fmupd x y0 M))
          (PState adversary_initial_state)
          (verifier_header_messages fr trace_roots trace_final as dg
              composition_roots composition_final @
            List.concat (take j0 query_chunks))
          final0"
      by (rule ro_absorb_lookup_chain_append[
          OF header_chain_ref query_chain_ref])
    have messages_eq:
        "verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final @
          List.concat (take j0 query_chunks) =
         verifier_header_messages fr0 trace_roots0 trace_final0 as0 dg0
            composition_roots0 composition_final0 @
          List.concat (take j0 query_chunks0)"
      by (rule ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target[
          OF clean0 no_initial0 full full0])
    have composition_len_plus:
        "length composition_roots = ceil_log (to_nat dg + 1)"
      using composition_len by simp
    have composition_len0_plus:
        "length composition_roots0 = ceil_log (to_nat dg0 + 1)"
      using composition_len0 by simp
    have header_eq:
        "verifier_header_messages fr trace_roots trace_final as dg
            composition_roots composition_final =
         verifier_header_messages fr0 trace_roots0 trace_final0 as0 dg0
            composition_roots0 composition_final0"
      by (rule verifier_header_messages_prefix_eq_from_append_eq[
          OF trace_len trace_len0 alpha_len alpha_len0
            composition_len_plus composition_len0_plus messages_eq])
    have fields_eq:
        "fr = fr0 \<and> trace_roots = trace_roots0 \<and>
         trace_final = trace_final0 \<and> as = as0 \<and> dg = dg0 \<and>
         composition_roots = composition_roots0 \<and>
         composition_final = composition_final0"
      by (rule verifier_header_messages_relevant_fields_eq[
          OF trace_len trace_len0 alpha_len alpha_len0
            composition_len_plus composition_len0_plus header_eq])
    have raw_own:
        "raws ! j \<in>
          ro_conditioned_combined_degenerate_raw_values (fmupd x y M)
            trace_roots trace_final dg composition_roots
            composition_final"
    using degenerate
    proof
      assume trace_case:
        "\<exists>i < length trace_roots.
          map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_degenerate_query_lists_at
              (fmupd x y M) trace_roots trace_final i j"
      then obtain i where i_bound: "i < length trace_roots"
        and member:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_degenerate_query_lists_at
              (fmupd x y M) trace_roots trace_final i j"
        by blast
      have trace_raw:
        "raws ! j \<in>
          ro_conditioned_trace_degenerate_raw_values (fmupd x y M)
            trace_roots trace_final"
        by (rule ro_conditioned_trace_degenerate_query_raw_value[
          OF trace_len i_bound member raws_len j_bound])
      show ?thesis
        unfolding ro_conditioned_combined_degenerate_raw_values_def
        using trace_raw by blast
    next
      assume composition_case:
        "\<exists>i < length composition_roots.
          map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_degenerate_query_lists_at
              (fmupd x y M) dg composition_roots composition_final i j"
      then obtain i where i_bound: "i < length composition_roots"
        and member:
          "map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_degenerate_query_lists_at
              (fmupd x y M) dg composition_roots composition_final i j"
        by blast
      have composition_raw:
        "raws ! j \<in>
          ro_conditioned_composition_degenerate_raw_values (fmupd x y M)
            dg composition_roots composition_final"
        by (rule ro_conditioned_composition_degenerate_query_raw_value[
          OF composition_len degree_bound i_bound member raws_len j_bound])
      show ?thesis
        unfolding ro_conditioned_combined_degenerate_raw_values_def
        using composition_raw by blast
    qed
    have R_eq:
        "ro_conditioned_combined_degenerate_raw_values (fmupd x y M)
            trace_roots trace_final dg composition_roots
            composition_final =
          ?R0"
      using fields_eq
      unfolding x0
      by (simp add:
        ro_conditioned_combined_degenerate_raw_values_def
        ro_conditioned_trace_degenerate_raw_values_def
        ro_conditioned_composition_degenerate_raw_values_def
        fri_conditioned_quantitative_degenerate_raw_values_at_def
        fri_builder_conceptual_layers_def)
    show "y \<in> ?R0"
      using raw_own R_eq y_eq by simp
  qed
  have finite_R0: "finite ?R0" by simp
  have card_le:
      "card {y.
        hash_state_relation_direct_activation
          ro_conditioned_degenerate_absorbed_query_relation M x y}
        \<le> card ?R0"
    by (rule card_mono[OF finite_R0 subset])
  have relation_le:
      "card ?R0 \<le>
        ro_conditioned_degenerate_query_raw_relation_fiber_bound"
    unfolding ro_conditioned_degenerate_query_raw_relation_fiber_bound_def
    by (rule card_ro_conditioned_combined_degenerate_raw_values[
      OF trace_len0 composition_len0 degree_bound0])
  show ?thesis
    by (rule order_trans[OF card_le relation_le])
qed



definition ro_conditioned_augmented_absorbed_query_relation
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool)"
where
  "ro_conditioned_augmented_absorbed_query_relation M x y \<longleftrightarrow>
    ro_conditioned_residual_absorbed_query_relation M x y \<or>
    ro_conditioned_degenerate_absorbed_query_relation M x y"

definition ro_conditioned_augmented_query_raw_relation_fiber_bound :: nat
where
  "ro_conditioned_augmented_query_raw_relation_fiber_bound =
    ro_conditioned_residual_query_raw_relation_fiber_bound +
    ro_conditioned_degenerate_query_raw_relation_fiber_bound"

lemma ro_conditioned_augmented_absorbed_query_relation_direct_fiber_card_bound:
  "card {y.
      hash_state_relation_direct_activation
        ro_conditioned_augmented_absorbed_query_relation M x y}
    \<le> ro_conditioned_augmented_query_raw_relation_fiber_bound"
proof -
  let ?A =
    "{y. hash_state_relation_direct_activation
      ro_conditioned_residual_absorbed_query_relation M x y}"
  let ?B =
    "{y. hash_state_relation_direct_activation
      ro_conditioned_degenerate_absorbed_query_relation M x y}"
  have subset:
      "{y.
        hash_state_relation_direct_activation
          ro_conditioned_augmented_absorbed_query_relation M x y}
        \<subseteq> ?A \<union> ?B"
    unfolding hash_state_relation_direct_activation_def
      hash_state_relation_active_def
      ro_conditioned_augmented_absorbed_query_relation_def
    by blast
  have finite_union: "finite (?A \<union> ?B)" by simp
  have card_subset:
      "card {y.
        hash_state_relation_direct_activation
          ro_conditioned_augmented_absorbed_query_relation M x y}
        \<le> card (?A \<union> ?B)"
    by (rule card_mono[OF finite_union subset])
  have union_le: "card (?A \<union> ?B) \<le> card ?A + card ?B"
    by (rule card_Un_le)
  have residual:
      "card ?A \<le> ro_conditioned_residual_query_raw_relation_fiber_bound"
    by (rule
      ro_conditioned_residual_absorbed_query_relation_direct_fiber_card_bound)
  have degenerate:
      "card ?B \<le> ro_conditioned_degenerate_query_raw_relation_fiber_bound"
    by (rule
      ro_conditioned_degenerate_absorbed_query_relation_direct_fiber_card_bound)
  show ?thesis
    unfolding ro_conditioned_augmented_query_raw_relation_fiber_bound_def
    by (rule order_trans[OF card_subset])
      (rule order_trans[OF union_le], use residual degenerate in simp)
qed

end
end
