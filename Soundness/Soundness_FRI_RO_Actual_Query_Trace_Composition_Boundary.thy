theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Boundary
  imports Soundness_FRI_RO_Actual_Query_Composition_Candidate
begin

context soundness
begin

definition trace_power_boundary_indices
where
  "trace_power_boundary_indices original candidate =
    {idx \<in> trace_table_base_agreement_indices original candidate.
      map ((!) original) (powers_scaled idx) \<noteq>
        map ((!) candidate) (powers_scaled idx)}"

definition trace_composition_accepted_indices
where
  "trace_composition_accepted_indices original candidate composition as =
    {idx \<in> trace_table_base_agreement_indices original candidate.
      query_consistent_at original composition as idx}"

lemma trace_power_boundary_indices_subset_query_sample_space:
  "trace_power_boundary_indices original candidate \<subseteq> query_sample_space"
  unfolding trace_power_boundary_indices_def
    trace_table_base_agreement_indices_def
  by auto

lemma trace_composition_accepted_indices_subset_query_sample_space:
  "trace_composition_accepted_indices original candidate composition as \<subseteq>
    query_sample_space"
  unfolding trace_composition_accepted_indices_def
    trace_table_base_agreement_indices_def
  by auto

lemma query_consistent_at_transfer_outside_trace_power_boundary:
  assumes lengths: "length original = length candidate"
    and base:
      "idx \<in> trace_table_base_agreement_indices original candidate"
    and outside: "idx \<notin> trace_power_boundary_indices original candidate"
    and consistent: "query_consistent_at original composition as idx"
  shows "query_consistent_at candidate composition as idx"
proof -
  have trace_values:
      "map ((!) original) (powers_scaled idx) =
        map ((!) candidate) (powers_scaled idx)"
    using base outside unfolding trace_power_boundary_indices_def by simp
  have equivalence:
      "query_consistent_at original composition as idx \<longleftrightarrow>
        query_consistent_at candidate composition as idx"
    by (rule query_consistent_at_cong_opened_values)
      (use lengths trace_values in simp_all)
  show ?thesis using consistent equivalence by simp
qed

lemma trace_composition_accepted_indices_subset:
  assumes lengths: "length original = length candidate"
  shows
    "trace_composition_accepted_indices original candidate composition as \<subseteq>
      query_agreement_indices candidate composition as \<union>
      trace_power_boundary_indices original candidate"
proof
  fix idx
  assume idx_in:
    "idx \<in> trace_composition_accepted_indices
      original candidate composition as"
  have base:
      "idx \<in> trace_table_base_agreement_indices original candidate"
    and consistent: "query_consistent_at original composition as idx"
    using idx_in unfolding trace_composition_accepted_indices_def by auto
  show
    "idx \<in> query_agreement_indices candidate composition as \<union>
      trace_power_boundary_indices original candidate"
  proof (cases "idx \<in> trace_power_boundary_indices original candidate")
    case True
    then show ?thesis by simp
  next
    case False
    have candidate_consistent:
        "query_consistent_at candidate composition as idx"
      by (rule query_consistent_at_transfer_outside_trace_power_boundary[
            OF lengths base False consistent])
    have idx_sample: "idx \<in> query_sample_space"
      using base unfolding trace_table_base_agreement_indices_def by simp
    have "idx \<in> query_agreement_indices candidate composition as"
      using idx_sample candidate_consistent
      unfolding query_agreement_indices_def by simp
    then show ?thesis by simp
  qed
qed

lemma trace_power_boundary_indices_subset_shift_union:
  "trace_power_boundary_indices original candidate \<subseteq>
    (\<Union>k \<in> {1..<powers}.
      {idx \<in> trace_table_base_agreement_indices original candidate.
        original ! (idx + k * scale) \<noteq>
          candidate ! (idx + k * scale)})"
  proof
  fix idx
  assume boundary: "idx \<in> trace_power_boundary_indices original candidate"
  have base:
      "idx \<in> trace_table_base_agreement_indices original candidate"
    and maps_ne:
      "map ((!) original) (powers_scaled idx) \<noteq>
        map ((!) candidate) (powers_scaled idx)"
    using boundary unfolding trace_power_boundary_indices_def by auto
  have exists_shift:
      "\<exists>k < powers.
        original ! (idx + k * scale) \<noteq>
          candidate ! (idx + k * scale)"
  proof (rule ccontr)
    assume
      "\<not> (\<exists>k<powers.
        original ! (idx + k * scale) \<noteq>
          candidate ! (idx + k * scale))"
    then have pointwise:
        "\<forall>k < powers.
          original ! (idx + k * scale) =
            candidate ! (idx + k * scale)"
      by simp
    have
        "map ((!) original) (powers_scaled idx) =
          map ((!) candidate) (powers_scaled idx)"
      unfolding powers_scaled_def
      using pointwise by auto
    then show False using maps_ne by contradiction
  qed
  then obtain k where k_lt: "k < powers"
    and value_ne:
      "original ! (idx + k * scale) \<noteq>
        candidate ! (idx + k * scale)"
    by blast
  have k_nonzero: "k \<noteq> 0"
  proof
    assume "k = 0"
    then have
        "original ! idx \<noteq> candidate ! idx"
      using value_ne by simp
    moreover have
        "original ! idx = candidate ! idx"
      using base unfolding trace_table_base_agreement_indices_def by simp
    ultimately show False by contradiction
  qed
  have k_in: "k \<in> {1..<powers}"
    using k_lt k_nonzero by simp
  show
    "idx \<in>
      (\<Union>k \<in> {1..<powers}.
        {idx \<in> trace_table_base_agreement_indices original candidate.
          original ! (idx + k * scale) \<noteq>
            candidate ! (idx + k * scale)})"
    using k_in base value_ne by blast
qed

lemma trace_power_boundary_shift_card_bound:
  "card
      {idx \<in> trace_table_base_agreement_indices original candidate.
        original ! (idx + k * scale) \<noteq>
          candidate ! (idx + k * scale)}
    \<le>
    (query_sample_space_size -
      card (trace_table_base_agreement_indices original candidate)) +
      k * scale"
  proof -
  let ?A = "trace_table_base_agreement_indices original candidate"
  let ?B =
    "{idx \<in> ?A.
      original ! (idx + k * scale) \<noteq> candidate ! (idx + k * scale)}"
  let ?internal =
    "{idx \<in> ?B. idx + k * scale < query_sample_space_size}"
  let ?tail =
    "{idx \<in> ?B. query_sample_space_size \<le> idx + k * scale}"

  have A_subset: "?A \<subseteq> query_sample_space"
    unfolding trace_table_base_agreement_indices_def by auto
  have B_subset: "?B \<subseteq> query_sample_space"
    using A_subset by auto
  have finite_A: "finite ?A"
    by (rule finite_subset[OF A_subset finite_query_sample_space])
  have finite_B: "finite ?B"
    by (rule finite_subset[OF B_subset finite_query_sample_space])
  have split: "?B = ?internal \<union> ?tail"
    by auto

  have internal_image_subset:
      "(\<lambda>idx. idx + k * scale) ` ?internal \<subseteq> query_sample_space - ?A"
  proof
    fix shifted
    assume
      "shifted \<in> (\<lambda>idx. idx + k * scale) ` ?internal"
    then obtain idx where idx_internal: "idx \<in> ?internal"
      and shifted_eq: "shifted = idx + k * scale"
      by blast
    have shifted_bound: "shifted < query_sample_space_size"
      using idx_internal shifted_eq by simp
    have shifted_sample: "shifted \<in> query_sample_space"
      using shifted_bound unfolding query_sample_space_def by simp
    have value_ne:
        "original ! shifted \<noteq> candidate ! shifted"
      using idx_internal shifted_eq by simp
    have shifted_not_A: "shifted \<notin> ?A"
      using value_ne
      unfolding trace_table_base_agreement_indices_def by auto
    show "shifted \<in> query_sample_space - ?A"
      using shifted_sample shifted_not_A by simp
  qed
  have internal_inj:
      "inj_on (\<lambda>idx. idx + k * scale) ?internal"
    by (rule inj_onI) simp
  have finite_diff: "finite (query_sample_space - ?A)"
    by simp
  have internal_card:
      "card ?internal \<le> query_sample_space_size - card ?A"
  proof -
    have "card ?internal =
        card ((\<lambda>idx. idx + k * scale) ` ?internal)"
      by (simp add: card_image internal_inj)
    also have "... \<le> card (query_sample_space - ?A)"
      by (rule card_mono[OF finite_diff internal_image_subset])
    also have "... = card query_sample_space - card ?A"
      by (rule card_Diff_subset)
        (use A_subset finite_A in auto)
    also have "... = query_sample_space_size - card ?A"
      by simp
    finally show ?thesis .
  qed

  have tail_interval_subset:
      "?tail \<subseteq>
        {query_sample_space_size - k * scale..<query_sample_space_size}"
  proof
    fix idx
    assume idx_tail: "idx \<in> ?tail"
    have idx_sample: "idx \<in> query_sample_space"
      using idx_tail B_subset by auto
    have idx_upper: "idx < query_sample_space_size"
      by (rule query_sample_spaceD[OF idx_sample])
    have tail_condition:
        "query_sample_space_size \<le> idx + k * scale"
      using idx_tail by simp
    have idx_lower: "query_sample_space_size - k * scale \<le> idx"
      using tail_condition by arith
    show
      "idx \<in>
        {query_sample_space_size - k * scale..<query_sample_space_size}"
      using idx_lower idx_upper by simp
  qed
  have tail_card: "card ?tail \<le> k * scale"
  proof -
    have "card ?tail \<le>
        card {query_sample_space_size - k * scale..<query_sample_space_size}"
      by (rule card_mono)
        (use tail_interval_subset in simp_all)
    also have "... =
        query_sample_space_size -
          (query_sample_space_size - k * scale)"
      by simp
    also have "... \<le> k * scale"
      by simp
    finally show ?thesis .
  qed

  have "card ?B = card (?internal \<union> ?tail)"
    by (rule arg_cong[where f=card, OF split])
  also have "... \<le> card ?internal + card ?tail"
    by (rule card_Un_le)
  also have "... \<le>
      (query_sample_space_size - card ?A) + k * scale"
    using internal_card tail_card by linarith
  finally show ?thesis .
qed

lemma trace_power_boundary_indices_card_bound:
  "card (trace_power_boundary_indices original candidate) \<le>
    (\<Sum>k \<in> {1..<powers}.
      ((query_sample_space_size -
        card (trace_table_base_agreement_indices original candidate)) +
        k * scale))"
  proof -
  let ?A = "trace_table_base_agreement_indices original candidate"
  let ?shift_bad =
    "\<lambda>k. {idx \<in> ?A.
      original ! (idx + k * scale) \<noteq> candidate ! (idx + k * scale)}"
  let ?union = "\<Union>k \<in> {1..<powers}. ?shift_bad k"
  have finite_A: "finite ?A"
    unfolding trace_table_base_agreement_indices_def by simp
  have finite_union: "finite ?union"
    by (simp add: finite_A)
  have "card (trace_power_boundary_indices original candidate) \<le>
      card ?union"
    by (rule card_mono[
          OF finite_union
            trace_power_boundary_indices_subset_shift_union])
  also have "... \<le> (\<Sum>k \<in> {1..<powers}. card (?shift_bad k))"
    by (rule card_UN_le) simp
  also have "... \<le>
      (\<Sum>k \<in> {1..<powers}.
        ((query_sample_space_size - card ?A) + k * scale))"
  proof (rule sum_mono)
    fix k
    assume "k \<in> {1..<powers}"
    show
      "card (?shift_bad k) \<le>
        (query_sample_space_size - card ?A) + k * scale"
      by (rule trace_power_boundary_shift_card_bound)
  qed
  finally show ?thesis .
qed

definition trace_composition_query_index_bound :: nat
where
  "trace_composition_query_index_bound =
    (query_agreement_bound +
      (powers - 1) * query_sample_space_size +
      (\<Sum>k \<in> {1..<powers}. k * scale)) div powers"

lemma trace_composition_accepted_indices_card_le_base_agreement:
  "card (trace_composition_accepted_indices
      original candidate composition as) \<le>
    card (trace_table_base_agreement_indices original candidate)"
proof -
  have subset:
      "trace_composition_accepted_indices original candidate composition as \<subseteq>
        trace_table_base_agreement_indices original candidate"
    unfolding trace_composition_accepted_indices_def by auto
  have finite:
      "finite (trace_table_base_agreement_indices original candidate)"
    unfolding trace_table_base_agreement_indices_def by simp
  show ?thesis by (rule card_mono[OF finite subset])
qed

lemma trace_composition_accepted_indices_card_bound_semantic:
  assumes lengths: "length original = length candidate"
    and trace_low: "trace_table_low_degree candidate"
    and composition_low:
      "composition_table_low_degree maxDegree composition"
    and not_all:
      "\<not> all_queries_consistent candidate composition as"
  shows
    "card (trace_composition_accepted_indices
        original candidate composition as) \<le>
      query_agreement_bound +
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
  have finite_agreement: "finite ?agreement"
    unfolding query_agreement_indices_def query_sample_space_def by simp
  have finite_boundary: "finite ?boundary"
    by (rule finite_subset[
          OF trace_power_boundary_indices_subset_query_sample_space
            finite_query_sample_space])
  have finite_union: "finite (?agreement \<union> ?boundary)"
    using finite_agreement finite_boundary by simp
  have "card ?accepted \<le> card (?agreement \<union> ?boundary)"
    by (rule card_mono[OF finite_union union_subset])
  also have "... \<le> card ?agreement + card ?boundary"
    by (rule card_Un_le)
  also have "... \<le>
      query_agreement_bound +
        (\<Sum>k \<in> {1..<powers}.
          ((query_sample_space_size -
            card (trace_table_base_agreement_indices original candidate)) +
            k * scale))"
    by (rule add_mono)
      (rule query_agreement_indices_card_bound[
        OF trace_low composition_low not_all],
       rule trace_power_boundary_indices_card_bound[
        where original=original and candidate=candidate])
  finally show ?thesis .
qed

lemma trace_composition_accepted_indices_card_bound:
  assumes lengths: "length original = length candidate"
    and trace_low: "trace_table_low_degree candidate"
    and composition_low:
      "composition_table_low_degree maxDegree composition"
    and not_all:
      "\<not> all_queries_consistent candidate composition as"
  shows
    "card (trace_composition_accepted_indices
        original candidate composition as) \<le>
      trace_composition_query_index_bound"
  proof -
  let ?accepted =
    "trace_composition_accepted_indices original candidate composition as"
  let ?A = "trace_table_base_agreement_indices original candidate"
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
        query_agreement_bound +
          (\<Sum>k \<in> {1..<powers}.
            ((query_sample_space_size - card ?A) + k * scale))"
    by (rule trace_composition_accepted_indices_card_bound_semantic[
          OF lengths trace_low composition_low not_all])
  have sum_eq:
      "(\<Sum>k \<in> {1..<powers}.
          ((query_sample_space_size - card ?A) + k * scale)) =
        (powers - 1) * (query_sample_space_size - card ?A) + ?tail"
    by (simp add: sum.distrib mult.commute)
  have accepted_upper:
      "card ?accepted \<le>
        query_agreement_bound +
          (powers - 1) * (query_sample_space_size - card ?A) + ?tail"
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
    have
      "(powers - 1) * card ?A +
          (powers - 1) * (query_sample_space_size - card ?A) =
        (powers - 1) *
          (card ?A + (query_sample_space_size - card ?A))"
      by (simp add: distrib_left)
    also have "... = (powers - 1) * query_sample_space_size"
      using sub_add by (simp add: add.commute)
    finally show ?thesis .
  qed
  have weighted:
      "powers * card ?accepted \<le>
        query_agreement_bound +
          (powers - 1) * query_sample_space_size + ?tail"
  proof -
    have components:
      "(powers - 1) * card ?accepted + card ?accepted \<le>
        (powers - 1) * card ?A +
          (query_agreement_bound +
            (powers - 1) * (query_sample_space_size - card ?A) + ?tail)"
      by (rule add_mono[OF multiplied_base accepted_upper])
    have left_eq:
        "powers * card ?accepted =
          (powers - 1) * card ?accepted + card ?accepted"
      using powers_eq by (metis distrib_right mult_1_left)
    have right_eq:
        "(powers - 1) * card ?A +
          (query_agreement_bound +
            (powers - 1) * (query_sample_space_size - card ?A) + ?tail) =
         query_agreement_bound +
          (powers - 1) * query_sample_space_size + ?tail"
      using partition by arith
    show ?thesis
      using components left_eq right_eq by simp
  qed
  show ?thesis
    unfolding trace_composition_query_index_bound_def
    using powers_pos weighted
    by (simp add: less_eq_div_iff_mult_less_eq mult.commute)
qed


definition query_index_lists_over
where
  "query_index_lists_over indices =
    {query_idxs. length query_idxs = rounds \<and> set query_idxs \<subseteq> indices}"

lemma query_index_lists_over_subset_fri_query_index_list_space:
  assumes subset: "indices \<subseteq> query_sample_space"
  shows "query_index_lists_over indices \<subseteq> fri_query_index_list_space"
  using subset
  unfolding query_index_lists_over_def fri_query_index_list_space_def
  by auto

lemma card_query_index_lists_over:
  assumes finite: "finite indices"
  shows "card (query_index_lists_over indices) = card indices ^ rounds"
  unfolding query_index_lists_over_def
  using card_lists_length_eq[OF finite, of rounds]
  by (simp add: conj.commute)

definition ro_actual_query_trace_composition_accepted_indices
where
  "ro_actual_query_trace_composition_accepted_indices
      prefix prefix_state data query_start =
    trace_composition_accepted_indices
      (conceptual_table prefix_state (staged_trace_root data)
        (scale * clength))
      (first_trace_fri_root_prefix_first_table prefix prefix_state)
      (ro_actual_query_composition_candidate data query_start)
      (staged_alphas data)"

definition ro_actual_query_trace_composition_accepted_query_lists
where
  "ro_actual_query_trace_composition_accepted_query_lists
      prefix prefix_state data query_start =
    query_index_lists_over
      (ro_actual_query_trace_composition_accepted_indices
        prefix prefix_state data query_start)"

lemma
  ro_absorb_checked_staged_first_root_actual_query_trace_composition_indices_or_targets:
  fixes final_state :: "'f protocol_channel"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and builder_out:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and verifier_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and clean: "\<not> hash_map_output_collision final_state"
  shows
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_actual_query_trace_composition_accepted_query_lists
          prefix prefix_state data query_start \<or>
      hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state \<or>
      hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets data query_start)
        query_start final_state"
  proof -
  let ?query_idxs = "map (\<lambda>raw. index (to_nat raw)) raws"
  let ?original =
    "conceptual_table prefix_state (staged_trace_root data)
      (scale * clength)"
  let ?candidate =
    "first_trace_fri_root_prefix_first_table prefix prefix_state"
  let ?composition =
    "ro_actual_query_composition_candidate data query_start"

  have query_length: "length raws = rounds"
    using
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
        OF wf controlled builder_out]
    by blast

  have base_or_target:
      "?query_idxs \<in>
          first_trace_fri_root_prefix_base_agreement_query_lists
            prefix prefix_state \<or>
        hash_map_new_output_hit
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
          prefix_state final_state"
    by (rule
        ro_absorb_checked_staged_first_root_actual_query_base_agreement_or_target[
          OF wf controlled nonempty builder_out verifier_out clean])

  have consistency_or_targets:
      "(\<forall>j < length raws.
        query_consistent_at ?original ?composition (staged_alphas data)
          (index (to_nat (raws ! j)))) \<or>
       hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state \<or>
       hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets data query_start)
        query_start final_state"
    by (rule
        ro_absorb_checked_staged_first_root_actual_query_conceptual_consistency_or_targets[
          OF wf controlled nonempty builder_out verifier_out clean])

  from ro_checked_staged_transcript_program_with_first_root_outcomeE[
      OF builder_out]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
    and after_out:
      "Some (head_data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A prefix)
            prefix_final)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    by blast
  obtain prefix_fr prefix_trace_bs first_root where
    prefix_eq: "prefix = (prefix_fr, prefix_trace_bs, first_root)"
    by (cases prefix) auto
  have after_fields:
      "staged_trace_root head_data = prefix_fr \<and>
       (\<exists>roots. staged_trace_fri_roots head_data = first_root # roots)"
    by (rule ro_checked_staged_after_first_trace_fri_root_prefix_program_fields[
          OF nonempty])
      (use after_out prefix_eq in simp)
  have original_eq:
      "first_trace_fri_root_prefix_trace_table prefix prefix_state =
        ?original"
    using after_fields data_eq
    unfolding prefix_eq first_trace_fri_root_prefix_trace_table_def
    by simp

  show ?thesis
  proof (cases
      "hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state")
    case True
    then show ?thesis by simp
  next
    case no_trace_target: False
    from consistency_or_targets no_trace_target
    have consistency_or_composition_target:
        "(\<forall>j < length raws.
          query_consistent_at ?original ?composition (staged_alphas data)
            (index (to_nat (raws ! j)))) \<or>
         hash_map_new_output_hit
          (ro_actual_query_composition_prefix_targets data query_start)
          query_start final_state"
      by blast
    then show ?thesis
    proof
      assume consistent:
          "\<forall>j < length raws.
            query_consistent_at ?original ?composition (staged_alphas data)
              (index (to_nat (raws ! j)))"
      from base_or_target no_trace_target have base:
          "?query_idxs \<in>
            first_trace_fri_root_prefix_base_agreement_query_lists
              prefix prefix_state"
        by blast
      have base':
          "?query_idxs \<in>
            trace_table_base_agreement_query_lists ?original ?candidate"
        using base original_eq
        unfolding first_trace_fri_root_prefix_base_agreement_query_lists_def
        by simp
      have base_entries:
          "set ?query_idxs \<subseteq>
            trace_table_base_agreement_indices ?original ?candidate"
        using base'
        unfolding trace_table_base_agreement_query_lists_def by blast
      have accepted_entries:
          "set ?query_idxs \<subseteq>
            trace_composition_accepted_indices
              ?original ?candidate ?composition (staged_alphas data)"
      proof
        fix idx
        assume idx_in: "idx \<in> set ?query_idxs"
        then obtain j where j_bound: "j < length raws"
          and idx_eq: "idx = index (to_nat (raws ! j))"
          by (auto simp: in_set_conv_nth)
        have idx_base:
            "idx \<in> trace_table_base_agreement_indices ?original ?candidate"
          using base_entries idx_in by blast
        have idx_consistent:
            "query_consistent_at ?original ?composition
              (staged_alphas data) idx"
          using consistent[rule_format, OF j_bound] idx_eq by simp
        show
          "idx \<in> trace_composition_accepted_indices
            ?original ?candidate ?composition (staged_alphas data)"
          using idx_base idx_consistent
          unfolding trace_composition_accepted_indices_def by simp
      qed
      have query_list:
          "?query_idxs \<in>
            ro_actual_query_trace_composition_accepted_query_lists
              prefix prefix_state data query_start"
        using query_length accepted_entries
        unfolding
          ro_actual_query_trace_composition_accepted_query_lists_def
          ro_actual_query_trace_composition_accepted_indices_def
          query_index_lists_over_def
        by simp
      then show ?thesis by simp
    next
      assume composition_target:
          "hash_map_new_output_hit
            (ro_actual_query_composition_prefix_targets data query_start)
            query_start final_state"
      then show ?thesis by simp
    qed
  qed
qed

lemma ro_actual_query_trace_composition_accepted_indices_subset:
  "ro_actual_query_trace_composition_accepted_indices
      prefix prefix_state data query_start \<subseteq> query_sample_space"
  unfolding ro_actual_query_trace_composition_accepted_indices_def
  by (rule trace_composition_accepted_indices_subset_query_sample_space)

lemma ro_actual_query_trace_composition_accepted_query_lists_subset:
  "ro_actual_query_trace_composition_accepted_query_lists
      prefix prefix_state data query_start \<subseteq> fri_query_index_list_space"
  unfolding ro_actual_query_trace_composition_accepted_query_lists_def
  by (rule query_index_lists_over_subset_fri_query_index_list_space)
    (rule ro_actual_query_trace_composition_accepted_indices_subset)

lemma ro_actual_query_trace_composition_accepted_query_lists_card_bound:
  assumes trace_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)"
    and composition_low:
      "composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate data query_start)"
    and not_all:
      "\<not> all_queries_consistent
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (ro_actual_query_composition_candidate data query_start)
        (staged_alphas data)"
  shows
    "card
      (ro_actual_query_trace_composition_accepted_query_lists
        prefix prefix_state data query_start) \<le>
      trace_composition_query_index_bound ^ rounds"
proof -
  let ?original =
    "conceptual_table prefix_state (staged_trace_root data)
      (scale * clength)"
  let ?candidate =
    "first_trace_fri_root_prefix_first_table prefix prefix_state"
  let ?composition =
    "ro_actual_query_composition_candidate data query_start"
  let ?indices =
    "ro_actual_query_trace_composition_accepted_indices
      prefix prefix_state data query_start"
  have original_len: "length ?original = scale * clength"
    by simp
  have candidate_len: "length ?candidate = scale * clength"
  proof -
    from trace_low obtain f where
      candidate: "?candidate = map (poly f) eval_domain"
      unfolding trace_table_low_degree_def by blast
    show ?thesis
      using candidate eval_domain_length by simp
  qed
  have lengths: "length ?original = length ?candidate"
    using original_len candidate_len by simp
  have indices_bound:
      "card ?indices \<le> trace_composition_query_index_bound"
    unfolding ro_actual_query_trace_composition_accepted_indices_def
    by (rule trace_composition_accepted_indices_card_bound[
          OF lengths trace_low composition_low not_all])
  have finite_indices: "finite ?indices"
    by (rule finite_subset[
          OF ro_actual_query_trace_composition_accepted_indices_subset
            finite_query_sample_space])
  have card_lists:
      "card
        (ro_actual_query_trace_composition_accepted_query_lists
          prefix prefix_state data query_start) =
        card ?indices ^ rounds"
    unfolding ro_actual_query_trace_composition_accepted_query_lists_def
    by (rule card_query_index_lists_over[OF finite_indices])
  show ?thesis
    unfolding card_lists
    by (rule power_mono[OF indices_bound]) simp
qed


end
end
