theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Query_Bound
  imports
    Soundness_FRI_RO_Query_Head_Dependent_Product
    Soundness_FRI_Prechallenge_Query_Product
begin

context soundness
begin

lemma query_index_raw_list_position_values_query_index_lists_over_subset:
  assumes i_bound: "i < rounds"
  shows
    "query_index_raw_list_position_values (query_index_lists_over indices) i
      \<subseteq> query_index_raw_preimage indices"
proof
  fix raw
  assume raw_in:
    "raw \<in>
      query_index_raw_list_position_values (query_index_lists_over indices) i"
  from raw_in obtain raws where
    raws_in:
      "raws \<in> query_index_raw_list_preimage (query_index_lists_over indices)"
    and raw_eq: "raw = raws ! i"
    unfolding query_index_raw_list_position_values_def
    using i_bound by blast
  have raws_len: "length raws = rounds"
    and mapped_in:
      "map (\<lambda>x. index (to_nat x)) raws \<in> query_index_lists_over indices"
    using raws_in
    unfolding query_index_raw_list_preimage_def by blast+
  have mapped_subset:
      "set (map (\<lambda>x. index (to_nat x)) raws) \<subseteq> indices"
    using mapped_in unfolding query_index_lists_over_def by blast
  have i_len: "i < length raws"
    using i_bound raws_len by simp
  have mapped_nth:
      "map (\<lambda>x. index (to_nat x)) raws ! i = index (to_nat raw)"
    using raw_eq i_len by simp
  have mapped_mem:
      "map (\<lambda>x. index (to_nat x)) raws ! i \<in>
        set (map (\<lambda>x. index (to_nat x)) raws)"
    by (rule nth_mem) (use i_len in simp)
  have "index (to_nat raw) \<in> indices"
    by (rule set_mp[OF mapped_subset])
      (use mapped_mem mapped_nth in simp)
  then show "raw \<in> query_index_raw_preimage indices"
    unfolding query_index_raw_preimage_def by simp
qed

lemma query_index_raw_list_relation_fiber_bound_query_index_lists_over:
  assumes subset: "indices \<subseteq> query_sample_space"
  shows
    "query_index_raw_list_relation_fiber_bound
        (query_index_lists_over indices)
      \<le> rounds * query_raw_preimage_card_envelope (card indices)"
proof -
  have per_position:
      "\<And>i. i < rounds \<Longrightarrow>
        card
          (query_index_raw_list_position_values
            (query_index_lists_over indices) i)
        \<le> query_raw_preimage_card_envelope (card indices)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have pos_subset:
        "query_index_raw_list_position_values
            (query_index_lists_over indices) i
          \<subseteq> query_index_raw_preimage indices"
      by (rule
          query_index_raw_list_position_values_query_index_lists_over_subset[
            OF i_bound])
    have card_le:
        "card
          (query_index_raw_list_position_values
            (query_index_lists_over indices) i)
          \<le> card (query_index_raw_preimage indices)"
      by (rule card_mono[OF _ pos_subset]) simp
    have raw_card:
        "card (query_index_raw_preimage indices) \<le>
          query_raw_preimage_card_envelope (card indices)"
      by (rule card_query_index_raw_preimage_le_query_envelope[OF subset])
    show
      "card
        (query_index_raw_list_position_values
          (query_index_lists_over indices) i)
        \<le> query_raw_preimage_card_envelope (card indices)"
      by (rule order_trans[OF card_le raw_card])
  qed
  have
    "(\<Sum>i<rounds.
      card
        (query_index_raw_list_position_values
          (query_index_lists_over indices) i))
      \<le>
     (\<Sum>i<rounds.
      query_raw_preimage_card_envelope (card indices))"
    by (rule sum_mono) (auto intro: per_position)
  then show ?thesis
    unfolding query_index_raw_list_relation_fiber_bound_def
    by simp
qed

definition
  ro_actual_query_trace_composition_good_query_lists
where
  "ro_actual_query_trace_composition_good_query_lists
      prefix prefix_state data query_start =
    (if
      trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
      composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate data query_start) \<and>
      \<not> all_queries_consistent
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (ro_actual_query_composition_candidate data query_start)
        (staged_alphas data)
     then
       ro_actual_query_trace_composition_accepted_query_lists
         prefix prefix_state data query_start
     else {})"

lemma ro_actual_query_trace_composition_good_query_lists_subset:
  "ro_actual_query_trace_composition_good_query_lists
      prefix prefix_state data query_start
    \<subseteq> fri_query_index_list_space"
  unfolding ro_actual_query_trace_composition_good_query_lists_def
  using ro_actual_query_trace_composition_accepted_query_lists_subset[
    of prefix prefix_state data query_start]
  by auto

lemma ro_actual_query_trace_composition_good_query_lists_card_bound:
  "card
      (ro_actual_query_trace_composition_good_query_lists
        prefix prefix_state data query_start)
    \<le> trace_composition_query_index_bound ^ rounds"
  unfolding ro_actual_query_trace_composition_good_query_lists_def
  by (auto intro:
    ro_actual_query_trace_composition_accepted_query_lists_card_bound)


lemma ro_actual_query_trace_composition_accepted_indices_card_bound:
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
      (ro_actual_query_trace_composition_accepted_indices
        prefix prefix_state data query_start)
      \<le> trace_composition_query_index_bound"
proof -
  let ?original =
    "conceptual_table prefix_state (staged_trace_root data)
      (scale * clength)"
  let ?candidate =
    "first_trace_fri_root_prefix_first_table prefix prefix_state"
  let ?composition =
    "ro_actual_query_composition_candidate data query_start"
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
  show ?thesis
    unfolding ro_actual_query_trace_composition_accepted_indices_def
    by (rule trace_composition_accepted_indices_card_bound[
          OF lengths trace_low composition_low not_all])
qed

lemma ro_actual_query_trace_composition_good_query_lists_relation_fiber_bound:
  "query_index_raw_list_relation_fiber_bound
      (ro_actual_query_trace_composition_good_query_lists
        prefix prefix_state data query_start)
    \<le> rounds *
      query_raw_preimage_card_envelope
        trace_composition_query_index_bound"
proof -
  let ?good =
    "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
      composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate data query_start) \<and>
      \<not> all_queries_consistent
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (ro_actual_query_composition_candidate data query_start)
        (staged_alphas data)"
  show ?thesis
  proof (cases ?good)
    case True
    let ?indices =
      "ro_actual_query_trace_composition_accepted_indices
        prefix prefix_state data query_start"
    have family_eq:
        "ro_actual_query_trace_composition_good_query_lists
            prefix prefix_state data query_start =
          query_index_lists_over ?indices"
      using True
      unfolding
        ro_actual_query_trace_composition_good_query_lists_def
        ro_actual_query_trace_composition_accepted_query_lists_def
      by simp
    have base:
        "query_index_raw_list_relation_fiber_bound
            (query_index_lists_over ?indices)
          \<le> rounds *
            query_raw_preimage_card_envelope (card ?indices)"
      by (rule
          query_index_raw_list_relation_fiber_bound_query_index_lists_over)
        (rule ro_actual_query_trace_composition_accepted_indices_subset)
    have indices_bound:
        "card ?indices \<le> trace_composition_query_index_bound"
      by (rule
          ro_actual_query_trace_composition_accepted_indices_card_bound)
        (use True in blast)+
    have envelope_bound:
        "query_raw_preimage_card_envelope (card ?indices) \<le>
          query_raw_preimage_card_envelope
            trace_composition_query_index_bound"
      by (rule query_raw_preimage_card_envelope_mono[OF indices_bound])
    have mono:
        "rounds * query_raw_preimage_card_envelope (card ?indices)
          \<le> rounds *
            query_raw_preimage_card_envelope
              trace_composition_query_index_bound"
      using envelope_bound by simp
    show ?thesis
      unfolding family_eq
      by (rule order_trans[OF base mono])
  next
    case False
    have family_eq:
        "ro_actual_query_trace_composition_good_query_lists
            prefix prefix_state data query_start = {}"
      unfolding ro_actual_query_trace_composition_good_query_lists_def
      by (rule if_not_P) (use False in blast)
    show ?thesis
      unfolding family_eq query_index_raw_list_relation_fiber_bound_def
        query_index_raw_list_position_values_def
        query_index_raw_list_preimage_def
      by simp
  qed
qed


lemma ro_actual_query_trace_composition_good_query_lists_memberD:
  assumes member:
    "query_idxs \<in>
      ro_actual_query_trace_composition_good_query_lists
        prefix prefix_state data query_start"
  shows
    "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
     composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate data query_start) \<and>
     \<not> all_queries_consistent
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (ro_actual_query_composition_candidate data query_start)
        (staged_alphas data) \<and>
     query_idxs \<in>
       ro_actual_query_trace_composition_accepted_query_lists
         prefix prefix_state data query_start"
  using member
  unfolding ro_actual_query_trace_composition_good_query_lists_def
  by (auto split: if_splits)

lemma wp_ro_actual_query_trace_composition_good_fresh_bound:
  "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_query_index_list_fresh_hit
        ro_actual_query_trace_composition_good_query_lists)
      s
    \<le> nnreal (trace_composition_query_index_bound ^ rounds) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof (rule
    wp_ro_checked_staged_transcript_query_head_dependent_fresh_bound)
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  show
    "ro_actual_query_trace_composition_good_query_lists
        prefix prefix_state data query_start
      \<subseteq> fri_query_index_list_space"
    by (rule ro_actual_query_trace_composition_good_query_lists_subset)
next
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  show
    "card
      (ro_actual_query_trace_composition_good_query_lists
        prefix prefix_state data query_start)
      \<le> trace_composition_query_index_bound ^ rounds"
    by (rule ro_actual_query_trace_composition_good_query_lists_card_bound)
qed

lemma wp_ro_actual_query_trace_composition_good_query_phase_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_query_phase_relation_hit A
        ro_actual_query_trace_composition_good_query_lists)
      adversary_initial_state
    \<le> hash_relation_budget_value
      (rounds *
        query_raw_preimage_card_envelope
          trace_composition_query_index_bound)
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)"
proof (rule
    wp_ro_query_head_dependent_query_phase_relation_hit_bound[
      OF wf controlled])
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "query_index_raw_list_relation_fiber_bound
      (ro_actual_query_trace_composition_good_query_lists
        prefix prefix_state data query_start)
      \<le> rounds *
        query_raw_preimage_card_envelope
          trace_composition_query_index_bound"
    by (rule
        ro_actual_query_trace_composition_good_query_lists_relation_fiber_bound)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show "length (staged_trace_fri_roots data) = ceil_log clength"
    using ro_checked_staged_first_root_query_head_program_output_lengths[
      OF nonempty head]
    by blast
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "length (staged_composition_fri_roots data)
      \<le> ceil_log (maxDegree + 1)"
    using ro_checked_staged_first_root_query_head_program_output_lengths[
      OF nonempty head]
    by blast
qed

lemma wp_ro_actual_query_trace_composition_good_actual_query_split_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_trace_composition_good_query_lists)
      adversary_initial_state
    \<le>
      nnreal (trace_composition_query_index_bound ^ rounds) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds +
      wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (ro_query_head_dependent_query_start_prequery_hit
          ro_actual_query_trace_composition_good_query_lists)
        adversary_initial_state +
      hash_relation_budget_value
        (rounds *
          query_raw_preimage_card_envelope
            trace_composition_query_index_bound)
        (sum_list (query_opening_budgets budgets) + rounds +
          rounds * ro_checked_query_round_transcript_bound)"
proof -
  have split:
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (ro_query_head_dependent_actual_query_index_list_hit
          ro_actual_query_trace_composition_good_query_lists)
        adversary_initial_state
      \<le>
      wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_query_head_dependent_query_index_list_fresh_hit
            ro_actual_query_trace_composition_good_query_lists)
          adversary_initial_state +
        wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_query_head_dependent_query_start_prequery_hit
            ro_actual_query_trace_composition_good_query_lists)
          adversary_initial_state +
        wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_query_head_dependent_query_phase_relation_hit A
            ro_actual_query_trace_composition_good_query_lists)
          adversary_initial_state"
    by (rule
        wp_ro_query_head_dependent_actual_query_index_list_hit_split[
          OF wf controlled])
  have fresh:
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (ro_query_head_dependent_query_index_list_fresh_hit
          ro_actual_query_trace_composition_good_query_lists)
        adversary_initial_state
      \<le> nnreal (trace_composition_query_index_bound ^ rounds) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule wp_ro_actual_query_trace_composition_good_fresh_bound)
  have relation:
    "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A)
        (ro_query_head_dependent_query_phase_relation_hit A
          ro_actual_query_trace_composition_good_query_lists)
        adversary_initial_state
      \<le> hash_relation_budget_value
        (rounds *
          query_raw_preimage_card_envelope
            trace_composition_query_index_bound)
        (sum_list (query_opening_budgets budgets) + rounds +
          rounds * ro_checked_query_round_transcript_bound)"
    by (rule
        wp_ro_actual_query_trace_composition_good_query_phase_relation_bound[
          OF wf controlled nonempty])
  show ?thesis
  proof (rule order_trans[OF split])
    show
      "wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_query_head_dependent_query_index_list_fresh_hit
            ro_actual_query_trace_composition_good_query_lists)
          adversary_initial_state +
        wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_query_head_dependent_query_start_prequery_hit
            ro_actual_query_trace_composition_good_query_lists)
          adversary_initial_state +
        wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_query_head_dependent_query_phase_relation_hit A
            ro_actual_query_trace_composition_good_query_lists)
          adversary_initial_state
        \<le>
        nnreal (trace_composition_query_index_bound ^ rounds) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds +
        wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_query_head_dependent_query_start_prequery_hit
            ro_actual_query_trace_composition_good_query_lists)
          adversary_initial_state +
        hash_relation_budget_value
          (rounds *
            query_raw_preimage_card_envelope
              trace_composition_query_index_bound)
          (sum_list (query_opening_budgets budgets) + rounds +
            rounds * ro_checked_query_round_transcript_bound)"
      by (rule add_mono)
        (rule add_mono[OF fresh order_refl], rule relation)
  qed
qed

end
end
