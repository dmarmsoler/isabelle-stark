theory Soundness_FRI_Conditioned_Explicit_Adaptive_Rectangles
  imports
    Stark.Soundness_FRI_Conditioned_Residual_Adaptive_Rectangle_Products
    Stark.Soundness_FRI_Conditioned_Explicit_Complete_List_Adaptive_Products
begin

context soundness
begin

definition ro_actual_query_trace_composition_good_query_indices
where
  "ro_actual_query_trace_composition_good_query_indices
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
       ro_actual_query_trace_composition_accepted_indices
         prefix prefix_state data query_start
     else {})"

lemma ro_actual_query_trace_composition_good_query_lists_rectangle_cover:
  "ro_actual_query_trace_composition_good_query_lists
      prefix prefix_state data query_start
    \<subseteq> fri_conditioned_query_lists
      (ro_actual_query_trace_composition_good_query_indices
        prefix prefix_state data query_start)"
  unfolding
    ro_actual_query_trace_composition_good_query_lists_def
    ro_actual_query_trace_composition_good_query_indices_def
    ro_actual_query_trace_composition_accepted_query_lists_def
    query_index_lists_over_def fri_conditioned_query_lists_def
  by auto

lemma ro_actual_query_trace_composition_good_query_indices_subset:
  "ro_actual_query_trace_composition_good_query_indices
      prefix prefix_state data query_start
    \<subseteq> query_sample_space"
  unfolding ro_actual_query_trace_composition_good_query_indices_def
  using ro_actual_query_trace_composition_accepted_indices_subset[
    of prefix prefix_state data query_start]
  by auto

lemma card_ro_actual_query_trace_composition_good_query_indices:
  "card
      (ro_actual_query_trace_composition_good_query_indices
        prefix prefix_state data query_start)
    \<le> trace_composition_query_index_bound"
proof (cases
    "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
     composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate data query_start) \<and>
     \<not> all_queries_consistent
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (ro_actual_query_composition_candidate data query_start)
        (staged_alphas data)")
  case True
  then have trace_low:
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
    by blast+
  show ?thesis
    unfolding ro_actual_query_trace_composition_good_query_indices_def
      if_P[OF True]
    by (rule
        ro_actual_query_trace_composition_accepted_indices_card_bound[
          OF trace_low composition_low not_all])
next
  case False
  show ?thesis
    unfolding ro_actual_query_trace_composition_good_query_indices_def
      if_not_P[OF False]
    by simp
qed

definition
  ro_checked_staged_trace_composition_good_actual_query_rectangle_error_adaptive
    :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_trace_composition_good_actual_query_rectangle_error_adaptive
      budgets =
    (nnreal
        (query_raw_preimage_card_envelope
          trace_composition_query_index_bound) /
      nnreal size) ^
    (rounds - staged_attacker_query_budget budgets)"

lemma
  wp_ro_checked_staged_trace_composition_good_actual_query_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_trace_composition_good_query_lists)
      adversary_initial_state
    \<le>
    ro_checked_staged_trace_composition_good_actual_query_rectangle_error_adaptive
      budgets"
  unfolding
    ro_checked_staged_trace_composition_good_actual_query_rectangle_error_adaptive_def
proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_bound[
      OF wf controlled,
      where
        I=ro_actual_query_trace_composition_good_query_indices])
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "ro_actual_query_trace_composition_good_query_lists
        prefix prefix_state data query_start
      \<subseteq>
      fri_conditioned_query_lists
        (ro_actual_query_trace_composition_good_query_indices
          prefix prefix_state data query_start)"
    by (rule
        ro_actual_query_trace_composition_good_query_lists_rectangle_cover)
next
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "ro_actual_query_trace_composition_good_query_indices
        prefix prefix_state data query_start
      \<subseteq> query_sample_space"
    by (rule ro_actual_query_trace_composition_good_query_indices_subset)
next
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "card
      (ro_actual_query_trace_composition_good_query_indices
        prefix prefix_state data query_start)
      \<le> trace_composition_query_index_bound"
    by (rule card_ro_actual_query_trace_composition_good_query_indices)
qed

definition ro_trace_composition_padding_query_head_indices
where
  "ro_trace_composition_padding_query_head_indices
      prefix prefix_state data query_start =
    (if to_nat (staged_degree data) \<le> maxDegree then
      if
        trace_table_low_degree
          (first_trace_fri_root_prefix_first_table prefix prefix_state) \<and>
        composition_table_low_degree
          (fri_padded_degree_bound (to_nat (staged_degree data)))
          (ro_actual_query_composition_candidate data query_start) \<and>
        \<not> composition_table_low_degree maxDegree
          (ro_actual_query_composition_candidate data query_start)
      then
        trace_composition_accepted_indices
          (conceptual_table prefix_state (staged_trace_root data)
            (scale * clength))
          (first_trace_fri_root_prefix_first_table prefix prefix_state)
          (ro_actual_query_composition_candidate data query_start)
          (staged_alphas data)
      else {}
     else {})"

lemma ro_trace_composition_padding_query_head_lists_rectangle_cover:
  "ro_trace_composition_padding_query_head_lists
      prefix prefix_state data query_start
    \<subseteq> fri_conditioned_query_lists
      (ro_trace_composition_padding_query_head_indices
        prefix prefix_state data query_start)"
  unfolding
    ro_trace_composition_padding_query_head_lists_def
    ro_trace_composition_padding_query_head_indices_def
    trace_composition_padding_query_lists_def
    query_index_lists_over_def fri_conditioned_query_lists_def
  by auto

lemma ro_trace_composition_padding_query_head_indices_subset:
  "ro_trace_composition_padding_query_head_indices
      prefix prefix_state data query_start
    \<subseteq> query_sample_space"
  unfolding ro_trace_composition_padding_query_head_indices_def
  using trace_composition_accepted_indices_subset_query_sample_space[
    of
      "conceptual_table prefix_state (staged_trace_root data)
        (scale * clength)"
      "first_trace_fri_root_prefix_first_table prefix prefix_state"
      "ro_actual_query_composition_candidate data query_start"
      "staged_alphas data"]
  by auto

lemma card_ro_trace_composition_padding_query_head_indices:
  "card
      (ro_trace_composition_padding_query_head_indices
        prefix prefix_state data query_start)
    \<le> trace_composition_padding_query_index_bound"
proof (cases "to_nat (staged_degree data) \<le> maxDegree")
  case degree_bound: True
  let ?original =
    "conceptual_table prefix_state (staged_trace_root data)
      (scale * clength)"
  let ?candidate =
    "first_trace_fri_root_prefix_first_table prefix prefix_state"
  let ?composition =
    "ro_actual_query_composition_candidate data query_start"
  let ?d = "to_nat (staged_degree data)"
  show ?thesis
  proof (cases
      "trace_table_low_degree ?candidate \<and>
       composition_table_low_degree (fri_padded_degree_bound ?d)
         ?composition \<and>
       \<not> composition_table_low_degree maxDegree ?composition")
    case active: True
    then have trace_low: "trace_table_low_degree ?candidate"
      and composition_low:
        "composition_table_low_degree (fri_padded_degree_bound ?d)
          ?composition"
      and composition_bad:
        "\<not> composition_table_low_degree maxDegree ?composition"
      by blast+
    have lengths: "length ?original = length ?candidate"
    proof -
      obtain fr xs first_root where prefix_eq:
        "prefix = (fr, xs, first_root)"
        by (cases prefix) auto
      show ?thesis
        unfolding prefix_eq first_trace_fri_root_prefix_first_table_def
        by simp
    qed
    have local:
      "card
        (trace_composition_accepted_indices
          ?original ?candidate ?composition (staged_alphas data))
       \<le> trace_composition_query_index_bound_for
          (fri_padded_degree_bound ?d)"
      by (rule trace_composition_accepted_indices_card_bound_for[
            OF lengths trace_low composition_low composition_bad])
    have mono:
      "trace_composition_query_index_bound_for
          (fri_padded_degree_bound ?d)
       \<le> trace_composition_padding_query_index_bound"
      by (rule trace_composition_padding_query_index_bound_mono[
            OF degree_bound])
    show ?thesis
      unfolding ro_trace_composition_padding_query_head_indices_def
        if_P[OF degree_bound] if_P[OF active]
      by (rule order_trans[OF local mono])
  next
    case active: False
    show ?thesis
      unfolding ro_trace_composition_padding_query_head_indices_def
        if_P[OF degree_bound] if_not_P[OF active]
      by simp
  qed
next
  case degree_bound: False
  show ?thesis
    unfolding ro_trace_composition_padding_query_head_indices_def
      if_not_P[OF degree_bound]
    by simp
qed

definition
  ro_checked_staged_trace_composition_padding_rectangle_error_adaptive
    :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_trace_composition_padding_rectangle_error_adaptive
      budgets =
    (nnreal
        (query_raw_preimage_card_envelope
          trace_composition_padding_query_index_bound) /
      nnreal size) ^
    (rounds - staged_attacker_query_budget budgets)"

lemma
  wp_ro_checked_staged_trace_composition_padding_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_actual_query_index_list_hit
        ro_trace_composition_padding_query_head_lists)
      adversary_initial_state
    \<le>
    ro_checked_staged_trace_composition_padding_rectangle_error_adaptive
      budgets"
  unfolding
    ro_checked_staged_trace_composition_padding_rectangle_error_adaptive_def
proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_bound[
      OF wf controlled,
      where I=ro_trace_composition_padding_query_head_indices])
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "ro_trace_composition_padding_query_head_lists
        prefix prefix_state data query_start
      \<subseteq> fri_conditioned_query_lists
        (ro_trace_composition_padding_query_head_indices
          prefix prefix_state data query_start)"
    by (rule ro_trace_composition_padding_query_head_lists_rectangle_cover)
next
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "ro_trace_composition_padding_query_head_indices
        prefix prefix_state data query_start
      \<subseteq> query_sample_space"
    by (rule ro_trace_composition_padding_query_head_indices_subset)
next
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "card
      (ro_trace_composition_padding_query_head_indices
        prefix prefix_state data query_start)
      \<le> trace_composition_padding_query_index_bound"
    by (rule card_ro_trace_composition_padding_query_head_indices)
qed

end
end
