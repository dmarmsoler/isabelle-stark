theory Soundness_FRI_Conditioned_Explicit_Complete_List_Adaptive_Products
  imports
    Soundness_FRI_Query_Head_Adaptive_Actual_Product
    Soundness_FRI_Conditioned_Explicit_Complete_List_Security_Classification
    Soundness_FRI_Conditioned_Explicit_Complete_List_Good_Query_Zero
begin

context soundness
begin

definition
  ro_checked_staged_conditioned_complete_list_actual_residual_error_adaptive
    :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_complete_list_actual_residual_error_adaptive
      budgets =
    nnreal
      (fri_conditioned_residual_query_list_card_bound (clength - 1) +
       fri_conditioned_residual_query_list_card_bound maxDegree) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^
        (rounds - staged_attacker_query_budget budgets)"

lemma
  wp_ro_checked_staged_combined_conditioned_residual_actual_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_combined_query_head_lists)
      adversary_initial_state
    \<le>
    ro_checked_staged_conditioned_complete_list_actual_residual_error_adaptive
      budgets"
  unfolding
    ro_checked_staged_conditioned_complete_list_actual_residual_error_adaptive_def
proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_bound[
      OF wf controlled])
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "fri_conditioned_combined_query_head_lists
        prefix prefix_state data query_start
      \<subseteq> fri_query_index_list_space"
    by (rule fri_conditioned_combined_query_head_lists_subset)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (Suc (to_nat (staged_degree data))) \<and>
       length (staged_composition_fri_challenges data) =
         ceil_log (Suc (to_nat (staged_degree data)))"
    by (rule
        ro_checked_staged_first_root_query_head_program_output_fri_lengths[
          OF head])
  show
    "card
      (fri_conditioned_combined_query_head_lists
        prefix prefix_state data query_start) \<le>
      fri_conditioned_residual_query_list_card_bound (clength - 1) +
        fri_conditioned_residual_query_list_card_bound maxDegree"
    by (rule card_fri_conditioned_combined_query_head_lists)
      (use shape in simp_all)
qed

lemma
  wp_ro_absorb_checked_staged_security_combined_conditioned_residual_actual_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_combined_query_head_lists)
      adversary_initial_state
    \<le>
    ro_checked_staged_conditioned_complete_list_actual_residual_error_adaptive
      budgets"
  by (rule order_trans[
    OF
      wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
      wp_ro_checked_staged_combined_conditioned_residual_actual_bound_adaptive[
        OF wf controlled]])



definition
  ro_checked_staged_trace_composition_complete_list_good_actual_query_error_adaptive
    :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_trace_composition_complete_list_good_actual_query_error_adaptive
      budgets =
    nnreal (trace_composition_query_index_bound ^ rounds) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^
        (rounds - staged_attacker_query_budget budgets)"

lemma
  wp_ro_checked_staged_trace_composition_complete_list_good_actual_query_bound_adaptive:
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
    ro_checked_staged_trace_composition_complete_list_good_actual_query_error_adaptive
      budgets"
  unfolding
    ro_checked_staged_trace_composition_complete_list_good_actual_query_error_adaptive_def
proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_bound[
      OF wf controlled])
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
      \<subseteq> fri_query_index_list_space"
    by (rule ro_actual_query_trace_composition_good_query_lists_subset)
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
      (ro_actual_query_trace_composition_good_query_lists
        prefix prefix_state data query_start) \<le>
      trace_composition_query_index_bound ^ rounds"
    by (rule
        ro_actual_query_trace_composition_good_query_lists_card_bound)
qed

lemma
  wp_ro_absorb_checked_staged_security_trace_composition_complete_list_good_actual_query_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_trace_composition_good_query_lists)
      adversary_initial_state
    \<le>
    ro_checked_staged_trace_composition_complete_list_good_actual_query_error_adaptive
      budgets"
  by (rule order_trans[
    OF
      wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
      wp_ro_checked_staged_trace_composition_complete_list_good_actual_query_bound_adaptive[
        OF wf controlled]])


definition
  ro_checked_staged_trace_composition_complete_list_padding_error_adaptive
    :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_trace_composition_complete_list_padding_error_adaptive
      budgets =
    nnreal (trace_composition_padding_query_index_bound ^ rounds) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^
        (rounds - staged_attacker_query_budget budgets)"

lemma
  wp_ro_checked_staged_trace_composition_complete_list_padding_bound_adaptive:
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
    ro_checked_staged_trace_composition_complete_list_padding_error_adaptive
      budgets"
  unfolding
    ro_checked_staged_trace_composition_complete_list_padding_error_adaptive_def
proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_bound[
      OF wf controlled])
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
      \<subseteq> fri_query_index_list_space"
    by (rule ro_trace_composition_padding_query_head_lists_subset)
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
      (ro_trace_composition_padding_query_head_lists
        prefix prefix_state data query_start) \<le>
      trace_composition_padding_query_index_bound ^ rounds"
    by (rule card_ro_trace_composition_padding_query_head_lists)
qed

lemma
  wp_ro_absorb_checked_staged_security_trace_composition_complete_list_padding_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        ro_trace_composition_padding_query_head_lists)
      adversary_initial_state
    \<le>
    ro_checked_staged_trace_composition_complete_list_padding_error_adaptive
      budgets"
  by (rule order_trans[
    OF
      wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
      wp_ro_checked_staged_trace_composition_complete_list_padding_bound_adaptive[
        OF wf controlled]])
end
end
