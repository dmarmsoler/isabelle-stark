theory Soundness_FRI_Robust_Balanced_Selected_Actual_Query
  imports Stark.Soundness_FRI_Robust_Balanced_Selected_Residual
begin

context soundness
begin

lemma fri_balanced_selected_residual_index_card_bound_mono:
  assumes "d \<le> D"
  shows
    "fri_balanced_selected_residual_index_card_bound d C \<le>
      fri_balanced_selected_residual_index_card_bound D C"
proof -
  have log_le: "ceil_log (Suc d) \<le> ceil_log (Suc D)"
    by (rule ceil_log_mono) (use assms in simp)
  show ?thesis
    unfolding fri_balanced_selected_residual_index_card_bound_def
    by (rule Max_mono) (use log_le in auto)
qed

definition fri_balanced_selected_trace_residual_query_lists
  :: "nat \<Rightarrow> 'f staged_proof_data \<Rightarrow>
    'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_balanced_selected_trace_residual_query_lists C data query_start =
    fri_balanced_selected_residual_query_lists
      (clength - 1) C
      (staged_trace_fri_roots data)
      (staged_trace_fri_challenges data)
      (staged_trace_final data) query_start"

definition fri_balanced_selected_composition_residual_query_lists
  :: "nat \<Rightarrow> 'f staged_proof_data \<Rightarrow>
    'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_balanced_selected_composition_residual_query_lists C data query_start =
    (if to_nat (staged_degree data) \<le> maxDegree then
      fri_balanced_selected_residual_query_lists
        (to_nat (staged_degree data)) C
        (staged_composition_fri_roots data)
        (staged_composition_fri_challenges data)
        (staged_composition_final data) query_start
     else {})"

definition fri_balanced_selected_trace_query_head_lists
  :: "nat \<Rightarrow> ('f \<times> 'f list \<times> 'f) \<Rightarrow>
    'f protocol_channel \<Rightarrow> 'f staged_proof_data \<Rightarrow>
    'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_balanced_selected_trace_query_head_lists C
      prefix prefix_state data query_start =
    fri_balanced_selected_trace_residual_query_lists C data query_start"

definition fri_balanced_selected_composition_query_head_lists
  :: "nat \<Rightarrow> ('f \<times> 'f list \<times> 'f) \<Rightarrow>
    'f protocol_channel \<Rightarrow> 'f staged_proof_data \<Rightarrow>
    'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_balanced_selected_composition_query_head_lists C
      prefix prefix_state data query_start =
    fri_balanced_selected_composition_residual_query_lists C data query_start"

definition fri_balanced_selected_combined_query_head_lists
  :: "nat \<Rightarrow> ('f \<times> 'f list \<times> 'f) \<Rightarrow>
    'f protocol_channel \<Rightarrow> 'f staged_proof_data \<Rightarrow>
    'f protocol_channel \<Rightarrow> nat list set"
where
  "fri_balanced_selected_combined_query_head_lists C
      prefix prefix_state data query_start =
    fri_balanced_selected_trace_query_head_lists C
        prefix prefix_state data query_start \<union>
      fri_balanced_selected_composition_query_head_lists C
        prefix prefix_state data query_start"

definition ro_checked_staged_balanced_selected_residual_rectangle_error_adaptive
  :: "nat \<Rightarrow> nat \<Rightarrow> staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_balanced_selected_residual_rectangle_error_adaptive
      d C budgets =
    (nnreal
        (query_raw_preimage_card_envelope
          (fri_balanced_selected_residual_index_card_bound d C)) /
      nnreal size) ^
    (rounds - staged_attacker_query_budget budgets)"

lemma wp_ro_checked_staged_trace_balanced_selected_residual_actual_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit
        (fri_balanced_selected_trace_query_head_lists C))
      adversary_initial_state
    \<le> ro_checked_staged_balanced_selected_residual_rectangle_error_adaptive
        (clength - 1) C budgets"
  unfolding
    ro_checked_staged_balanced_selected_residual_rectangle_error_adaptive_def
proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_bound[
      OF wf controlled,
      where
        I="\<lambda>prefix prefix_state data query_start.
          fri_balanced_selected_residual_query_indices (clength - 1) C
            (staged_trace_fri_roots data)
            (staged_trace_fri_challenges data)
            (staged_trace_final data) query_start"])
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength"
    using
      ro_checked_staged_first_root_query_head_program_output_fri_lengths[
        OF head]
    by blast
  have roots_le: "length (staged_trace_fri_roots data) \<le> N"
    using shape trace_rounds_fit by linarith
  have lengths:
      "length (staged_trace_fri_challenges data) =
        length (staged_trace_fri_roots data)"
    using shape by simp
  show
    "fri_balanced_selected_trace_query_head_lists C
        prefix prefix_state data query_start
      \<subseteq> fri_conditioned_query_lists
        (fri_balanced_selected_residual_query_indices (clength - 1) C
          (staged_trace_fri_roots data)
          (staged_trace_fri_challenges data)
          (staged_trace_final data) query_start)"
    unfolding fri_balanced_selected_trace_query_head_lists_def
      fri_balanced_selected_trace_residual_query_lists_def
    by (rule fri_balanced_selected_residual_query_lists_rectangle_cover[
          OF eval_power roots_le lengths])
next
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "fri_balanced_selected_residual_query_indices (clength - 1) C
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        (staged_trace_final data) query_start
      \<subseteq> query_sample_space"
    by (rule fri_balanced_selected_residual_query_indices_subset)
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
       length (staged_trace_fri_challenges data) = ceil_log clength"
    using
      ro_checked_staged_first_root_query_head_program_output_fri_lengths[
        OF head]
    by blast
  have round_count:
      "length (staged_trace_fri_challenges data) =
        ceil_log (Suc (clength - 1))"
    using shape clength_pos by simp
  have rounds_fit:
      "Suc (length (staged_trace_fri_challenges data)) \<le> N"
    using shape trace_rounds_fit by simp
  have lengths:
      "length (staged_trace_fri_challenges data) =
        length (staged_trace_fri_roots data)"
    using shape by simp
  show
    "card
      (fri_balanced_selected_residual_query_indices (clength - 1) C
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        (staged_trace_final data) query_start)
      \<le> fri_balanced_selected_residual_index_card_bound (clength - 1) C"
    by (rule card_fri_balanced_selected_residual_query_indices[
          OF eval_power round_count rounds_fit lengths])
qed



lemma wp_ro_checked_staged_composition_balanced_selected_residual_actual_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit
        (fri_balanced_selected_composition_query_head_lists C))
      adversary_initial_state
    \<le> ro_checked_staged_balanced_selected_residual_rectangle_error_adaptive
        maxDegree C budgets"
  unfolding
    ro_checked_staged_balanced_selected_residual_rectangle_error_adaptive_def
proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_bound[
      OF wf controlled,
      where
        I="\<lambda>prefix prefix_state data query_start.
          if to_nat (staged_degree data) \<le> maxDegree then
            fri_balanced_selected_residual_query_indices
              (to_nat (staged_degree data)) C
              (staged_composition_fri_roots data)
              (staged_composition_fri_challenges data)
              (staged_composition_final data) query_start
          else {}"])
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "fri_balanced_selected_composition_query_head_lists C
        prefix prefix_state data query_start
      \<subseteq> fri_conditioned_query_lists
        (if to_nat (staged_degree data) \<le> maxDegree then
          fri_balanced_selected_residual_query_indices
            (to_nat (staged_degree data)) C
            (staged_composition_fri_roots data)
            (staged_composition_fri_challenges data)
            (staged_composition_final data) query_start
         else {})"
  proof (cases "to_nat (staged_degree data) \<le> maxDegree")
    case True
    have shape:
        "length (staged_composition_fri_roots data) =
            ceil_log (Suc (to_nat (staged_degree data))) \<and>
         length (staged_composition_fri_challenges data) =
            ceil_log (Suc (to_nat (staged_degree data)))"
      using
        ro_checked_staged_first_root_query_head_program_output_fri_lengths[
          OF head]
      by blast
    have log_le:
        "ceil_log (Suc (to_nat (staged_degree data))) \<le>
          ceil_log (Suc maxDegree)"
      by (rule ceil_log_mono) (use True in simp)
    have roots_le:
        "length (staged_composition_fri_roots data) \<le> N"
      using shape log_le composition_rounds_fit by linarith
    have lengths:
        "length (staged_composition_fri_challenges data) =
          length (staged_composition_fri_roots data)"
      using shape by simp
    show ?thesis
      unfolding fri_balanced_selected_composition_query_head_lists_def
        fri_balanced_selected_composition_residual_query_lists_def
        if_P[OF True]
      by (rule
          fri_balanced_selected_residual_query_lists_rectangle_cover[
            OF eval_power roots_le lengths])
  next
    case False
    show ?thesis
      unfolding fri_balanced_selected_composition_query_head_lists_def
        fri_balanced_selected_composition_residual_query_lists_def
        if_not_P[OF False]
      by simp
  qed
next
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "(if to_nat (staged_degree data) \<le> maxDegree then
      fri_balanced_selected_residual_query_indices
        (to_nat (staged_degree data)) C
        (staged_composition_fri_roots data)
        (staged_composition_fri_challenges data)
        (staged_composition_final data) query_start
     else {})
    \<subseteq> query_sample_space"
    by (cases "to_nat (staged_degree data) \<le> maxDegree")
      (simp_all add: fri_balanced_selected_residual_query_indices_subset)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "card
      (if to_nat (staged_degree data) \<le> maxDegree then
        fri_balanced_selected_residual_query_indices
          (to_nat (staged_degree data)) C
          (staged_composition_fri_roots data)
          (staged_composition_fri_challenges data)
          (staged_composition_final data) query_start
       else {})
      \<le> fri_balanced_selected_residual_index_card_bound maxDegree C"
  proof (cases "to_nat (staged_degree data) \<le> maxDegree")
    case True
    have shape:
        "length (staged_composition_fri_roots data) =
            ceil_log (Suc (to_nat (staged_degree data))) \<and>
         length (staged_composition_fri_challenges data) =
            ceil_log (Suc (to_nat (staged_degree data)))"
      using
        ro_checked_staged_first_root_query_head_program_output_fri_lengths[
          OF head]
      by blast
    have round_count:
        "length (staged_composition_fri_challenges data) =
          ceil_log (Suc (to_nat (staged_degree data)))"
      using shape by simp
    have log_le:
        "ceil_log (Suc (to_nat (staged_degree data))) \<le>
          ceil_log (Suc maxDegree)"
      by (rule ceil_log_mono) (use True in simp)
    have rounds_fit:
        "Suc (length (staged_composition_fri_challenges data)) \<le> N"
      using shape log_le composition_rounds_fit by linarith
    have lengths:
        "length (staged_composition_fri_challenges data) =
          length (staged_composition_fri_roots data)"
      using shape by simp
    have local:
        "card
          (fri_balanced_selected_residual_query_indices
            (to_nat (staged_degree data)) C
            (staged_composition_fri_roots data)
            (staged_composition_fri_challenges data)
            (staged_composition_final data) query_start)
          \<le> fri_balanced_selected_residual_index_card_bound
              (to_nat (staged_degree data)) C"
      by (rule card_fri_balanced_selected_residual_query_indices[
            OF eval_power round_count rounds_fit lengths])
    have mono:
        "fri_balanced_selected_residual_index_card_bound
            (to_nat (staged_degree data)) C
          \<le> fri_balanced_selected_residual_index_card_bound maxDegree C"
      by (rule
        fri_balanced_selected_residual_index_card_bound_mono[OF True])
    show ?thesis
      unfolding if_P[OF True]
      using local mono by linarith
  next
    case False
    show ?thesis
      unfolding if_not_P[OF False] by simp
  qed
qed

definition
  ro_checked_staged_balanced_selected_combined_actual_residual_rectangle_error_adaptive
    :: "nat \<Rightarrow> staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_balanced_selected_combined_actual_residual_rectangle_error_adaptive
      C budgets =
    ro_checked_staged_balanced_selected_residual_rectangle_error_adaptive
      (clength - 1) C budgets +
    ro_checked_staged_balanced_selected_residual_rectangle_error_adaptive
      maxDegree C budgets"

lemma wp_ro_checked_staged_combined_balanced_selected_residual_actual_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit
        (fri_balanced_selected_combined_query_head_lists C))
      adversary_initial_state
    \<le>
      ro_checked_staged_balanced_selected_combined_actual_residual_rectangle_error_adaptive
        C budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?Trace =
    "ro_query_head_dependent_actual_query_index_list_hit
      (fri_balanced_selected_trace_query_head_lists C)"
  let ?Composition =
    "ro_query_head_dependent_actual_query_index_list_hit
      (fri_balanced_selected_composition_query_head_lists C)"
  have event_eq:
      "ro_query_head_dependent_actual_query_index_list_hit
          (fri_balanced_selected_combined_query_head_lists C) =
        (\<lambda>out. ?Trace out \<or> ?Composition out)"
    unfolding ro_query_head_dependent_actual_query_index_list_hit_def
      fri_balanced_selected_combined_query_head_lists_def
    by (rule ext) (auto split: option.splits prod.splits)
  have union:
      "wp_event ?M
          (ro_query_head_dependent_actual_query_index_list_hit
            (fri_balanced_selected_combined_query_head_lists C))
          adversary_initial_state
        \<le>
        wp_event ?M ?Trace adversary_initial_state +
        wp_event ?M ?Composition adversary_initial_state"
    unfolding event_eq
    by (rule wp_event_union_bound)
  have trace:
      "wp_event ?M ?Trace adversary_initial_state \<le>
        ro_checked_staged_balanced_selected_residual_rectangle_error_adaptive
          (clength - 1) C budgets"
    by (rule
        wp_ro_checked_staged_trace_balanced_selected_residual_actual_rectangle_bound_adaptive[
          OF wf controlled eval_power trace_rounds_fit])
  have composition:
      "wp_event ?M ?Composition adversary_initial_state \<le>
        ro_checked_staged_balanced_selected_residual_rectangle_error_adaptive
          maxDegree C budgets"
    by (rule
        wp_ro_checked_staged_composition_balanced_selected_residual_actual_rectangle_bound_adaptive[
          OF wf controlled eval_power composition_rounds_fit])
  show ?thesis
    unfolding
      ro_checked_staged_balanced_selected_combined_actual_residual_rectangle_error_adaptive_def
    by (rule order_trans[OF union add_mono[OF trace composition]])
qed

end
end
