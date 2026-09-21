theory Soundness_FRI_Conditioned_Residual_Adaptive_Rectangle_Products
  imports Soundness_FRI_Conditioned_Residual_Adaptive_Rectangle_Layers
begin

context soundness
begin

lemma wp_ro_checked_staged_trace_conditioned_residual_actual_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_trace_query_head_lists)
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_residual_rectangle_error_adaptive
        (clength - 1) budgets"
  proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_family_bound[
      OF wf controlled,
      where
        K="\<lambda>prefix prefix_state data query_start.
          fri_conditioned_residual_active_layers (clength - 1)
            (staged_trace_fri_roots data)
            (staged_trace_fri_challenges data)
            (staged_trace_final data) query_start"
      and
        I="\<lambda>prefix prefix_state data query_start i.
          fri_conditioned_residual_layer_query_indices
            (staged_trace_fri_roots data)
            (staged_trace_fri_challenges data)
            (fri_builder_conceptual_layers
              (staged_trace_fri_roots data) query_start
              (staged_trace_final data))
            i"])
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "finite
      (fri_conditioned_residual_active_layers (clength - 1)
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        (staged_trace_final data) query_start)"
    by simp
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have shape:
    "length (staged_trace_fri_roots data) = ceil_log clength \<and>
     length (staged_trace_fri_challenges data) = ceil_log clength"
    using
      ro_checked_staged_first_root_query_head_program_output_fri_lengths[
        OF head]
    by blast
  have roots_le: "length (staged_trace_fri_roots data) \<le> N"
    using shape ceil_log_clength_le_eval_power[OF eval_power]
    by simp
  have lengths:
    "length (staged_trace_fri_challenges data) =
      length (staged_trace_fri_roots data)"
    using shape by simp
  show
    "fri_conditioned_trace_query_head_lists
        prefix prefix_state data query_start
      \<subseteq>
      (\<Union>i\<in>fri_conditioned_residual_active_layers (clength - 1)
          (staged_trace_fri_roots data)
          (staged_trace_fri_challenges data)
          (staged_trace_final data) query_start.
        fri_conditioned_query_lists
          (fri_conditioned_residual_layer_query_indices
            (staged_trace_fri_roots data)
            (staged_trace_fri_challenges data)
            (fri_builder_conceptual_layers
              (staged_trace_fri_roots data) query_start
              (staged_trace_final data))
            i))"
    unfolding fri_conditioned_trace_query_head_lists_def
      fri_conditioned_trace_residual_query_lists_def
    by (rule
        fri_conditioned_quantitative_residual_query_lists_active_rectangle_cover[
          OF eval_power roots_le lengths])
next
  fix prefix prefix_state data query_start t i
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
    and
    "i \<in>
      fri_conditioned_residual_active_layers (clength - 1)
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        (staged_trace_final data) query_start"
  show
    "fri_conditioned_residual_layer_query_indices
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        (fri_builder_conceptual_layers
          (staged_trace_fri_roots data) query_start
          (staged_trace_final data))
        i
      \<subseteq> query_sample_space"
    by (rule fri_conditioned_residual_layer_query_indices_subset)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
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
  have rounds_le: "ceil_log (Suc (clength - 1)) \<le> N"
    using ceil_log_clength_le_eval_power[OF eval_power] clength_pos by simp
  have lengths:
    "length (staged_trace_fri_challenges data) =
      length (staged_trace_fri_roots data)"
    using shape by simp
  show
    "(\<Sum>i\<in>fri_conditioned_residual_active_layers (clength - 1)
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        (staged_trace_final data) query_start.
      (nnreal
          (query_raw_preimage_card_envelope
            (card
              (fri_conditioned_residual_layer_query_indices
                (staged_trace_fri_roots data)
                (staged_trace_fri_challenges data)
                (fri_builder_conceptual_layers
                  (staged_trace_fri_roots data) query_start
                  (staged_trace_final data))
                i))) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets))
    \<le> ro_checked_staged_conditioned_residual_rectangle_error_adaptive
        (clength - 1) budgets"
    by (rule fri_conditioned_residual_active_layer_probability_sum_le[
          OF eval_power round_count rounds_le lengths])
qed


lemma ro_checked_staged_conditioned_residual_rectangle_error_adaptive_mono:
  assumes "d \<le> D"
  shows
    "ro_checked_staged_conditioned_residual_rectangle_error_adaptive d budgets
      \<le> ro_checked_staged_conditioned_residual_rectangle_error_adaptive
          D budgets"
  unfolding
    ro_checked_staged_conditioned_residual_rectangle_error_adaptive_def
  by (rule sum_mono2)
    (use ceil_log_mono[of "Suc d" "Suc D"] assms in auto)


lemma wp_ro_checked_staged_composition_conditioned_residual_actual_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_composition_query_head_lists)
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_residual_rectangle_error_adaptive
        maxDegree budgets"
  proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_family_bound[
      OF wf controlled,
      where
        K="\<lambda>prefix prefix_state data query_start.
          if to_nat (staged_degree data) \<le> maxDegree then
            fri_conditioned_residual_active_layers
              (to_nat (staged_degree data))
              (staged_composition_fri_roots data)
              (staged_composition_fri_challenges data)
              (staged_composition_final data) query_start
          else {}"
      and
        I="\<lambda>prefix prefix_state data query_start i.
          fri_conditioned_residual_layer_query_indices
            (staged_composition_fri_roots data)
            (staged_composition_fri_challenges data)
            (fri_builder_conceptual_layers
              (staged_composition_fri_roots data) query_start
              (staged_composition_final data))
            i"])
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "finite
      (if to_nat (staged_degree data) \<le> maxDegree then
        fri_conditioned_residual_active_layers
          (to_nat (staged_degree data))
          (staged_composition_fri_roots data)
          (staged_composition_fri_challenges data)
          (staged_composition_final data) query_start
       else {})"
    by simp
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "fri_conditioned_composition_query_head_lists
        prefix prefix_state data query_start
      \<subseteq>
      (\<Union>i\<in>
        (if to_nat (staged_degree data) \<le> maxDegree then
          fri_conditioned_residual_active_layers
            (to_nat (staged_degree data))
            (staged_composition_fri_roots data)
            (staged_composition_fri_challenges data)
            (staged_composition_final data) query_start
         else {}).
        fri_conditioned_query_lists
          (fri_conditioned_residual_layer_query_indices
            (staged_composition_fri_roots data)
            (staged_composition_fri_challenges data)
            (fri_builder_conceptual_layers
              (staged_composition_fri_roots data) query_start
              (staged_composition_final data))
            i))"
  proof (cases "to_nat (staged_degree data) \<le> maxDegree")
    case True
    obtain N where eval_power: "clength * scale = 2 ^ N"
      using eval_domain_length_power by blast
    have shape:
      "length (staged_composition_fri_roots data) =
          ceil_log (Suc (to_nat (staged_degree data))) \<and>
       length (staged_composition_fri_challenges data) =
          ceil_log (Suc (to_nat (staged_degree data)))"
      using
        ro_checked_staged_first_root_query_head_program_output_fri_lengths[
          OF head]
      by blast
    have roots_le:
      "length (staged_composition_fri_roots data) \<le> N"
      using shape
        ceil_log_reachable_degree_le_eval_power[
          OF eval_power True]
      by simp
    have lengths:
      "length (staged_composition_fri_challenges data) =
        length (staged_composition_fri_roots data)"
      using shape by simp
    show ?thesis
      unfolding fri_conditioned_composition_query_head_lists_def
        fri_conditioned_composition_residual_query_lists_def
        if_P[OF True]
      by (rule
          fri_conditioned_quantitative_residual_query_lists_active_rectangle_cover[
            OF eval_power roots_le lengths])
  next
    case False
    show ?thesis
      unfolding fri_conditioned_composition_query_head_lists_def
        fri_conditioned_composition_residual_query_lists_def
        if_not_P[OF False]
      by simp
  qed
next
  fix prefix prefix_state data query_start t i
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
    and
    "i \<in>
      (if to_nat (staged_degree data) \<le> maxDegree then
        fri_conditioned_residual_active_layers
          (to_nat (staged_degree data))
          (staged_composition_fri_roots data)
          (staged_composition_fri_challenges data)
          (staged_composition_final data) query_start
       else {})"
  show
    "fri_conditioned_residual_layer_query_indices
        (staged_composition_fri_roots data)
        (staged_composition_fri_challenges data)
        (fri_builder_conceptual_layers
          (staged_composition_fri_roots data) query_start
          (staged_composition_final data))
        i
      \<subseteq> query_sample_space"
    by (rule fri_conditioned_residual_layer_query_indices_subset)
next
  fix prefix prefix_state data query_start t
  assume head:
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "(\<Sum>i\<in>
        (if to_nat (staged_degree data) \<le> maxDegree then
          fri_conditioned_residual_active_layers
            (to_nat (staged_degree data))
            (staged_composition_fri_roots data)
            (staged_composition_fri_challenges data)
            (staged_composition_final data) query_start
         else {}).
      (nnreal
          (query_raw_preimage_card_envelope
            (card
              (fri_conditioned_residual_layer_query_indices
                (staged_composition_fri_roots data)
                (staged_composition_fri_challenges data)
                (fri_builder_conceptual_layers
                  (staged_composition_fri_roots data) query_start
                  (staged_composition_final data))
                i))) /
        nnreal size) ^
      (rounds - staged_attacker_query_budget budgets))
    \<le> ro_checked_staged_conditioned_residual_rectangle_error_adaptive
        maxDegree budgets"
  proof (cases "to_nat (staged_degree data) \<le> maxDegree")
    case True
    obtain N where eval_power: "clength * scale = 2 ^ N"
      using eval_domain_length_power by blast
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
    have rounds_le:
      "ceil_log (Suc (to_nat (staged_degree data))) \<le> N"
      by (rule ceil_log_reachable_degree_le_eval_power[
            OF eval_power True])
    have lengths:
      "length (staged_composition_fri_challenges data) =
        length (staged_composition_fri_roots data)"
      using shape by simp
    have local:
      "(\<Sum>i\<in>
          fri_conditioned_residual_active_layers
            (to_nat (staged_degree data))
            (staged_composition_fri_roots data)
            (staged_composition_fri_challenges data)
            (staged_composition_final data) query_start.
        (nnreal
            (query_raw_preimage_card_envelope
              (card
                (fri_conditioned_residual_layer_query_indices
                  (staged_composition_fri_roots data)
                  (staged_composition_fri_challenges data)
                  (fri_builder_conceptual_layers
                    (staged_composition_fri_roots data) query_start
                    (staged_composition_final data))
                  i))) /
          nnreal size) ^
        (rounds - staged_attacker_query_budget budgets))
      \<le> ro_checked_staged_conditioned_residual_rectangle_error_adaptive
          (to_nat (staged_degree data)) budgets"
      by (rule fri_conditioned_residual_active_layer_probability_sum_le[
            OF eval_power round_count rounds_le lengths])
    have mono:
      "ro_checked_staged_conditioned_residual_rectangle_error_adaptive
          (to_nat (staged_degree data)) budgets
        \<le> ro_checked_staged_conditioned_residual_rectangle_error_adaptive
            maxDegree budgets"
      by (rule
          ro_checked_staged_conditioned_residual_rectangle_error_adaptive_mono[
            OF True])
    show ?thesis
      unfolding if_P[OF True]
      by (rule order_trans[OF local mono])
  next
    case False
    show ?thesis
      unfolding if_not_P[OF False] by simp
  qed
qed


definition
  ro_checked_staged_conditioned_complete_list_actual_residual_rectangle_error_adaptive
    :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_conditioned_complete_list_actual_residual_rectangle_error_adaptive
      budgets =
    ro_checked_staged_conditioned_residual_rectangle_error_adaptive
      (clength - 1) budgets +
    ro_checked_staged_conditioned_residual_rectangle_error_adaptive
      maxDegree budgets"

lemma wp_ro_checked_staged_combined_conditioned_residual_actual_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_combined_query_head_lists)
      adversary_initial_state
    \<le>
      ro_checked_staged_conditioned_complete_list_actual_residual_rectangle_error_adaptive
        budgets"
  proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?Trace =
    "ro_query_head_dependent_actual_query_index_list_hit
      fri_conditioned_trace_query_head_lists"
  let ?Composition =
    "ro_query_head_dependent_actual_query_index_list_hit
      fri_conditioned_composition_query_head_lists"
  have event_eq:
    "ro_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_combined_query_head_lists =
      (\<lambda>out. ?Trace out \<or> ?Composition out)"
    unfolding ro_query_head_dependent_actual_query_index_list_hit_def
      fri_conditioned_combined_query_head_lists_def
    by (rule ext) (auto split: option.splits prod.splits)
  have union:
    "wp_event ?M
        (ro_query_head_dependent_actual_query_index_list_hit
          fri_conditioned_combined_query_head_lists)
        adversary_initial_state
      \<le>
      wp_event ?M ?Trace adversary_initial_state +
      wp_event ?M ?Composition adversary_initial_state"
    unfolding event_eq
    by (rule wp_event_union_bound)
  have trace:
    "wp_event ?M ?Trace adversary_initial_state \<le>
      ro_checked_staged_conditioned_residual_rectangle_error_adaptive
        (clength - 1) budgets"
    by (rule
        wp_ro_checked_staged_trace_conditioned_residual_actual_rectangle_bound_adaptive[
          OF wf controlled])
  have composition:
    "wp_event ?M ?Composition adversary_initial_state \<le>
      ro_checked_staged_conditioned_residual_rectangle_error_adaptive
        maxDegree budgets"
    by (rule
        wp_ro_checked_staged_composition_conditioned_residual_actual_rectangle_bound_adaptive[
          OF wf controlled])
  show ?thesis
    unfolding
      ro_checked_staged_conditioned_complete_list_actual_residual_rectangle_error_adaptive_def
    by (rule order_trans[OF union add_mono[OF trace composition]])
qed

end
end
