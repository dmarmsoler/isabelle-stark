theory Soundness_FRI_Conditioned_Explicit_Adaptive_Rectangle_Security
  imports Soundness_FRI_Conditioned_Explicit_Adaptive_Rectangles
begin

context soundness
begin

lemma
  wp_ro_absorb_checked_staged_security_combined_conditioned_residual_actual_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_combined_query_head_lists)
      adversary_initial_state
    \<le> ro_checked_staged_conditioned_complete_list_actual_residual_rectangle_error_adaptive
        budgets"
  by (rule order_trans[
      OF
        wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
        wp_ro_checked_staged_combined_conditioned_residual_actual_rectangle_bound_adaptive[
          OF wf controlled]])

lemma
  wp_ro_absorb_checked_staged_security_trace_composition_good_actual_query_rectangle_bound_adaptive:
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
    ro_checked_staged_trace_composition_good_actual_query_rectangle_error_adaptive
      budgets"
  by (rule order_trans[
      OF
        wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
        wp_ro_checked_staged_trace_composition_good_actual_query_rectangle_bound_adaptive[
          OF wf controlled]])

lemma
  wp_ro_absorb_checked_staged_security_trace_composition_padding_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        ro_trace_composition_padding_query_head_lists)
      adversary_initial_state
    \<le> ro_checked_staged_trace_composition_padding_rectangle_error_adaptive
        budgets"
  by (rule order_trans[
      OF
        wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
        wp_ro_checked_staged_trace_composition_padding_rectangle_bound_adaptive[
          OF wf controlled]])

end
end
