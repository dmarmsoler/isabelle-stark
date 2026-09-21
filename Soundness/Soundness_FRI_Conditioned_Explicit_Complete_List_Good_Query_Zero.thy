theory Soundness_FRI_Conditioned_Explicit_Complete_List_Good_Query_Zero
  imports Stark.Soundness_FRI_Conditioned_Explicit_Residual_Actual_Product_Zero
begin

context soundness
begin

definition
  ro_checked_staged_trace_composition_complete_list_good_actual_query_error
    :: prob
where
  "ro_checked_staged_trace_composition_complete_list_good_actual_query_error =
    nnreal (trace_composition_query_index_bound ^ rounds) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"

lemma wp_ro_checked_staged_trace_composition_complete_list_good_actual_query_bound_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_trace_composition_good_query_lists)
      adversary_initial_state
    \<le> ro_checked_staged_trace_composition_complete_list_good_actual_query_error"
proof (rule order_trans)
  show
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
      adversary_initial_state"
    by (rule
      wp_ro_query_head_dependent_actual_query_index_list_hit_le_fresh_zero[
        OF wf controlled zero])
  show
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_index_list_fresh_hit
        ro_actual_query_trace_composition_good_query_lists)
      adversary_initial_state
    \<le> ro_checked_staged_trace_composition_complete_list_good_actual_query_error"
    unfolding
      ro_checked_staged_trace_composition_complete_list_good_actual_query_error_def
    by (rule wp_ro_actual_query_trace_composition_good_fresh_bound)
qed

lemma
  wp_ro_absorb_checked_staged_security_trace_composition_complete_list_good_actual_query_bound_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_trace_composition_good_query_lists)
      adversary_initial_state
    \<le> ro_checked_staged_trace_composition_complete_list_good_actual_query_error"
  by (rule order_trans[
    OF
      wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
      wp_ro_checked_staged_trace_composition_complete_list_good_actual_query_bound_zero[
        OF wf controlled zero]])

end
end
