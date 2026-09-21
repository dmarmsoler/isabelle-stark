theory Soundness_FRI_Conditioned_Explicit_Residual_Actual_Product_Zero
  imports Soundness_FRI_Query_Future_Fresh_Zero_Budget
begin

context soundness
begin

lemma
  ro_query_head_dependent_actual_query_index_list_hit_imp_fresh_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and actual:
      "ro_query_head_dependent_actual_query_index_list_hit Q
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
  shows
    "ro_query_head_dependent_query_index_list_fresh_hit Q
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
proof -
  from ro_checked_staged_transcript_program_with_first_root_outcomeE[
      OF outcome]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute
            (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
    and after_out:
      "Some (head_data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program
              A prefix)
            prefix_final)"
    and tail_out:
      "Some ((raws, query_states, query_chunks), attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots head_data)
              (staged_composition_fri_roots head_data)
              query_start 0 rounds)
            query_start)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    .
  have head_out:
    "Some (((prefix, prefix_state), head_data, query_start), query_start) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
    unfolding ro_checked_staged_first_root_query_head_program_def
    apply (rule set_dist_bindI[OF prefix_out])
    apply (simp only: fst_conv)
    apply (rule set_dist_bindI[OF after_out])
    apply (rule_tac x=query_start and t=query_start in set_dist_bindI)
    by simp_all
  have initial_future:
    "query_future_fresh adversary_initial_state"
    unfolding query_future_fresh_def by simp
  have query_start_future: "query_future_fresh query_start"
    by (rule
        ro_checked_staged_first_root_query_head_program_preserves_query_future_fresh_zero[
          OF wf controlled zero initial_future head_out])
  have zero_controlled:
    "controlled_ro_program 0 (trace_root_stage A) \<and>
     (\<forall>i < length (trace_fri_budgets budgets). \<forall>bs.
       controlled_ro_program 0 (trace_fri_root_stage A i bs)) \<and>
     (\<forall>bs. controlled_ro_program 0 (trace_final_stage A bs)) \<and>
     (\<forall>as. controlled_ro_program 0 (degree_stage A as)) \<and>
     (\<forall>dg i. i < length (composition_fri_budgets budgets) \<longrightarrow>
       (\<forall>bs. controlled_ro_program 0
         (composition_fri_root_stage A dg i bs))) \<and>
     (\<forall>dg bs.
       controlled_ro_program 0 (composition_final_stage A dg bs)) \<and>
     (\<forall>i < length (query_opening_budgets budgets). \<forall>raw.
       controlled_ro_program 0 (query_opening_stage A i raw))"
    by (rule staged_adversary_controlled_query_budget_zeroD[
          OF controlled zero])
  have query_budget_length:
    "length (query_opening_budgets budgets) = rounds"
    using wf unfolding staged_budget_wellformed_def by blast
  have query_controlled:
    "\<forall>j raw. j < rounds \<longrightarrow>
      controlled_ro_program 0 (query_opening_stage A j raw)"
    using zero_controlled query_budget_length by blast
  have tail_hit:
    "ro_query_witnesses_raws_fresh_hit raws
      (Some ((raws, query_states, query_chunks), attacker_state))"
    by (rule
        ro_checked_staged_query_program_with_witnesses_future_fresh_hit_zero[
          OF query_start_future query_controlled _ tail_out])
      simp
  have query_bound:
    "0 + rounds \<le> length (query_opening_budgets budgets)"
    using query_budget_length by simp
  have len_raws: "length raws = rounds"
    using
      ro_checked_staged_query_program_with_witnesses_outcome[
        OF controlled query_bound tail_out]
    by blast
  let ?Q =
    "Q prefix prefix_state (ro_query_head_data data) query_start"
  have query_in:
    "map (\<lambda>raw. index (to_nat raw)) raws \<in> ?Q"
    using actual
    unfolding ro_query_head_dependent_actual_query_index_list_hit_def
    by simp
  have raw_in: "raws \<in> query_index_raw_list_preimage ?Q"
    unfolding query_index_raw_list_preimage_def
    using len_raws query_in by blast
  have chunks_eq: "staged_query_chunks data = query_chunks"
    using data_eq by simp
  have tail_hit_data:
    "ro_query_witnesses_raws_fresh_hit raws
      (Some ((raws, query_states, staged_query_chunks data),
        attacker_state))"
    using tail_hit chunks_eq by simp
  have list_fresh:
    "ro_query_witnesses_query_index_list_fresh_hit ?Q
      (Some ((raws, query_states, staged_query_chunks data),
        attacker_state))"
    by (rule ro_query_witnesses_query_index_list_fresh_hitI[
          OF raw_in tail_hit_data])
  show ?thesis
    unfolding ro_query_head_dependent_query_index_list_fresh_hit_def
    using list_fresh by simp
qed

lemma
  wp_ro_query_head_dependent_actual_query_index_list_hit_le_fresh_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_actual_query_index_list_hit Q)
      adversary_initial_state
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_index_list_fresh_hit Q)
      adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
    "out \<in>
      set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          adversary_initial_state)"
    and actual:
      "ro_query_head_dependent_actual_query_index_list_hit Q out"
  show "ro_query_head_dependent_query_index_list_fresh_hit Q out"
  proof (cases out)
    case None
    then show ?thesis
      using actual
      unfolding ro_query_head_dependent_actual_query_index_list_hit_def
      by simp
  next
    case (Some packed)
    obtain prefix prefix_state data query_start raws query_states
        attacker_state where packed_eq:
      "packed =
        (((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)"
      by (cases packed) (auto split: prod.splits)
    have outcome':
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
      using support unfolding Some packed_eq .
    have actual':
      "ro_query_head_dependent_actual_query_index_list_hit Q
        (Some ((((prefix, prefix_state), data, query_start, raws,
          query_states), attacker_state)))"
      using actual unfolding Some packed_eq .
    have fresh':
      "ro_query_head_dependent_query_index_list_fresh_hit Q
        (Some ((((prefix, prefix_state), data, query_start, raws,
          query_states), attacker_state)))"
      by (rule
          ro_query_head_dependent_actual_query_index_list_hit_imp_fresh_zero[
            OF wf controlled zero outcome' actual'])
    show ?thesis using fresh' unfolding Some packed_eq .
  qed
qed

lemma
  wp_ro_checked_staged_combined_conditioned_residual_actual_bound_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_combined_query_head_lists)
      adversary_initial_state
    \<le>
    nnreal
      (fri_conditioned_residual_query_list_card_bound (clength - 1) +
       fri_conditioned_residual_query_list_card_bound maxDegree) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
proof (rule order_trans)
  show
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_combined_query_head_lists)
      adversary_initial_state
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_index_list_fresh_hit
        fri_conditioned_combined_query_head_lists)
      adversary_initial_state"
    by (rule
        wp_ro_query_head_dependent_actual_query_index_list_hit_le_fresh_zero[
          OF wf controlled zero])
  show
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_index_list_fresh_hit
        fri_conditioned_combined_query_head_lists)
      adversary_initial_state
    \<le>
    nnreal
      (fri_conditioned_residual_query_list_card_bound (clength - 1) +
       fri_conditioned_residual_query_list_card_bound maxDegree) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
    by (rule wp_ro_checked_staged_combined_conditioned_residual_fresh_bound)
qed


end
end
