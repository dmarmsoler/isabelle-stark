theory Soundness_FRI_Conditioned_Explicit_Complete_List_Padding_Zero
  imports
    Stark.Soundness_FRI_Conditioned_Explicit_Residual_Actual_Product_Zero
    Stark.Soundness_FRI_Conditioned_Trace_Composition_Padding_Outcome_Bridge
begin

context soundness
begin

definition ro_trace_composition_padding_query_head_lists
  :: "('f \<times> 'f list \<times> 'f) \<Rightarrow> 'f protocol_channel \<Rightarrow>
      'f staged_proof_data \<Rightarrow> 'f protocol_channel \<Rightarrow>
      nat list set"
where
  "ro_trace_composition_padding_query_head_lists
      prefix prefix_state data query_start =
    (if to_nat (staged_degree data) \<le> maxDegree
     then trace_composition_padding_query_lists
       (conceptual_table prefix_state (staged_trace_root data)
         (scale * clength))
       (first_trace_fri_root_prefix_first_table prefix prefix_state)
       (ro_actual_query_composition_candidate data query_start)
       (staged_alphas data)
       (fri_padded_degree_bound (to_nat (staged_degree data)))
     else {})"

lemma ro_trace_composition_padding_query_head_lists_subset:
  "ro_trace_composition_padding_query_head_lists
      prefix prefix_state data query_start
    \<subseteq> fri_query_index_list_space"
proof (cases "to_nat (staged_degree data) \<le> maxDegree")
  case True
  show ?thesis
    unfolding ro_trace_composition_padding_query_head_lists_def
      if_P[OF True]
    by (rule trace_composition_padding_query_lists_subset)
next
  case False
  show ?thesis
    unfolding ro_trace_composition_padding_query_head_lists_def
      if_not_P[OF False]
    by simp
qed

lemma card_ro_trace_composition_padding_query_head_lists:
  "card
      (ro_trace_composition_padding_query_head_lists
        prefix prefix_state data query_start)
    \<le> trace_composition_padding_query_index_bound ^ rounds"
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
  have lengths: "length ?original = length ?candidate"
  proof -
    obtain fr xs first_root where prefix_eq:
      "prefix = (fr, xs, first_root)"
      by (cases prefix) auto
    show ?thesis
      unfolding prefix_eq first_trace_fri_root_prefix_first_table_def
      by simp
  qed
  have card:
      "card
        (trace_composition_padding_query_lists
          ?original ?candidate ?composition (staged_alphas data)
          (fri_padded_degree_bound ?d))
      \<le>
        trace_composition_query_index_bound_for
          (fri_padded_degree_bound ?d) ^ rounds"
    by (rule card_trace_composition_padding_query_lists[OF lengths])
  have index_mono:
      "trace_composition_query_index_bound_for
          (fri_padded_degree_bound ?d)
        \<le> trace_composition_padding_query_index_bound"
    by (rule trace_composition_padding_query_index_bound_mono[
          OF degree_bound])
  have power_mono:
      "trace_composition_query_index_bound_for
          (fri_padded_degree_bound ?d) ^ rounds
        \<le> trace_composition_padding_query_index_bound ^ rounds"
    by (rule power_mono[OF index_mono]) simp
  show ?thesis
    unfolding ro_trace_composition_padding_query_head_lists_def
      if_P[OF degree_bound]
    by (rule order_trans[OF card power_mono])
next
  case degree_bound: False
  show ?thesis
    unfolding ro_trace_composition_padding_query_head_lists_def
      if_not_P[OF degree_bound]
    by simp
qed

definition ro_checked_staged_trace_composition_complete_list_padding_error
  :: prob
where
  "ro_checked_staged_trace_composition_complete_list_padding_error =
    nnreal (trace_composition_padding_query_index_bound ^ rounds) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"

lemma wp_ro_checked_staged_trace_composition_padding_fresh_bound:
  "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_index_list_fresh_hit
        ro_trace_composition_padding_query_head_lists)
      s
    \<le> ro_checked_staged_trace_composition_complete_list_padding_error"
  unfolding
    ro_checked_staged_trace_composition_complete_list_padding_error_def
proof (rule
    wp_ro_checked_staged_transcript_query_head_dependent_fresh_bound)
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
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
        (execute (ro_checked_staged_first_root_query_head_program A) s)"
  show
    "card
      (ro_trace_composition_padding_query_head_lists
        prefix prefix_state data query_start)
      \<le> trace_composition_padding_query_index_bound ^ rounds"
    by (rule card_ro_trace_composition_padding_query_head_lists)
qed

lemma wp_ro_checked_staged_trace_composition_complete_list_padding_bound_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_actual_query_index_list_hit
        ro_trace_composition_padding_query_head_lists)
      adversary_initial_state
    \<le> ro_checked_staged_trace_composition_complete_list_padding_error"
proof (rule order_trans)
  show
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_actual_query_index_list_hit
        ro_trace_composition_padding_query_head_lists)
      adversary_initial_state
    \<le>
    wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_index_list_fresh_hit
        ro_trace_composition_padding_query_head_lists)
      adversary_initial_state"
    by (rule
      wp_ro_query_head_dependent_actual_query_index_list_hit_le_fresh_zero[
        OF wf controlled zero])
  show
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_index_list_fresh_hit
        ro_trace_composition_padding_query_head_lists)
      adversary_initial_state
    \<le> ro_checked_staged_trace_composition_complete_list_padding_error"
    by (rule wp_ro_checked_staged_trace_composition_padding_fresh_bound)
qed

lemma
  wp_ro_absorb_checked_staged_security_trace_composition_complete_list_padding_bound_zero:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and zero: "staged_attacker_query_budget budgets = 0"
  shows
    "wp_event
      (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
        A)
      (ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        ro_trace_composition_padding_query_head_lists)
      adversary_initial_state
    \<le> ro_checked_staged_trace_composition_complete_list_padding_error"
  by (rule order_trans[
    OF
      wp_ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_le
      wp_ro_checked_staged_trace_composition_complete_list_padding_bound_zero[
        OF wf controlled zero]])

lemma ro_trace_composition_padding_query_head_lists_query_head_data[simp]:
  "ro_trace_composition_padding_query_head_lists
      prefix prefix_state (ro_query_head_data data) query_start =
    ro_trace_composition_padding_query_head_lists
      prefix prefix_state data query_start"
  unfolding ro_trace_composition_padding_query_head_lists_def
    ro_query_head_data_def ro_actual_query_composition_candidate_def
  by simp


lemma
  checked_builder_trace_composition_padding_bad_imp_actual_or_targets:
  fixes final_state :: "'f protocol_channel"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and builder_out:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in> set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          adversary_initial_state)"
    and verifier_out:
      "Some (results, final_state) \<in> set_dist
        (execute ro_verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    and final_clean: "\<not> hash_map_output_collision final_state"
    and first_trace_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)"
    and composition_padded_low:
      "composition_table_low_degree
        (fri_padded_degree_bound (to_nat (staged_degree data)))
        (ro_actual_query_composition_candidate data query_start)"
    and composition_bad:
      "\<not> composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate data query_start)"
  shows
    "ro_query_head_dependent_actual_query_index_list_hit
        ro_trace_composition_padding_query_head_lists
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state))) \<or>
     hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state \<or>
     hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets data query_start)
        query_start final_state"
proof -
  have indices_or_targets:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_actual_query_trace_composition_accepted_query_lists
            prefix prefix_state data query_start \<or>
       hash_map_new_output_hit
         (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
         prefix_state final_state \<or>
       hash_map_new_output_hit
         (ro_actual_query_composition_prefix_targets data query_start)
         query_start final_state"
    by (rule
      ro_absorb_checked_staged_first_root_actual_query_trace_composition_indices_or_targets[
        OF wf controlled nonempty builder_out verifier_out final_clean])
  then show ?thesis
  proof
    assume accepted_queries:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_actual_query_trace_composition_accepted_query_lists
          prefix prefix_state data query_start"
    have degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
      using ro_absorb_checked_staged_first_root_actual_query_accepted_evidence[
        OF wf controlled nonempty builder_out verifier_out final_clean]
      by blast
    have accepted_exact:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          query_index_lists_over
            (trace_composition_accepted_indices
              (conceptual_table prefix_state (staged_trace_root data)
                (scale * clength))
              (first_trace_fri_root_prefix_first_table prefix prefix_state)
              (ro_actual_query_composition_candidate data query_start)
              (staged_alphas data))"
      using accepted_queries
      unfolding
        ro_actual_query_trace_composition_accepted_query_lists_def
        ro_actual_query_trace_composition_accepted_indices_def
      .
    have raws_in:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          trace_composition_padding_query_lists
            (conceptual_table prefix_state (staged_trace_root data)
              (scale * clength))
            (first_trace_fri_root_prefix_first_table prefix prefix_state)
            (ro_actual_query_composition_candidate data query_start)
            (staged_alphas data)
            (fri_padded_degree_bound (to_nat (staged_degree data)))"
      unfolding trace_composition_padding_query_lists_def
        if_P[OF conjI[OF first_trace_low
          conjI[OF composition_padded_low composition_bad]]]
      by (rule accepted_exact)
    have query_in:
        "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_trace_composition_padding_query_head_lists
            prefix prefix_state data query_start"
      unfolding ro_trace_composition_padding_query_head_lists_def
        if_P[OF degree_bound]
      by (rule raws_in)
    have actual:
        "ro_query_head_dependent_actual_query_index_list_hit
          ro_trace_composition_padding_query_head_lists
          (Some ((((prefix, prefix_state), data, query_start, raws,
            query_states), attacker_state)))"
      unfolding ro_query_head_dependent_actual_query_index_list_hit_def
      using query_in by simp
    then show ?thesis by blast
  next
    assume targets:
      "hash_map_new_output_hit
         (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
         prefix_state final_state \<or>
       hash_map_new_output_hit
         (ro_actual_query_composition_prefix_targets data query_start)
         query_start final_state"
    then show ?thesis by blast
  qed
qed

end
end
