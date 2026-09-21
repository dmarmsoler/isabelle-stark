theory Soundness_FRI_Robust_Balanced_Decoded_Rectangle
  imports
    Stark.Soundness_FRI_Robust_Decoded_Rectangle
    Stark.Soundness_FRI_Robust_Balanced_Actual_Query
    Stark.Soundness_FRI_Query_Head_Adaptive_Rectangle_Family
    Stark.Soundness_FRI_Conditioned_Trace_Composition_Padding_Relation
begin

context soundness
begin

definition balanced_decoded_semantic_query_index_bound :: "nat \<Rightarrow> nat"
where
  "balanced_decoded_semantic_query_index_bound C =
    trace_composition_padding_query_index_bound +
    fri_balanced_radius (ceil_log clength) C 0 +
    fri_balanced_radius (ceil_log (Suc maxDegree)) C 0"

definition ro_balanced_decoded_semantic_query_indices
where
  "ro_balanced_decoded_semantic_query_indices
      C prefix prefix_state data query_start =
    (let d = to_nat (staged_degree data);
         fri_table =
           first_trace_fri_root_prefix_first_table prefix prefix_state;
         composition_table =
           ro_actual_query_composition_candidate data query_start;
         decoded_trace =
           fri_canonical_decoded_table (clength - 1) fri_table;
         decoded_composition =
           fri_canonical_decoded_table d composition_table;
         trace_radius = fri_balanced_radius (ceil_log clength) C 0;
         composition_radius =
           fri_balanced_radius (ceil_log (Suc d)) C 0
     in if
       d \<le> maxDegree \<and>
       fri_rs_distance_to_code
          (fri_padded_degree_bound (clength - 1))
          eval_domain (nth fri_table) \<le> trace_radius \<and>
       fri_rs_distance_to_code
          (fri_padded_degree_bound d)
          eval_domain (nth composition_table) \<le> composition_radius \<and>
       \<not> (composition_table_low_degree maxDegree decoded_composition \<and>
         all_queries_consistent decoded_trace decoded_composition
           (staged_alphas data))
     then ro_actual_query_trace_composition_accepted_indices
       prefix prefix_state data query_start
     else {})"

definition ro_balanced_decoded_semantic_query_lists
where
  "ro_balanced_decoded_semantic_query_lists
      C prefix prefix_state data query_start =
    fri_conditioned_query_lists
      (ro_balanced_decoded_semantic_query_indices
        C prefix prefix_state data query_start)"


lemma ro_balanced_decoded_semantic_query_lists_rectangle_cover:
  "ro_balanced_decoded_semantic_query_lists
      C prefix prefix_state data query_start
    \<subseteq> fri_conditioned_query_lists
      (ro_balanced_decoded_semantic_query_indices
        C prefix prefix_state data query_start)"
  unfolding ro_balanced_decoded_semantic_query_lists_def by simp

lemma ro_balanced_decoded_semantic_query_indices_subset:
  "ro_balanced_decoded_semantic_query_indices
      C prefix prefix_state data query_start \<subseteq> query_sample_space"
  unfolding ro_balanced_decoded_semantic_query_indices_def Let_def
  using ro_actual_query_trace_composition_accepted_indices_subset[
    of prefix prefix_state data query_start]
  by auto

lemma trace_composition_query_index_bound_le_padding_balanced:
  "trace_composition_query_index_bound \<le>
    trace_composition_padding_query_index_bound"
proof -
  have exact:
      "trace_composition_query_index_bound =
        trace_composition_query_index_bound_for maxDegree"
    unfolding trace_composition_query_index_bound_def
      trace_composition_query_index_bound_for_def
      query_agreement_bound_def query_agreement_bound_for_def
    by simp
  have mono:
      "trace_composition_query_index_bound_for maxDegree \<le>
        trace_composition_query_index_bound_for
          (fri_padded_degree_bound maxDegree)"
    by (rule trace_composition_query_index_bound_for_mono)
      (rule fri_degree_le_padded_degree_bound)
  show ?thesis
    unfolding trace_composition_padding_query_index_bound_def exact
    by (rule mono)
qed

lemma fri_balanced_radius_initial_mono_decoded:
  assumes "m \<le> M"
  shows "fri_balanced_radius m C 0 \<le> fri_balanced_radius M C 0"
  by (rule fri_balanced_radius_initial_mono[OF assms])


lemma card_ro_balanced_decoded_semantic_query_indices:
  "card (ro_balanced_decoded_semantic_query_indices
      C prefix prefix_state data query_start)
    \<le> balanced_decoded_semantic_query_index_bound C"
proof -
  let ?d = "to_nat (staged_degree data)"
  let ?fri_table =
    "first_trace_fri_root_prefix_first_table prefix prefix_state"
  let ?composition =
    "ro_actual_query_composition_candidate data query_start"
  let ?decoded_trace =
    "fri_canonical_decoded_table (clength - 1) ?fri_table"
  let ?decoded_composition =
    "fri_canonical_decoded_table ?d ?composition"
  let ?trace_radius = "fri_balanced_radius (ceil_log clength) C 0"
  let ?composition_radius =
    "fri_balanced_radius (ceil_log (Suc ?d)) C 0"
  let ?accepted =
    "ro_actual_query_trace_composition_accepted_indices
      prefix prefix_state data query_start"
  let ?active =
    "?d \<le> maxDegree \<and>
     fri_rs_distance_to_code
       (fri_padded_degree_bound (clength - 1))
       eval_domain (nth ?fri_table) \<le> ?trace_radius \<and>
     fri_rs_distance_to_code
       (fri_padded_degree_bound ?d)
       eval_domain (nth ?composition) \<le> ?composition_radius \<and>
     \<not> (composition_table_low_degree maxDegree ?decoded_composition \<and>
       all_queries_consistent ?decoded_trace ?decoded_composition
         (staged_alphas data))"
  show ?thesis
  proof (cases ?active)
    case inactive: False
    show ?thesis
      unfolding ro_balanced_decoded_semantic_query_indices_def Let_def
        if_not_P[OF inactive]
      by simp
  next
    case active: True
    then have degree: "?d \<le> maxDegree"
      and trace_close:
        "fri_rs_distance_to_code
          (fri_padded_degree_bound (clength - 1))
          eval_domain (nth ?fri_table) \<le> ?trace_radius"
      and composition_close:
        "fri_rs_distance_to_code
          (fri_padded_degree_bound ?d)
          eval_domain (nth ?composition) \<le> ?composition_radius"
      and not_all:
        "\<not> (composition_table_low_degree maxDegree ?decoded_composition \<and>
          all_queries_consistent ?decoded_trace ?decoded_composition
            (staged_alphas data))"
      by blast+
    have original_length:
        "length
          (conceptual_table prefix_state (staged_trace_root data)
            (scale * clength)) = length eval_domain"
      using eval_domain_length by (simp add: mult.commute)
    have composition_length: "length ?composition = length eval_domain"
      unfolding ro_actual_query_composition_candidate_def
      using eval_domain_length by (simp add: mult.commute)
    have split:
        "(\<not> composition_table_low_degree maxDegree
              ?decoded_composition \<and>
            card ?accepted \<le>
              trace_composition_query_index_bound_for
                (fri_padded_degree_bound ?d) +
              ?trace_radius + ?composition_radius) \<or>
         (composition_table_low_degree maxDegree ?decoded_composition \<and>
            \<not> all_queries_consistent
              ?decoded_trace ?decoded_composition (staged_alphas data) \<and>
            card ?accepted \<le>
              trace_composition_query_index_bound +
              ?trace_radius + ?composition_radius) \<or>
         (composition_table_low_degree maxDegree ?decoded_composition \<and>
            all_queries_consistent
              ?decoded_trace ?decoded_composition (staged_alphas data))"
      unfolding ro_actual_query_trace_composition_accepted_indices_def
      by (rule robust_two_decodes_semantic_trichotomy[
        OF original_length composition_length trace_close composition_close])
    have padded_degree:
        "fri_padded_degree_bound ?d \<le>
          fri_padded_degree_bound maxDegree"
      by (rule fri_padded_degree_bound_mono[OF degree])
    have padded_bound:
        "trace_composition_query_index_bound_for
            (fri_padded_degree_bound ?d) \<le>
          trace_composition_padding_query_index_bound"
      unfolding trace_composition_padding_query_index_bound_def
      by (rule trace_composition_query_index_bound_for_mono[OF padded_degree])
    have composition_radius_bound:
        "?composition_radius \<le>
          fri_balanced_radius (ceil_log (Suc maxDegree)) C 0"
    proof (rule fri_balanced_radius_initial_mono)
      show "ceil_log (Suc ?d) \<le> ceil_log (Suc maxDegree)"
        by (rule ceil_log_mono) (use degree in simp)
    qed
    have accepted_bound:
        "card ?accepted \<le>
          balanced_decoded_semantic_query_index_bound C"
    proof -
      from split show ?thesis
      proof
        assume first:
            "\<not> composition_table_low_degree maxDegree
                ?decoded_composition \<and>
              card ?accepted \<le>
                trace_composition_query_index_bound_for
                  (fri_padded_degree_bound ?d) +
                ?trace_radius + ?composition_radius"
        show ?thesis
          using first padded_bound composition_radius_bound
          unfolding balanced_decoded_semantic_query_index_bound_def
          by linarith
      next
        assume rest:
            "(composition_table_low_degree maxDegree ?decoded_composition \<and>
                \<not> all_queries_consistent
                  ?decoded_trace ?decoded_composition (staged_alphas data) \<and>
                card ?accepted \<le>
                  trace_composition_query_index_bound +
                  ?trace_radius + ?composition_radius) \<or>
             (composition_table_low_degree maxDegree ?decoded_composition \<and>
                all_queries_consistent
                  ?decoded_trace ?decoded_composition (staged_alphas data))"
        then show ?thesis
        proof
          assume second:
              "composition_table_low_degree maxDegree ?decoded_composition \<and>
                \<not> all_queries_consistent
                  ?decoded_trace ?decoded_composition (staged_alphas data) \<and>
                card ?accepted \<le>
                  trace_composition_query_index_bound +
                  ?trace_radius + ?composition_radius"
          show ?thesis
            using second trace_composition_query_index_bound_le_padding
              composition_radius_bound
            unfolding balanced_decoded_semantic_query_index_bound_def
            by linarith
        next
          assume third:
              "composition_table_low_degree maxDegree ?decoded_composition \<and>
                all_queries_consistent
                  ?decoded_trace ?decoded_composition (staged_alphas data)"
          then show ?thesis
            using not_all by contradiction
        qed
      qed
    qed
    show ?thesis
      unfolding ro_balanced_decoded_semantic_query_indices_def Let_def
        if_P[OF active]
      by (rule accepted_bound)
  qed
qed


definition ro_checked_staged_balanced_decoded_semantic_rectangle_error_adaptive
  :: "nat \<Rightarrow> staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_balanced_decoded_semantic_rectangle_error_adaptive
      C budgets =
    (nnreal
        (query_raw_preimage_card_envelope
          (balanced_decoded_semantic_query_index_bound C)) /
      nnreal size) ^
    (rounds - staged_attacker_query_budget budgets)"

lemma
  wp_ro_checked_staged_balanced_decoded_semantic_rectangle_bound_adaptive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_actual_query_index_list_hit
        (ro_balanced_decoded_semantic_query_lists C))
      adversary_initial_state
    \<le>
    ro_checked_staged_balanced_decoded_semantic_rectangle_error_adaptive
      C budgets"
  unfolding
    ro_checked_staged_balanced_decoded_semantic_rectangle_error_adaptive_def
proof (rule
    wp_ro_query_head_dependent_actual_query_index_list_hit_adaptive_rectangle_bound[
      OF wf controlled,
      where I="ro_balanced_decoded_semantic_query_indices C"])
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "ro_balanced_decoded_semantic_query_lists
        C prefix prefix_state data query_start
      \<subseteq> fri_conditioned_query_lists
        (ro_balanced_decoded_semantic_query_indices
          C prefix prefix_state data query_start)"
    by (rule ro_balanced_decoded_semantic_query_lists_rectangle_cover)
next
  fix prefix prefix_state data query_start t
  assume
    "Some (((prefix, prefix_state), data, query_start), t) \<in>
      set_dist
        (execute
          (ro_checked_staged_first_root_query_head_program A)
          adversary_initial_state)"
  show
    "ro_balanced_decoded_semantic_query_indices
        C prefix prefix_state data query_start \<subseteq> query_sample_space"
    by (rule ro_balanced_decoded_semantic_query_indices_subset)
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
      (ro_balanced_decoded_semantic_query_indices
        C prefix prefix_state data query_start)
      \<le> balanced_decoded_semantic_query_index_bound C"
    by (rule card_ro_balanced_decoded_semantic_query_indices)
qed


end
end
