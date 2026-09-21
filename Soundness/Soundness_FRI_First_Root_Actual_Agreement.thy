(*  Title:      Stark/Soundness_FRI_First_Root_Actual_Agreement.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_Actual_Agreement
  imports Soundness_FRI_First_Root_Augmented_Experiment
begin

context soundness
begin

definition first_trace_fri_root_prefix_trace_table
  :: "('f \<times> 'f list \<times> 'f) \<Rightarrow> 'f protocol_channel \<Rightarrow> 'f list"
  where
  "first_trace_fri_root_prefix_trace_table prefix prefix_state =
    (case prefix of (fr, _, first_root) \<Rightarrow>
      conceptual_table prefix_state fr (scale * clength))"

definition first_trace_fri_root_prefix_first_table
  :: "('f \<times> 'f list \<times> 'f) \<Rightarrow> 'f protocol_channel \<Rightarrow> 'f list"
  where
  "first_trace_fri_root_prefix_first_table prefix prefix_state =
    (case prefix of (fr, _, first_root) \<Rightarrow>
      conceptual_table prefix_state first_root (scale * clength))"

definition first_trace_fri_root_prefix_base_agreement_query_lists
  :: "('f \<times> 'f list \<times> 'f) \<Rightarrow> 'f protocol_channel \<Rightarrow> nat list set"
  where
  "first_trace_fri_root_prefix_base_agreement_query_lists
      prefix prefix_state =
    trace_table_base_agreement_query_lists
      (first_trace_fri_root_prefix_trace_table prefix prefix_state)
      (first_trace_fri_root_prefix_first_table prefix prefix_state)"


lemma accepted_fri_opening_transcript_first_trace_fri_root_prefix_agreement_or_target:
  assumes prefix_eq: "prefix = (fr, prefix_trace_bs, first_root)"
    and roots_nonempty: "trace_roots \<noteq> []"
    and first_root_eq: "trace_roots ! 0 = first_root"
    and trace_bs_nonempty: "0 < length trace_bs"
    and ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and fri:
      "accepted_fri_opening_transcript initial_state
        (Some (result, final_state))
        trace_roots trace_bs trace_final dg composition_roots composition_bs
        composition_final query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript initial_state fr trace_roots trace_final
        header_as dg composition_roots composition_final header_rest"
  shows
    "query_idxs \<in>
       first_trace_fri_root_prefix_base_agreement_query_lists
         prefix prefix_state \<or>
     hash_map_new_output_hit
       (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
       prefix_state final_state"
proof -
  have bridge:
    "query_idxs \<in>
       trace_table_base_agreement_query_lists
         (conceptual_table prefix_state fr (scale * clength))
         (conceptual_table prefix_state (trace_roots ! 0)
           (scale * clength)) \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {fr, trace_roots ! 0} prefix_state)
       prefix_state final_state"
    by (rule
        accepted_fri_opening_transcript_prefix_conceptual_trace_head_query_list_agreement_or_target
          [OF roots_nonempty trace_bs_nonempty ext clean fri header])
  show ?thesis
    using bridge
    unfolding prefix_eq first_root_eq
      first_trace_fri_root_prefix_base_agreement_query_lists_def
      first_trace_fri_root_prefix_trace_table_def
      first_trace_fri_root_prefix_first_table_def
      first_trace_fri_root_prefix_merkle_targets_def
    using clean by simp
qed


lemma first_trace_fri_root_prefix_base_agreement_query_lists_subset:
  "first_trace_fri_root_prefix_base_agreement_query_lists
      prefix prefix_state
    \<subseteq> fri_query_index_list_space"
  unfolding first_trace_fri_root_prefix_base_agreement_query_lists_def
  by (rule trace_table_base_agreement_query_lists_subset)


lemma first_trace_fri_root_prefix_base_agreement_query_lists_card_bound:
  assumes trace_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_trace_table prefix prefix_state)"
    and first_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)"
    and distinct:
      "first_trace_fri_root_prefix_trace_table prefix prefix_state \<noteq>
        first_trace_fri_root_prefix_first_table prefix prefix_state"
  shows
    "card
        (first_trace_fri_root_prefix_base_agreement_query_lists
          prefix prefix_state)
      \<le> clength ^ rounds"
proof -
  have agreement_le:
    "card
        (trace_table_base_agreement_indices
          (first_trace_fri_root_prefix_trace_table prefix prefix_state)
          (first_trace_fri_root_prefix_first_table prefix prefix_state))
      \<le> clength"
    using trace_table_base_agreement_indices_card_bound
        [OF trace_low first_low distinct]
    by simp
  show ?thesis
    unfolding first_trace_fri_root_prefix_base_agreement_query_lists_def
      card_trace_table_base_agreement_query_lists
    by (rule power_mono[OF agreement_le]) simp
qed


lemma first_trace_fri_root_prefix_base_agreement_relation_fiber_bound:
  assumes trace_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_trace_table prefix prefix_state)"
    and first_low:
      "trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)"
    and distinct:
      "first_trace_fri_root_prefix_trace_table prefix prefix_state \<noteq>
        first_trace_fri_root_prefix_first_table prefix prefix_state"
  shows
    "query_index_raw_list_relation_fiber_bound
        (first_trace_fri_root_prefix_base_agreement_query_lists
          prefix prefix_state)
      \<le> rounds * query_raw_preimage_card_envelope clength"
  unfolding first_trace_fri_root_prefix_base_agreement_query_lists_def
  by (rule
      query_index_raw_list_relation_fiber_bound_base_agreement_parameter_le
        [OF trace_low first_low distinct])

end
end
