(*  Title:      Stark/Soundness_FRI_Prechallenge_Selected_Query_Product.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Prechallenge_Selected_Query_Product
  imports Soundness_FRI_First_Root_Prefix
begin

text \<open>
  The prefix selector from the first-root decomposition determines the two
  conceptual trace tables used by the query-local bridge.  This layer packages
  their state-dependent exact fresh-query product and connects an accepted
  transcript to the selected agreement family modulo one shared Merkle target.
\<close>

context soundness
begin

definition selected_prechallenge_trace_table
  :: "'f staged_adversary \<Rightarrow> 'f staged_proof_data \<Rightarrow>
      'f protocol_channel \<Rightarrow> 'f list"
  where
  "selected_prechallenge_trace_table A data attacker_state =
    conceptual_table
      (first_trace_fri_root_prefix_state_for A data attacker_state)
      (staged_trace_root data) (scale * clength)"

definition selected_prechallenge_first_fri_table
  :: "'f staged_adversary \<Rightarrow> 'f staged_proof_data \<Rightarrow>
      'f protocol_channel \<Rightarrow> 'f list"
  where
  "selected_prechallenge_first_fri_table A data attacker_state =
    conceptual_table
      (first_trace_fri_root_prefix_state_for A data attacker_state)
      (staged_trace_fri_roots data ! 0) (scale * clength)"

definition selected_prechallenge_base_agreement_query_lists
  :: "'f staged_adversary \<Rightarrow> 'f staged_proof_data \<Rightarrow>
      'f protocol_channel \<Rightarrow> nat list set"
  where
  "selected_prechallenge_base_agreement_query_lists A data attacker_state =
    trace_table_base_agreement_query_lists
      (selected_prechallenge_trace_table A data attacker_state)
      (selected_prechallenge_first_fri_table A data attacker_state)"

lemma checked_staged_security_selected_prechallenge_base_agreement_path_fresh_product_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_low:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (selected_prechallenge_trace_table A data attacker_state)"
    and first_low:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<Longrightarrow>
        trace_table_low_degree
          (selected_prechallenge_first_fri_table A data attacker_state)"
    and distinct:
      "\<And>data attacker_state.
        Some (data, attacker_state) \<in>
          set_dist
            (execute (checked_staged_transcript_program A)
              adversary_initial_state) \<Longrightarrow>
        selected_prechallenge_trace_table A data attacker_state \<noteq>
          selected_prechallenge_first_fri_table A data attacker_state"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_dependent_query_index_list_path_fresh
        (selected_prechallenge_base_agreement_query_lists A))
      adversary_initial_state \<le>
      nnreal (clength ^ rounds) *
        (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds"
  unfolding selected_prechallenge_base_agreement_query_lists_def
  by (rule
      checked_staged_security_with_data_state_dependent_base_agreement_path_fresh_product_bound
        [OF wf controlled trace_low first_low distinct])

lemma accepted_fri_opening_transcript_selected_prechallenge_query_list_agreement_or_target:
  assumes nonempty: "0 < ceil_log clength"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and trace_bs_nonempty: "0 < length trace_bs"
    and ext:
      "first_trace_fri_root_prefix_state_for A data attacker_state \<le>
        final_state"
    and clean:
      "\<not> hash_map_output_collision
        (first_trace_fri_root_prefix_state_for A data attacker_state)"
    and fri:
      "accepted_fri_opening_transcript initial_state
        (Some (result, final_state))
        (staged_trace_fri_roots data) trace_bs trace_final dg
        composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript initial_state
        (staged_trace_root data) (staged_trace_fri_roots data) trace_final
        header_as dg composition_roots composition_final header_rest"
  shows
    "query_idxs \<in>
       selected_prechallenge_base_agreement_query_lists A data attacker_state \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets
         {staged_trace_root data, staged_trace_fri_roots data ! 0}
         (first_trace_fri_root_prefix_state_for A data attacker_state))
       (first_trace_fri_root_prefix_state_for A data attacker_state)
       final_state"
proof -
  have roots_nonempty: "staged_trace_fri_roots data \<noteq> []"
    by (rule first_trace_fri_root_prefix_state_for_data(1)
        [OF nonempty builder])
  have bridge:
    "query_idxs \<in>
       trace_table_base_agreement_query_lists
         (conceptual_table
           (first_trace_fri_root_prefix_state_for A data attacker_state)
           (staged_trace_root data) (scale * clength))
         (conceptual_table
           (first_trace_fri_root_prefix_state_for A data attacker_state)
           (staged_trace_fri_roots data ! 0) (scale * clength)) \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets
         {staged_trace_root data, staged_trace_fri_roots data ! 0}
         (first_trace_fri_root_prefix_state_for A data attacker_state))
       (first_trace_fri_root_prefix_state_for A data attacker_state)
       final_state"
    by (rule
        accepted_fri_opening_transcript_prefix_conceptual_trace_head_query_list_agreement_or_target
          [OF roots_nonempty trace_bs_nonempty ext clean fri header])
  show ?thesis
    using bridge
    unfolding selected_prechallenge_base_agreement_query_lists_def
      selected_prechallenge_trace_table_def
      selected_prechallenge_first_fri_table_def .
qed

end

end
