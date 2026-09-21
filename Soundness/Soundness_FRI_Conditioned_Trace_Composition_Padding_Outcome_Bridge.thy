theory Soundness_FRI_Conditioned_Trace_Composition_Padding_Outcome_Bridge
  imports
    Stark.Soundness_FRI_Conditioned_Trace_Composition_Padding_Relation
    Stark.Soundness_FRI_Conditioned_Composition_Outcome_Bridge
begin

context soundness
begin

lemma trace_composition_padding_absorbed_query_relation_prefix_activeI:
  assumes clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values attacker_state"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and query_start_ext: "query_start \<le> attacker_state"
    and prefix_eq:
      "prefix =
        (staged_trace_root data, [],
          trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data))"
    and no_trace_merkle:
      "\<not> hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state attacker_state"
    and no_composition_merkle:
      "\<not> hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets data query_start)
        query_start attacker_state"
    and header_chain:
      "ro_absorb_lookup_chain attacker_state (PState adversary_initial_state)
        (verifier_header_messages (staged_trace_root data)
          (staged_trace_fri_roots data) (staged_trace_final data)
          (staged_alphas data) (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)) (PState query_start)"
    and query_chain:
      "ro_absorb_lookup_chain attacker_state (PState query_start)
        (List.concat (take j (staged_query_chunks data)))
        (PState (query_states ! j))"
    and trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    and alpha_len: "length (staged_alphas data) = length spec"
    and composition_len:
      "length (staged_composition_fri_roots data) =
        ceil_log (to_nat (staged_degree data) + 1)"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and raws_len: "length raws = rounds"
    and raws_in:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        trace_composition_padding_query_lists
          (conceptual_table prefix_state (staged_trace_root data)
            (scale * clength))
          (first_trace_fri_root_prefix_first_table prefix prefix_state)
          (ro_actual_query_composition_candidate data query_start)
          (staged_alphas data)
          (fri_padded_degree_bound (to_nat (staged_degree data)))"
    and j_bound: "j < rounds"
    and lookup:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge j (PState (query_states ! j))) =
        Some (raws ! j)"
  shows
    "hash_state_relation_active
      trace_composition_padding_absorbed_query_relation
      (HashMap attacker_state)
      (QueryIndexChallenge j (PState (query_states ! j))) (raws ! j)"
proof -
  let ?selected =
    "trace_composition_header_trace_root
      (staged_trace_root data) (staged_trace_fri_roots data)"
  let ?final = "channel_for_hash_map (HashMap attacker_state)"
  have final_map: "HashMap ?final = HashMap attacker_state"
    unfolding channel_for_hash_map_def adversary_initial_state_def by simp
  have clean_final: "\<not> hash_map_output_collision ?final"
    using clean final_map unfolding hash_map_output_collision_def by simp
  have no_initial_final:
      "PState adversary_initial_state \<notin> hash_map_output_values ?final"
    using no_initial final_map unfolding hash_map_output_values_def by simp
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision attacker_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_ext])
    then show False using clean by contradiction
  qed
  have original_targets:
      "merkle_prefix_path_targets {staged_trace_root data} prefix_state \<subseteq>
        first_trace_fri_root_prefix_merkle_targets prefix prefix_state"
    unfolding prefix_eq first_trace_fri_root_prefix_merkle_targets_def
    using prefix_clean
    by (simp add: merkle_prefix_path_targets_mono)
  have selected_targets:
      "merkle_prefix_path_targets {?selected} prefix_state \<subseteq>
        first_trace_fri_root_prefix_merkle_targets prefix prefix_state"
    unfolding prefix_eq first_trace_fri_root_prefix_merkle_targets_def
    using prefix_clean
    by (simp add: merkle_prefix_path_targets_mono)
  have no_original:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {staged_trace_root data} prefix_state)
        prefix_state attacker_state"
    using no_trace_merkle
      hash_map_new_output_hit_subset[OF original_targets]
    by blast
  have no_selected:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {?selected} prefix_state)
        prefix_state attacker_state"
    using no_trace_merkle
      hash_map_new_output_hit_subset[OF selected_targets]
    by blast
  have original_final:
      "conceptual_table ?final (staged_trace_root data) (scale * clength) =
       conceptual_table prefix_state (staged_trace_root data) (scale * clength)"
  proof -
    have A:
        "conceptual_table ?final (staged_trace_root data) (scale * clength) =
          conceptual_table attacker_state (staged_trace_root data)
            (scale * clength)"
      by (rule conceptual_table_cong_hash_map[OF final_map])
    have B:
        "conceptual_table attacker_state (staged_trace_root data)
            (scale * clength) =
          conceptual_table prefix_state (staged_trace_root data)
            (scale * clength)"
      by (rule conceptual_table_prefix_stable_if_no_target[
        OF prefix_ext no_original])
    show ?thesis using A B by simp
  qed
  have first_final:
      "first_trace_fri_root_prefix_first_table
          (staged_trace_root data, [], ?selected) ?final =
        first_trace_fri_root_prefix_first_table prefix prefix_state"
  proof -
    have A:
        "conceptual_table ?final ?selected (scale * clength) =
          conceptual_table attacker_state ?selected (scale * clength)"
      by (rule conceptual_table_cong_hash_map[OF final_map])
    have B:
        "conceptual_table attacker_state ?selected (scale * clength) =
          conceptual_table prefix_state ?selected (scale * clength)"
      by (rule conceptual_table_prefix_stable_if_no_target[
        OF prefix_ext no_selected])
    show ?thesis
      unfolding first_trace_fri_root_prefix_first_table_def prefix_eq
      using A B by simp
  qed
  have composition_final:
      "ro_actual_query_composition_candidate
          (ro_trace_composition_header_data (staged_trace_root data)
            (staged_trace_fri_roots data) (staged_trace_final data)
            (staged_alphas data) (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)) ?final =
        ro_actual_query_composition_candidate data query_start"
  proof (cases "staged_composition_fri_roots data = []")
    case True
    then show ?thesis
      unfolding ro_actual_query_composition_candidate_def by simp
  next
    case False
    have no_composition:
        "\<not> hash_map_new_output_hit
          (merkle_prefix_path_targets
            {hd (staged_composition_fri_roots data)} query_start)
          query_start attacker_state"
      using no_composition_merkle False
      unfolding ro_actual_query_composition_prefix_targets_def by simp
    have A:
        "conceptual_table ?final
            (hd (staged_composition_fri_roots data)) (scale * clength) =
          conceptual_table attacker_state
            (hd (staged_composition_fri_roots data)) (scale * clength)"
      by (rule conceptual_table_cong_hash_map[OF final_map])
    have B:
        "conceptual_table attacker_state
            (hd (staged_composition_fri_roots data)) (scale * clength) =
          conceptual_table query_start
            (hd (staged_composition_fri_roots data)) (scale * clength)"
      by (rule conceptual_table_prefix_stable_if_no_target[
        OF query_start_ext no_composition])
    show ?thesis
      unfolding ro_actual_query_composition_candidate_def
      using False A B by simp
  qed
  have query_lists_final:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_trace_composition_padding_header_query_lists
          (HashMap attacker_state)
          (staged_trace_root data) (staged_trace_fri_roots data)
          (staged_trace_final data) (staged_alphas data)
          (staged_degree data) (staged_composition_fri_roots data)
          (staged_composition_final data)"
    unfolding ro_trace_composition_padding_header_query_lists_def
      if_P[OF degree_bound]
    using raws_in original_final first_final composition_final by simp
  have header_chain_final:
      "ro_absorb_lookup_chain ?final (PState adversary_initial_state)
        (verifier_header_messages (staged_trace_root data)
          (staged_trace_fri_roots data) (staged_trace_final data)
          (staged_alphas data) (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)) (PState query_start)"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule header_chain)
  have query_chain_final:
      "ro_absorb_lookup_chain ?final (PState query_start)
        (List.concat (take j (staged_query_chunks data)))
        (PState (query_states ! j))"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule query_chain)
  show ?thesis
    by (rule trace_composition_padding_absorbed_query_relation_activeI[
      OF clean_final no_initial_final trace_len alpha_len composition_len
        header_chain_final query_chain_final raws_len query_lists_final
        j_bound lookup])
qed

lemma
  checked_builder_trace_composition_padding_bad_imp_transition_or_targets:
  fixes final_state :: "'f protocol_channel"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and builder_out:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in> set_dist
        (execute
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
          adversary_initial_state)"
    and verifier_out:
      "Some (results, final_state) \<in> set_dist
        (execute ro_verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    and final_clean: "\<not> hash_map_output_collision final_state"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values attacker_state"
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
    "hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state \<or>
     hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets data query_start)
        query_start final_state \<or>
     hash_state_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          trace_composition_padding_absorbed_query_relation)
        (HashMap adversary_initial_state) (HashMap attacker_state)"
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
    have original_out:
        "Some (data, attacker_state) \<in>
          set_dist (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
      by (rule
        ro_checked_staged_transcript_program_with_first_root_projection_outcome[
          OF nonempty builder_out])
    have attacker_verifier_ext:
        "attacker_state \<le> verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      by (rule hash_extends_verifier_state_from_adversary_right)
        (rule hash_ext_refl)
    have verifier_final_ext:
        "verifier_state_from_adversary attacker_state
            (staged_proof_transcript data) \<le> final_state"
      using ro_checked_staged_transcript_program_ro_verify_monad_sync[
        OF wf controlled original_out verifier_out] by blast
    have attacker_final_ext: "attacker_state \<le> final_state"
      by (rule hash_ext_trans[OF attacker_verifier_ext verifier_final_ext])
    have attacker_clean: "\<not> hash_map_output_collision attacker_state"
    proof
      assume collision: "hash_map_output_collision attacker_state"
      have "hash_map_output_collision final_state"
        by (rule hash_map_output_collision_mono[OF collision attacker_final_ext])
      then show False using final_clean by contradiction
    qed
    have outcome_props:
        "length raws = rounds \<and> query_start \<le> attacker_state \<and>
         (\<forall>j < rounds.
           fmlookup (HashMap attacker_state)
             (QueryIndexChallenge (PQueryCounter (query_states ! j))
               (PState (query_states ! j))) = Some (raws ! j))"
      using
        ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
          OF wf controlled builder_out]
      by blast
    have witness_props:
        "length raws = rounds \<and>
         PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
         (\<forall>j < rounds.
           PQueryCounter (query_states ! j) =
             PQueryCounter query_start + j \<and>
           fmlookup (HashMap attacker_state)
             (QueryIndexChallenge (PQueryCounter (query_states ! j))
               (PState (query_states ! j))) = Some (raws ! j))"
      using ro_checked_staged_transcript_program_with_query_witnesses_outcome[
        OF wf controlled
          ro_checked_staged_transcript_program_with_first_root_witnesses_projection_outcome[
            OF nonempty builder_out]]
      by blast
    have good_fields:
        "prefix_state \<le> attacker_state \<and> PQueryCounter query_start = 0"
      using ro_checked_staged_transcript_program_with_first_root_good_fields[
        OF wf controlled nonempty builder_out] by blast
    have shape:
        "length (staged_trace_fri_roots data) = ceil_log clength \<and>
         length (staged_alphas data) = length spec \<and>
         length (staged_composition_fri_roots data) =
           ceil_log (to_nat (staged_degree data) + 1) \<and>
         length (staged_query_chunks data) = rounds"
      using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
      by blast
    have degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
      using ro_absorb_checked_staged_first_root_actual_query_accepted_evidence[
        OF wf controlled nonempty builder_out verifier_out final_clean]
      by blast
    have rounds_pos: "0 < rounds" by (rule rounds_positive)
    have chains:
        "prefix =
          (staged_trace_root data, [], hd (staged_trace_fri_roots data)) \<and>
         ro_absorb_lookup_chain attacker_state (PState adversary_initial_state)
           (verifier_header_messages (staged_trace_root data)
             (staged_trace_fri_roots data) (staged_trace_final data)
             (staged_alphas data) (staged_degree data)
             (staged_composition_fri_roots data)
             (staged_composition_final data))
           (PState query_start) \<and>
         ro_absorb_lookup_chain attacker_state (PState query_start)
           (List.concat (take 0 (staged_query_chunks data)))
           (PState (query_states ! 0))"
      by (rule
        ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain[
          OF wf controlled nonempty builder_out attacker_clean rounds_pos])
    have trace_roots_nonempty: "staged_trace_fri_roots data \<noteq> []"
      using shape nonempty by auto
    have prefix_selector:
        "prefix =
          (staged_trace_root data, [],
            trace_composition_header_trace_root
              (staged_trace_root data) (staged_trace_fri_roots data))"
      using chains trace_roots_nonempty
      by (simp add: trace_composition_header_trace_root_nonempty)
    show ?thesis
    proof (cases
        "hash_map_new_output_hit
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
          prefix_state final_state")
      case True
      then show ?thesis by simp
    next
      case no_trace: False
      show ?thesis
      proof (cases
          "hash_map_new_output_hit
            (ro_actual_query_composition_prefix_targets data query_start)
            query_start final_state")
        case True
        then show ?thesis by simp
      next
        case no_composition: False
        have no_trace_attacker:
            "\<not> hash_map_new_output_hit
              (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
              prefix_state attacker_state"
          using no_trace
            hash_map_new_output_hit_extend_final[OF attacker_final_ext]
          by blast
        have no_composition_attacker:
            "\<not> hash_map_new_output_hit
              (ro_actual_query_composition_prefix_targets data query_start)
              query_start attacker_state"
          using no_composition
            hash_map_new_output_hit_extend_final[OF attacker_final_ext]
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
        have witness0:
            "PQueryCounter (query_states ! 0) =
               PQueryCounter query_start + 0 \<and>
             fmlookup (HashMap attacker_state)
               (QueryIndexChallenge (PQueryCounter (query_states ! 0))
                 (PState (query_states ! 0))) = Some (raws ! 0)"
          using witness_props rounds_pos by blast
        have counter0: "PQueryCounter (query_states ! 0) = 0"
          using witness0 good_fields by simp
        have lookup0:
            "fmlookup (HashMap attacker_state)
              (QueryIndexChallenge 0 (PState (query_states ! 0))) =
              Some (raws ! 0)"
          using witness0 counter0 by simp
        have active:
            "hash_state_relation_active
              trace_composition_padding_absorbed_query_relation
              (HashMap attacker_state)
              (QueryIndexChallenge 0 (PState (query_states ! 0)))
              (raws ! 0)"
          by (rule
            trace_composition_padding_absorbed_query_relation_prefix_activeI[
              OF attacker_clean no_initial good_fields[THEN conjunct1]
                outcome_props[THEN conjunct2, THEN conjunct1]
                prefix_selector no_trace_attacker no_composition_attacker])
            (use chains shape degree_bound outcome_props raws_in rounds_pos
              lookup0 in simp_all)
        have domain:
            "card (fmdom' (HashMap attacker_state)) \<le>
              ro_checked_staged_transcript_hash_query_budget_for budgets"
          by (rule
            ro_checked_staged_transcript_program_with_first_root_map_domain_bound[
              OF wf controlled nonempty builder_out attacker_clean])
        have transition:
            "hash_state_relation_transition
              (conditioned_fri_relation_bounded
                (ro_checked_staged_transcript_hash_query_budget_for budgets)
                trace_composition_padding_absorbed_query_relation)
              (HashMap adversary_initial_state) (HashMap attacker_state)"
          by (rule conditioned_relation_active_imp_bounded_initial_transition[
            OF _ domain])
            (use active in blast)
        then show ?thesis by simp
      qed
    qed
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