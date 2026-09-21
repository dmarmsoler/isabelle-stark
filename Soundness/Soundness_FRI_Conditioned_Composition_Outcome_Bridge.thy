theory Soundness_FRI_Conditioned_Composition_Outcome_Bridge
  imports
    Stark.Soundness_FRI_Conditioned_Composition_Padding_Relation
    Stark.Soundness_FRI_Conditioned_Prequery_Outcome_Bridge
begin

context soundness
begin

lemma composition_padding_absorbed_query_relation_prefix_activeI:
  assumes clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial: "PState adversary_initial_state \<notin> hash_map_output_values attacker_state"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and query_start_ext: "query_start \<le> attacker_state"
    and no_original_merkle:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {staged_trace_root data} prefix_state)
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
    and trace_len: "length (staged_trace_fri_roots data) = ceil_log clength"
    and alpha_len: "length (staged_alphas data) = length spec"
    and composition_len:
      "length (staged_composition_fri_roots data) =
        ceil_log (to_nat (staged_degree data) + 1)"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and raws_len: "length raws = rounds"
    and raws_in:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        composition_padding_query_lists
          (conceptual_table prefix_state (staged_trace_root data)
            (scale * clength))
          (ro_actual_query_composition_candidate data query_start)
          (staged_alphas data)
          (fri_padded_degree_bound (to_nat (staged_degree data)))"
    and j_bound: "j < rounds"
    and lookup:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge j (PState (query_states ! j))) =
        Some (raws ! j)"
  shows
    "hash_state_relation_active composition_padding_absorbed_query_relation
      (HashMap attacker_state)
      (QueryIndexChallenge j (PState (query_states ! j))) (raws ! j)"
proof -
  let ?final = "channel_for_hash_map (HashMap attacker_state)"
  have final_map: "HashMap ?final = HashMap attacker_state"
    unfolding channel_for_hash_map_def adversary_initial_state_def by simp
  have clean_final: "\<not> hash_map_output_collision ?final"
    using clean final_map unfolding hash_map_output_collision_def by simp
  have no_initial_final:
      "PState adversary_initial_state \<notin> hash_map_output_values ?final"
    using no_initial final_map unfolding hash_map_output_values_def by simp
  have original_final:
      "conceptual_table ?final (staged_trace_root data) (scale * clength) =
       conceptual_table prefix_state (staged_trace_root data) (scale * clength)"
  proof -
    have A: "conceptual_table ?final (staged_trace_root data) (scale * clength) =
        conceptual_table attacker_state (staged_trace_root data) (scale * clength)"
      by (rule conceptual_table_cong_hash_map[OF final_map])
    have B: "conceptual_table attacker_state (staged_trace_root data) (scale * clength) =
        conceptual_table prefix_state (staged_trace_root data) (scale * clength)"
      by (rule conceptual_table_prefix_stable_if_no_target[
        OF prefix_ext no_original_merkle])
    show ?thesis using A B by simp
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
    then show ?thesis unfolding ro_actual_query_composition_candidate_def by simp
  next
    case False
    have no_composition:
        "\<not> hash_map_new_output_hit
          (merkle_prefix_path_targets
            {hd (staged_composition_fri_roots data)} query_start)
          query_start attacker_state"
      using no_composition_merkle False
      unfolding ro_actual_query_composition_prefix_targets_def by simp
    have A: "conceptual_table ?final
          (hd (staged_composition_fri_roots data)) (scale * clength) =
        conceptual_table attacker_state
          (hd (staged_composition_fri_roots data)) (scale * clength)"
      by (rule conceptual_table_cong_hash_map[OF final_map])
    have B: "conceptual_table attacker_state
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
        ro_composition_padding_header_query_lists (HashMap attacker_state)
          (staged_trace_root data) (staged_trace_fri_roots data)
          (staged_trace_final data) (staged_alphas data)
          (staged_degree data) (staged_composition_fri_roots data)
          (staged_composition_final data)"
    unfolding ro_composition_padding_header_query_lists_def if_P[OF degree_bound]
    using raws_in original_final composition_final by simp
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
    by (rule composition_padding_absorbed_query_relation_activeI[
      OF clean_final no_initial_final trace_len alpha_len composition_len
        header_chain_final query_chain_final raws_len query_lists_final
        j_bound lookup])
qed

lemma hash_map_new_output_hit_extend_final:
  assumes ext: "t \<le> u"
    and hit: "hash_map_new_output_hit B s t"
  shows "hash_map_new_output_hit B s u"
proof -
  from hit obtain x y where
    none: "fmlookup (HashMap s) x = None"
    and lookup: "fmlookup (HashMap t) x = Some y"
    and y_in: "y \<in> B"
    unfolding hash_map_new_output_hit_def by blast
  have lookup_u: "fmlookup (HashMap u) x = Some y"
    by (rule hash_extension_lookup[OF lookup ext])
  show ?thesis
    unfolding hash_map_new_output_hit_def
    using none lookup_u y_in by blast
qed

lemma checked_builder_composition_padding_bad_imp_transition_or_targets:
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
    and trace_low:
      "trace_table_low_degree
        (conceptual_table prefix_state (staged_trace_root data)
          (scale * clength))"
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
          composition_padding_absorbed_query_relation)
        (HashMap adversary_initial_state) (HashMap attacker_state)"
proof -
  from ro_absorb_checked_staged_first_root_actual_query_conceptual_consistency_or_targets[
      OF wf controlled nonempty builder_out verifier_out final_clean]
  have consistency_or_targets:
      "(\<forall>j < length raws.
        query_consistent_at
          (conceptual_table prefix_state (staged_trace_root data)
            (scale * clength))
          (ro_actual_query_composition_candidate data query_start)
          (staged_alphas data) (index (to_nat (raws ! j)))) \<or>
       hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state \<or>
       hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets data query_start)
        query_start final_state"
    by blast
  then show ?thesis
  proof
    assume consistent:
      "\<forall>j < length raws.
        query_consistent_at
          (conceptual_table prefix_state (staged_trace_root data)
            (scale * clength))
          (ro_actual_query_composition_candidate data query_start)
          (staged_alphas data) (index (to_nat (raws ! j)))"
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
      using ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
        OF wf controlled builder_out] by blast
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
        have prefix_clean: "\<not> hash_map_output_collision prefix_state"
        proof
          assume collision: "hash_map_output_collision prefix_state"
          have "hash_map_output_collision attacker_state"
            by (rule hash_map_output_collision_mono[
              OF collision good_fields[THEN conjunct1]])
          then show False using attacker_clean by contradiction
        qed
        have original_targets:
            "merkle_prefix_path_targets {staged_trace_root data} prefix_state
              \<subseteq>
             first_trace_fri_root_prefix_merkle_targets prefix prefix_state"
          using chains prefix_clean
          unfolding first_trace_fri_root_prefix_merkle_targets_def
          by (simp add: merkle_prefix_path_targets_mono)
        have no_original_final:
            "\<not> hash_map_new_output_hit
              (merkle_prefix_path_targets {staged_trace_root data} prefix_state)
              prefix_state final_state"
          using no_trace hash_map_new_output_hit_subset[OF original_targets]
          by blast
        have no_original_attacker:
            "\<not> hash_map_new_output_hit
              (merkle_prefix_path_targets {staged_trace_root data} prefix_state)
              prefix_state attacker_state"
          using no_original_final
            hash_map_new_output_hit_extend_final[OF attacker_final_ext]
          by blast
        have no_composition_attacker:
            "\<not> hash_map_new_output_hit
              (ro_actual_query_composition_prefix_targets data query_start)
              query_start attacker_state"
          using no_composition
            hash_map_new_output_hit_extend_final[OF attacker_final_ext]
          by blast
        have agreement_subset:
            "set (map (\<lambda>raw. index (to_nat raw)) raws) \<subseteq>
              query_agreement_indices
                (conceptual_table prefix_state (staged_trace_root data)
                  (scale * clength))
                (ro_actual_query_composition_candidate data query_start)
                (staged_alphas data)"
        proof
          fix idx
          assume idx_in:
            "idx \<in> set (map (\<lambda>raw. index (to_nat raw)) raws)"
          then obtain j where
            j_bound: "j < length raws"
            and idx_eq: "idx = index (to_nat (raws ! j))"
            by (auto simp: in_set_conv_nth)
          have sample: "idx \<in> query_sample_space"
            unfolding idx_eq query_sample_space_def
            using index_less_query_sample_space by simp
          have consistent_idx:
              "query_consistent_at
                (conceptual_table prefix_state (staged_trace_root data)
                  (scale * clength))
                (ro_actual_query_composition_candidate data query_start)
                (staged_alphas data) idx"
            using consistent[rule_format, OF j_bound] unfolding idx_eq .
          show "idx \<in> query_agreement_indices
              (conceptual_table prefix_state (staged_trace_root data)
                (scale * clength))
              (ro_actual_query_composition_candidate data query_start)
              (staged_alphas data)"
            unfolding query_agreement_indices_def
            using sample consistent_idx by simp
        qed
        have raws_in:
            "map (\<lambda>raw. index (to_nat raw)) raws \<in>
              composition_padding_query_lists
                (conceptual_table prefix_state (staged_trace_root data)
                  (scale * clength))
                (ro_actual_query_composition_candidate data query_start)
                (staged_alphas data)
                (fri_padded_degree_bound (to_nat (staged_degree data)))"
          unfolding composition_padding_query_lists_def
            if_P[OF conjI[OF trace_low
              conjI[OF composition_padded_low composition_bad]]]
            query_index_lists_over_def
          using outcome_props agreement_subset by simp
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
          using witness0 counter0 by simp        have active:
            "hash_state_relation_active
              composition_padding_absorbed_query_relation
              (HashMap attacker_state)
              (QueryIndexChallenge 0 (PState (query_states ! 0)))
              (raws ! 0)"
          by (rule composition_padding_absorbed_query_relation_prefix_activeI[
            OF attacker_clean no_initial good_fields[THEN conjunct1]
              outcome_props[THEN conjunct2, THEN conjunct1] no_original_attacker
              no_composition_attacker])
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
                composition_padding_absorbed_query_relation)
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

lemma ro_actual_query_composition_candidate_zero_round_low_degree_any:
  assumes empty: "staged_composition_fri_roots data = []"
  shows "composition_table_low_degree d
    (ro_actual_query_composition_candidate data query_start)"
proof -
  have table:
      "replicate (scale * clength) (staged_composition_final data) =
        map (poly [:staged_composition_final data:]) eval_domain"
  proof (rule nth_equalityI)
    show "length (replicate (scale * clength)
        (staged_composition_final data)) =
      length (map (poly [:staged_composition_final data:]) eval_domain)"
      using eval_domain_length by (simp add: mult.commute)
  next
    fix i
    assume "i < length (replicate (scale * clength)
      (staged_composition_final data))"
    then show "replicate (scale * clength)
        (staged_composition_final data) ! i =
      map (poly [:staged_composition_final data:]) eval_domain ! i"
      using eval_domain_length by (simp add: mult.commute)
  qed
  show ?thesis
    unfolding ro_actual_query_composition_candidate_def empty
      composition_table_low_degree_def
    by (intro exI[of _ "[:staged_composition_final data:]"])
      (use table in simp)
qed

lemma checked_builder_composition_padded_candidate_bad_imp_conditioned_transitions_or_targets:
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
    and candidate_bad:
      "\<not> composition_table_low_degree
        (fri_padded_degree_bound (to_nat (staged_degree data)))
        (ro_actual_query_composition_candidate data query_start)"
  shows
    "hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets data query_start)
        query_start final_state \<or>
     fri_checked_builder_merkle_target_hit data attacker_state final_state \<or>
     hash_state_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          conditioned_composition_fri_bad_challenge_relation)
        (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
     hash_state_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          ro_conditioned_augmented_absorbed_query_relation)
        (HashMap adversary_initial_state) (HashMap attacker_state)"
proof -
  from ro_absorb_checked_staged_first_root_actual_query_accepted_evidence[
      OF wf controlled nonempty builder_out verifier_out final_clean]
  obtain f_fl fl fr f_final as final trace_round_layers
      composition_round_layers where
    fr_eq: "fr = staged_trace_root data"
    and trace_challenges_eq: "map fst f_fl = staged_trace_fri_challenges data"
    and trace_roots_eq: "map snd f_fl = staged_trace_fri_roots data"
    and trace_final_eq: "f_final = staged_trace_final data"
    and alphas_eq: "as = staged_alphas data"
    and composition_challenges_eq:
      "map fst fl = staged_composition_fri_challenges data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and composition_final_eq: "final = staged_composition_final data"
    and f_fl_nonempty: "f_fl \<noteq> []"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and trace_layers_len: "length trace_round_layers = length raws"
    and composition_layers_len:
      "length composition_round_layers = length raws"
    and layer_transcripts:
      "\<forall>j < length raws.
        query_round_fri_layer_transcripts
          (map (\<lambda>raw. index (to_nat raw)) raws ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)
          (trace_round_layers ! j) (composition_round_layers ! j)"
    and raw_bound:
      "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
    and accepted:
      "\<forall>round_idx < length raws.
        ro_recorded_query_fri_accepted_evidence
          fr f_fl f_final as fl final (raws ! round_idx)
          (trace_round_layers ! round_idx)
          (composition_round_layers ! round_idx) final_state"
    .
  let ?query_idxs = "map (\<lambda>raw. index (to_nat raw)) raws"
  have query_idxs_len: "length ?query_idxs = length raws" by simp
  have layer_transcripts':
      "\<forall>j < length ?query_idxs.
        query_round_fri_layer_transcripts (?query_idxs ! j)
          (map snd f_fl) (map snd fl) (staged_query_chunks data ! j)
          (trace_round_layers ! j) (composition_round_layers ! j)"
    using layer_transcripts trace_roots_eq composition_roots_eq by simp
  have composition_all_layers:
      "fri_all_round_layer_evidence
        (map snd fl) (map fst fl) ?query_idxs composition_round_layers"
    by (rule
      query_round_fri_layer_transcripts_composition_all_round_layer_evidence[
        OF _ _ layer_transcripts'])
      (use composition_layers_len query_idxs_len in simp_all)
  have composition_chain:
      "generic_fri_recorded_value_chain_evidence
        (map snd fl) (map fst fl) final ?query_idxs composition_round_layers"
    using ro_recorded_query_fri_accepted_evidence_all_value_chains[
      OF trace_layers_len composition_layers_len accepted] by blast
  have composition_authenticated:
      "generic_fri_recorded_chunks_authenticated
        (map snd fl) ?query_idxs composition_round_layers final_state"
    using ro_recorded_query_fri_accepted_evidence_all_chunks_authenticated[
      OF trace_layers_len composition_layers_len accepted] by blast
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist (execute (ro_checked_staged_transcript_program A)
          adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome[
        OF nonempty builder_out])
  have shape:
      "length (staged_composition_fri_roots data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       length (staged_composition_fri_challenges data) =
         ceil_log (to_nat (staged_degree data) + 1)"
    using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
    by blast
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
  have query_start_attacker: "query_start \<le> attacker_state"
    using ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
      OF wf controlled builder_out] by blast
  have query_start_final: "query_start \<le> final_state"
    by (rule hash_ext_trans[OF query_start_attacker attacker_final_ext])
  have roots_nonempty: "map snd fl \<noteq> []"
  proof
    assume empty: "map snd fl = []"
    have staged_empty: "staged_composition_fri_roots data = []"
      using composition_roots_eq empty by simp
    have low:
        "composition_table_low_degree
          (fri_padded_degree_bound (to_nat (staged_degree data)))
          (ro_actual_query_composition_candidate data query_start)"
      by (rule ro_actual_query_composition_candidate_zero_round_low_degree_any[
        OF staged_empty])
    show False using candidate_bad low by contradiction
  qed
  have root0:
      "map snd fl ! 0 = hd (staged_composition_fri_roots data)"
    using composition_roots_eq roots_nonempty
    by (cases "staged_composition_fri_roots data") simp_all
  have staged_roots_nonempty:
      "staged_composition_fri_roots data \<noteq> []"
    using composition_roots_eq roots_nonempty by auto
  have candidate_len:
      "length (ro_actual_query_composition_candidate data query_start) =
        clength * scale"
    unfolding ro_actual_query_composition_candidate_def
      conceptual_table_def
    by (simp add: mult.commute)
  show ?thesis
  proof (cases
      "hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets data query_start)
        query_start final_state")
    case True
    then show ?thesis by simp
  next
    case no_prefix: False
    show ?thesis
    proof (cases
        "fri_checked_builder_merkle_target_hit data attacker_state final_state")
      case True
      then show ?thesis by simp
    next
      case no_builder: False
      have no_prefix_singleton:
          "\<not> hash_map_new_output_hit
            (merkle_prefix_path_targets {map snd fl ! 0} query_start)
            query_start final_state"
        using no_prefix roots_nonempty staged_roots_nonempty root0
        unfolding ro_actual_query_composition_prefix_targets_def
        by simp
      have query_start_stable:
          "conceptual_table final_state (map snd fl ! 0)
              (length (fri_canonical_domain_at 0)) =
            conceptual_table query_start (map snd fl ! 0)
              (length (fri_canonical_domain_at 0))"
        by (rule conceptual_table_prefix_stable_if_no_target[
          OF query_start_final no_prefix_singleton])
      have no_builder_target:
          "\<not> hash_map_new_output_hit
            (merkle_prefix_path_targets (set (map snd fl)) attacker_state)
            attacker_state final_state"
      proof
        assume hit:
            "hash_map_new_output_hit
              (merkle_prefix_path_targets (set (map snd fl)) attacker_state)
              attacker_state final_state"
        have roots_subset:
            "set (map snd fl) \<subseteq>
              set (staged_trace_fri_roots data) \<union>
              set (staged_composition_fri_roots data)"
          using composition_roots_eq by auto
        have target_subset:
            "merkle_prefix_path_targets (set (map snd fl)) attacker_state
              \<subseteq> fri_checked_builder_merkle_targets data attacker_state"
          unfolding fri_checked_builder_merkle_targets_def
          by (rule merkle_prefix_path_targets_mono[OF roots_subset])
        have "hash_map_new_output_hit
            (fri_checked_builder_merkle_targets data attacker_state)
            attacker_state final_state"
          by (rule hash_map_new_output_hit_subset[OF target_subset hit])
        then show False
          using no_builder unfolding fri_checked_builder_merkle_target_hit_def
          by contradiction
      qed
      have no_builder_singleton:
          "\<not> hash_map_new_output_hit
            (merkle_prefix_path_targets {map snd fl ! 0} attacker_state)
            attacker_state final_state"
      proof
        assume hit:
            "hash_map_new_output_hit
              (merkle_prefix_path_targets {map snd fl ! 0} attacker_state)
              attacker_state final_state"
        have root_mem: "map snd fl ! 0 \<in> set (map snd fl)"
          using roots_nonempty by simp
        have target_subset:
            "merkle_prefix_path_targets {map snd fl ! 0} attacker_state
              \<subseteq>
             merkle_prefix_path_targets (set (map snd fl)) attacker_state"
          by (rule merkle_prefix_path_targets_mono)
            (use root_mem in auto)
        have "hash_map_new_output_hit
            (merkle_prefix_path_targets (set (map snd fl)) attacker_state)
            attacker_state final_state"
          by (rule hash_map_new_output_hit_subset[OF target_subset hit])
        then show False using no_builder_target by contradiction
      qed
      have attacker_stable:
          "conceptual_table final_state (map snd fl ! 0)
              (length (fri_canonical_domain_at 0)) =
            conceptual_table attacker_state (map snd fl ! 0)
              (length (fri_canonical_domain_at 0))"
        by (rule conceptual_table_prefix_stable_if_no_target[
          OF attacker_final_ext no_builder_singleton])
      have domain0_len:
          "length (fri_canonical_domain_at 0) = clength * scale"
        unfolding fri_canonical_domain_at_length by simp
      have query_attacker:
          "conceptual_table query_start (map snd fl ! 0)
              (length (fri_canonical_domain_at 0)) =
            conceptual_table attacker_state (map snd fl ! 0)
              (length (fri_canonical_domain_at 0))"
        using query_start_stable attacker_stable by simp
      have actual_at_attacker:
          "ro_actual_query_composition_candidate data query_start =
            conceptual_table attacker_state (map snd fl ! 0)
              (length (fri_canonical_domain_at 0))"
        unfolding ro_actual_query_composition_candidate_def
        using staged_roots_nonempty root0 composition_roots_eq
          query_attacker domain0_len
        by (simp add: mult.commute)      have layer0_eq:
          "fri_builder_conceptual_layers (map snd fl) attacker_state final ! 0 =
            ro_actual_query_composition_candidate data query_start"
        using fri_builder_conceptual_layers_at[
          of 0 "map snd fl" attacker_state final]
          roots_nonempty actual_at_attacker
        by simp
      have conditioned_layer0:
          "fri_conditioned_layer_table 0
              (fri_builder_conceptual_layers (map snd fl) attacker_state final ! 0) =
            ro_actual_query_composition_candidate data query_start"
        using layer0_eq candidate_len
        unfolding fri_conditioned_layer_table_def
          fri_canonical_domain_at_length
        by simp
      have start_not_low:
          "\<not> fri_table_low_degree_on
            (fri_padded_degree_bound (to_nat (staged_degree data)))
            (fri_canonical_domain_at 0)
            (fri_conditioned_layer_table 0
              (fri_builder_conceptual_layers (map snd fl) attacker_state
                final ! 0))"
        using candidate_bad conditioned_layer0
        unfolding fri_canonical_domain_at_0
          composition_table_low_degree_iff_fri_table_low_degree_on_eval_domain
        by simp
      obtain N where eval_power: "clength * scale = 2 ^ N"
        using eval_domain_length_power by blast
      have round_count:
          "length (map fst fl) =
            ceil_log (Suc (to_nat (staged_degree data)))"
        using composition_challenges_eq shape by simp
      have rounds_le:
          "ceil_log (Suc (to_nat (staged_degree data))) \<le> N"
      proof -
        have d_suc_le: "Suc (to_nat (staged_degree data)) \<le> clength * scale"
          using degree_bound maxDegree_less_eval_domain by linarith
        show ?thesis
          by (rule ceil_log_le_power) (use d_suc_le eval_power in simp)
      qed
      have split:
          "(\<exists>j < length (map fst fl).
              map fst fl ! j \<in>
                fri_online_bad_challenges (to_nat (staged_degree data)) j
                  attacker_state (map snd fl ! j)) \<or>
           (\<exists>i < length (map fst fl).
              map fst fl ! i \<notin>
                fri_conditioned_bad_challenges (to_nat (staged_degree data))
                  (\<lambda>j _. fri_builder_conceptual_layers (map snd fl)
                    attacker_state final ! j)
                  i (take i (map fst fl)) \<and>
              \<not> fri_table_low_degree_on
                (fri_degree_after i
                  (fri_padded_degree_bound (to_nat (staged_degree data))))
                (fri_canonical_domain_at i)
                (fri_conditioned_layer_table i
                  (fri_builder_conceptual_layers (map snd fl)
                    attacker_state final ! i)) \<and>
              fri_table_low_degree_on
                (fri_degree_after (Suc i)
                  (fri_padded_degree_bound (to_nat (staged_degree data))))
                (fri_canonical_domain_at (Suc i))
                (fri_conditioned_layer_table (Suc i)
                  (fri_builder_conceptual_layers (map snd fl)
                    attacker_state final ! Suc i)) \<and>
              ?query_idxs \<in> fri_conditioned_residual_query_lists
                (map snd fl) (map fst fl)
                (fri_builder_conceptual_layers (map snd fl)
                  attacker_state final) i)"
        by (rule fri_builder_authenticated_chain_online_or_quantitative_residual[
          OF composition_chain eval_power round_count rounds_le
            attacker_final_ext attacker_clean no_builder_target
            composition_authenticated start_not_low])
      from split show ?thesis
      proof
        assume online:
            "\<exists>j < length (map fst fl).
              map fst fl ! j \<in>
                fri_online_bad_challenges (to_nat (staged_degree data)) j
                  attacker_state (map snd fl ! j)"
        have staged_online:
            "\<exists>j < length (staged_composition_fri_roots data).
              staged_composition_fri_challenges data ! j \<in>
                fri_online_bad_challenges (to_nat (staged_degree data)) j
                  attacker_state (staged_composition_fri_roots data ! j)"
          using online composition_challenges_eq composition_roots_eq
            composition_chain
          unfolding generic_fri_recorded_value_chain_evidence_def
          by simp
        have transition:
            "hash_state_relation_transition
              (conditioned_fri_relation_bounded
                (ro_checked_staged_transcript_hash_query_budget_for budgets)
                conditioned_composition_fri_bad_challenge_relation)
              (HashMap adversary_initial_state) (HashMap attacker_state)"
          by (rule
            checked_builder_composition_online_bad_imp_bounded_relation_transition[
              OF wf controlled builder_out attacker_clean no_initial
                degree_bound staged_online])
        then show ?thesis by simp
      next
        assume residual:
            "\<exists>i < length (map fst fl).
              map fst fl ! i \<notin>
                fri_conditioned_bad_challenges (to_nat (staged_degree data))
                  (\<lambda>j _. fri_builder_conceptual_layers (map snd fl)
                    attacker_state final ! j)
                  i (take i (map fst fl)) \<and>
              \<not> fri_table_low_degree_on
                (fri_degree_after i
                  (fri_padded_degree_bound (to_nat (staged_degree data))))
                (fri_canonical_domain_at i)
                (fri_conditioned_layer_table i
                  (fri_builder_conceptual_layers (map snd fl)
                    attacker_state final ! i)) \<and>
              fri_table_low_degree_on
                (fri_degree_after (Suc i)
                  (fri_padded_degree_bound (to_nat (staged_degree data))))
                (fri_canonical_domain_at (Suc i))
                (fri_conditioned_layer_table (Suc i)
                  (fri_builder_conceptual_layers (map snd fl)
                    attacker_state final ! Suc i)) \<and>
              ?query_idxs \<in> fri_conditioned_residual_query_lists
                (map snd fl) (map fst fl)
                (fri_builder_conceptual_layers (map snd fl)
                  attacker_state final) i"
        then obtain i where
          i_bound: "i < length (map fst fl)"
          and not_bad:
            "map fst fl ! i \<notin>
              fri_conditioned_bad_challenges (to_nat (staged_degree data))
                (\<lambda>j _. fri_builder_conceptual_layers (map snd fl)
                  attacker_state final ! j)
                i (take i (map fst fl))"
          and current_bad:
            "\<not> fri_table_low_degree_on
              (fri_degree_after i
                (fri_padded_degree_bound (to_nat (staged_degree data))))
              (fri_canonical_domain_at i)
              (fri_conditioned_layer_table i
                (fri_builder_conceptual_layers (map snd fl)
                  attacker_state final ! i))"
          and next_low:
            "fri_table_low_degree_on
              (fri_degree_after (Suc i)
                (fri_padded_degree_bound (to_nat (staged_degree data))))
              (fri_canonical_domain_at (Suc i))
              (fri_conditioned_layer_table (Suc i)
                (fri_builder_conceptual_layers (map snd fl)
                  attacker_state final ! Suc i))"
          and residual_query:
            "?query_idxs \<in> fri_conditioned_residual_query_lists
              (map snd fl) (map fst fl)
              (fri_builder_conceptual_layers (map snd fl)
                attacker_state final) i"
          by blast
        have raws_len: "length raws = rounds"
          using ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
            OF wf controlled builder_out] by blast
        have query_space: "?query_idxs \<in> fri_query_index_list_space"
          unfolding fri_query_index_list_space_def query_sample_space_def
          using raws_len index_less_query_sample_space by auto
        have quantitative:
            "?query_idxs \<in>
              fri_conditioned_quantitative_residual_query_lists_at
                (to_nat (staged_degree data)) (map snd fl) (map fst fl)
                final attacker_state i"
          unfolding fri_conditioned_quantitative_residual_query_lists_at_def
          using query_space not_bad current_bad next_low residual_query
          by blast
        have quantitative_at:
            "?query_idxs \<in>
              fri_conditioned_quantitative_residual_query_lists_at_value
                (to_nat (staged_degree data)) (map snd fl)
                (map fst fl ! i) final attacker_state i"
          using quantitative
          unfolding fri_conditioned_quantitative_residual_query_lists_at_value_eq[
            OF i_bound]
          .
        have final_map:
            "HashMap (channel_for_hash_map (HashMap attacker_state)) =
              HashMap attacker_state"
          unfolding channel_for_hash_map_def adversary_initial_state_def by simp
        have builder_layers_map:
            "fri_builder_conceptual_layers
                (staged_composition_fri_roots data)
                (channel_for_hash_map (HashMap attacker_state))
                (staged_composition_final data) =
              fri_builder_conceptual_layers (map snd fl)
                attacker_state final"
        proof -
          have table_map:
              "\<And>root len.
                conceptual_table
                    (channel_for_hash_map (HashMap attacker_state)) root len =
                  conceptual_table attacker_state root len"
            by (rule conceptual_table_cong_hash_map[OF final_map])
          show ?thesis
            unfolding fri_builder_conceptual_layers_def
            using composition_roots_eq composition_final_eq
            by (simp add: table_map)
        qed
        have quantitative_staged:
            "?query_idxs \<in>
              fri_conditioned_quantitative_residual_query_lists_at_value
                (to_nat (staged_degree data))
                (staged_composition_fri_roots data)
                (staged_composition_fri_challenges data ! i)
                (staged_composition_final data)
                (channel_for_hash_map (HashMap attacker_state)) i"
          using quantitative_at composition_roots_eq
            composition_challenges_eq builder_layers_map
          unfolding fri_conditioned_quantitative_residual_query_lists_at_value_def
            Let_def
          by simp
        have i_bound_staged:
            "i < length (staged_composition_fri_roots data)"
          using i_bound composition_roots_eq composition_challenges_eq
            composition_chain
          unfolding generic_fri_recorded_value_chain_evidence_def
          by simp
        have challenge_prefixes:
            "length (staged_composition_fri_challenges data) =
               length (staged_composition_fri_roots data) \<and>
             (\<forall>j < length (staged_composition_fri_roots data).
               \<exists>state.
                 ro_absorb_lookup_chain attacker_state
                   (PState adversary_initial_state)
                   (composition_fri_challenge_prefix_messages
                     (staged_trace_root data)
                     (staged_trace_fri_roots data)
                     (staged_trace_final data)
                     (staged_alphas data)
                     (staged_degree data)
                     (staged_composition_fri_roots data) j) state \<and>
                 fmlookup (HashMap attacker_state)
                   (CompositionFriChallenge j state) =
                   Some (staged_composition_fri_challenges data ! j))"
          using ro_checked_staged_transcript_program_conditioned_challenge_prefixes[
            OF wf controlled original_out] shape
          by simp
        have composition_challenge_evidence:
            "ro_conditioned_composition_challenge_evidence
              (HashMap attacker_state)
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              (staged_alphas data)
              (staged_degree data)
              (staged_composition_fri_roots data)
              (staged_composition_fri_challenges data)"
        proof -
          have at:
              "\<forall>j < length (staged_composition_fri_roots data).
                \<exists>state.
                  ro_absorb_lookup_chain
                    (channel_for_hash_map (HashMap attacker_state))
                    (PState adversary_initial_state)
                    (composition_fri_challenge_prefix_messages
                      (staged_trace_root data)
                      (staged_trace_fri_roots data)
                      (staged_trace_final data)
                      (staged_alphas data)
                      (staged_degree data)
                      (staged_composition_fri_roots data) j) state \<and>
                  fmlookup (HashMap attacker_state)
                    (CompositionFriChallenge j state) =
                    Some (staged_composition_fri_challenges data ! j)"
          proof (intro allI impI)
            fix j
            assume j_bound:
              "j < length (staged_composition_fri_roots data)"
            from challenge_prefixes j_bound obtain state where
              chain:
                "ro_absorb_lookup_chain attacker_state
                  (PState adversary_initial_state)
                  (composition_fri_challenge_prefix_messages
                    (staged_trace_root data)
                    (staged_trace_fri_roots data)
                    (staged_trace_final data)
                    (staged_alphas data)
                    (staged_degree data)
                    (staged_composition_fri_roots data) j) state"
              and lookup:
                "fmlookup (HashMap attacker_state)
                  (CompositionFriChallenge j state) =
                  Some (staged_composition_fri_challenges data ! j)"
              by blast
            have chain':
                "ro_absorb_lookup_chain
                  (channel_for_hash_map (HashMap attacker_state))
                  (PState adversary_initial_state)
                  (composition_fri_challenge_prefix_messages
                    (staged_trace_root data)
                    (staged_trace_fri_roots data)
                    (staged_trace_final data)
                    (staged_alphas data)
                    (staged_degree data)
                    (staged_composition_fri_roots data) j) state"
              by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
                (rule chain)
            show "\<exists>state.
                ro_absorb_lookup_chain
                  (channel_for_hash_map (HashMap attacker_state))
                  (PState adversary_initial_state)
                  (composition_fri_challenge_prefix_messages
                    (staged_trace_root data)
                    (staged_trace_fri_roots data)
                    (staged_trace_final data)
                    (staged_alphas data)
                    (staged_degree data)
                    (staged_composition_fri_roots data) j) state \<and>
                fmlookup (HashMap attacker_state)
                  (CompositionFriChallenge j state) =
                  Some (staged_composition_fri_challenges data ! j)"
              using chain' lookup by blast
          qed
          show ?thesis
            unfolding ro_conditioned_composition_challenge_evidence_def
            using challenge_prefixes at by blast
        qed
        have combined:
            "?query_idxs \<in>
              ro_conditioned_combined_residual_query_lists
                (HashMap attacker_state)
                (staged_trace_root data)
                (staged_trace_fri_roots data)
                (staged_trace_final data)
                (staged_alphas data)
                (staged_degree data)
                (staged_composition_fri_roots data)
                (staged_composition_final data)"
          by (rule fri_conditioned_composition_quantitative_residual_imp_combined[
            OF composition_challenge_evidence degree_bound i_bound_staged
              quantitative_staged])
        have transition:
            "hash_state_relation_transition
              (conditioned_fri_relation_bounded
                (ro_checked_staged_transcript_hash_query_budget_for budgets)
                ro_conditioned_augmented_absorbed_query_relation)
              (HashMap adversary_initial_state) (HashMap attacker_state)"
          by (rule
            checked_builder_conditioned_residual_imp_bounded_relation_transition[
              OF wf controlled nonempty builder_out attacker_clean no_initial
                degree_bound combined])
        then show ?thesis by simp
      qed    qed
  qed
qed

end
end
