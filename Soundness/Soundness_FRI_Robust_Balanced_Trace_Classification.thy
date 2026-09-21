theory Soundness_FRI_Robust_Balanced_Trace_Classification
  imports
    Stark.Soundness_FRI_Robust_Trace_Classification
    Stark.Soundness_FRI_Robust_Balanced_Actual_Query
    Stark.Soundness_FRI_Robust_Balanced_Challenge_Relation
    Stark.Soundness_FRI_Robust_Balanced_Query_Phase_Transport
begin

context soundness
begin

lemma checked_builder_trace_not_robust_close_imp_residual_or_targets_balanced_exact_two:
  fixes final_state :: "'f protocol_channel"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and trace_rounds_fit: "Suc (ceil_log clength) \<le> N"
    and trace_exact:
      "fri_balanced_exact_list_cap
        (clength - 1) (ceil_log clength) C 2"
    and builder_out:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and verifier_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and final_clean: "\<not> hash_map_output_collision final_state"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values attacker_state"
    and candidate_far:
      "\<not> fri_rs_distance_to_code
        (fri_padded_degree_bound (clength - 1)) eval_domain
        (nth (first_trace_fri_root_prefix_first_table
          prefix prefix_state))
        \<le> fri_balanced_radius (ceil_log clength) C 0"
  shows
    "hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state \<or>
      fri_checked_builder_merkle_target_hit data attacker_state final_state \<or>
      hash_state_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          (balanced_conditioned_trace_fri_bad_challenge_relation C))
        (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
      hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data query_start)
        query_start attacker_state \<or>
      ro_query_head_dependent_actual_query_index_list_hit
        (fri_balanced_combined_query_head_lists C)
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
proof -
  from
    ro_absorb_checked_staged_first_root_actual_query_accepted_evidence[
      OF wf controlled nonempty builder_out verifier_out final_clean]
  obtain f_fl fl fr f_final as final trace_round_layers
      composition_round_layers where
    fr_eq: "fr = staged_trace_root data"
    and trace_challenges_eq:
      "map fst f_fl = staged_trace_fri_challenges data"
    and trace_roots_eq:
      "map snd f_fl = staged_trace_fri_roots data"
    and trace_final_eq: "f_final = staged_trace_final data"
    and alphas_eq: "as = staged_alphas data"
    and composition_challenges_eq:
      "map fst fl = staged_composition_fri_challenges data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and composition_final_eq:
      "final = staged_composition_final data"
    and f_fl_nonempty: "f_fl \<noteq> []"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and trace_layers_len:
      "length trace_round_layers = length raws"
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
  have query_idxs_len: "length ?query_idxs = length raws"
    by simp
  have layer_transcripts':
      "\<forall>j < length ?query_idxs.
        query_round_fri_layer_transcripts (?query_idxs ! j)
          (map snd f_fl) (map snd fl)
          (staged_query_chunks data ! j)
          (trace_round_layers ! j) (composition_round_layers ! j)"
    using layer_transcripts trace_roots_eq composition_roots_eq by simp
  have trace_all_layers:
      "fri_all_round_layer_evidence
        (map snd f_fl) (map fst f_fl) ?query_idxs trace_round_layers"
    by (rule
      query_round_fri_layer_transcripts_trace_all_round_layer_evidence[
        OF _ _ layer_transcripts'])
      (use trace_layers_len query_idxs_len in simp_all)
  have composition_all_layers:
      "fri_all_round_layer_evidence
        (map snd fl) (map fst fl) ?query_idxs composition_round_layers"
    by (rule
      query_round_fri_layer_transcripts_composition_all_round_layer_evidence[
        OF _ _ layer_transcripts'])
      (use composition_layers_len query_idxs_len in simp_all)
  have original_out0:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome[
        OF nonempty builder_out])
  have evidence_shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (to_nat (staged_degree data) + 1)"
    using ro_checked_staged_transcript_program_outcome_shape[OF original_out0]
    by blast
  have trace_count:
      "length (map snd f_fl) =
        fri_round_count_for_degree_bound (clength - 1)"
    using trace_roots_eq evidence_shape trace_fri_algebraic_round_count_eq
    unfolding trace_fri_algebraic_round_count_def
    by simp
  have composition_count:
      "length (map snd fl) =
        fri_round_count_for_degree_bound (to_nat (staged_degree data))"
    using composition_roots_eq evidence_shape
    unfolding fri_round_count_for_degree_bound_def
    by simp
  have trace_partial:
      "generic_fri_partial_evidence trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (clength - 1) (map snd f_fl) (map fst f_fl) f_final
        ?query_idxs trace_round_layers"
    unfolding generic_fri_partial_evidence_def
    using trace_count trace_all_layers by simp
  have composition_partial:
      "generic_fri_partial_evidence
        (composition_table_low_degree (to_nat (staged_degree data))) []
        (to_nat (staged_degree data)) (map snd fl) (map fst fl) final
        ?query_idxs composition_round_layers"
    unfolding generic_fri_partial_evidence_def
    using composition_count composition_all_layers by simp
  have chains:

      "generic_fri_recorded_value_chain_evidence
         (map snd f_fl) (map fst f_fl) f_final
         ?query_idxs trace_round_layers \<and>
       generic_fri_recorded_value_chain_evidence
         (map snd fl) (map fst fl) final
         ?query_idxs composition_round_layers"
    by (rule ro_recorded_query_fri_accepted_evidence_all_value_chains[
      OF trace_layers_len composition_layers_len accepted])
  have trace_chain:
      "generic_fri_recorded_value_chain_evidence
        (map snd f_fl) (map fst f_fl) f_final
        ?query_idxs trace_round_layers"
    using chains by blast
  have composition_chain:
      "generic_fri_recorded_value_chain_evidence
        (map snd fl) (map fst fl) final
        ?query_idxs composition_round_layers"
    using chains by blast
  have authenticated:
      "generic_fri_recorded_chunks_authenticated
         (map snd f_fl) ?query_idxs trace_round_layers final_state \<and>
       generic_fri_recorded_chunks_authenticated
         (map snd fl) ?query_idxs composition_round_layers final_state"
    by (rule ro_recorded_query_fri_accepted_evidence_all_chunks_authenticated[
      OF trace_layers_len composition_layers_len accepted])
  have trace_authenticated:
      "generic_fri_recorded_chunks_authenticated
        (map snd f_fl) ?query_idxs trace_round_layers final_state"
    using authenticated by blast
  have composition_authenticated:
      "generic_fri_recorded_chunks_authenticated
        (map snd fl) ?query_idxs composition_round_layers final_state"
    using authenticated by blast
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome[
        OF nonempty builder_out])
  have attacker_verifier_ext:
      "attacker_state \<le>
        verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
    by (rule hash_extends_verifier_state_from_adversary_right)
      (rule hash_ext_refl)
  have verifier_final_ext:
      "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data) \<le> final_state"
    using ro_checked_staged_transcript_program_ro_verify_monad_sync[
      OF wf controlled original_out verifier_out]
    by blast
  have attacker_final_ext: "attacker_state \<le> final_state"
    by (rule hash_ext_trans[OF attacker_verifier_ext verifier_final_ext])
  have attacker_clean: "\<not> hash_map_output_collision attacker_state"
  proof
    assume collision: "hash_map_output_collision attacker_state"
    have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[OF collision attacker_final_ext])
    then show False using final_clean by contradiction
  qed

  have prefix_attacker_ext: "prefix_state \<le> attacker_state"
    using
      ro_checked_staged_transcript_program_with_first_root_good_fields[
        OF wf controlled nonempty builder_out]
    by blast
  have prefix_final_ext: "prefix_state \<le> final_state"
    by (rule hash_ext_trans[OF prefix_attacker_ext attacker_final_ext])
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_final_ext])
    then show False using final_clean by contradiction
  qed

  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength \<and>
       length (staged_alphas data) = length spec \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       length (staged_composition_fri_challenges data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       ceil_log (to_nat (staged_degree data) + 1) \<le>
         ceil_log (maxDegree + 1) \<and>
       length (staged_query_chunks data) = rounds"
    by (rule ro_checked_staged_transcript_program_outcome_shape[OF original_out])
  have roots_nonempty: "map snd f_fl \<noteq> []"
    using f_fl_nonempty by simp
  have challenge_len:
      "length (map fst f_fl) = ceil_log clength"
    using trace_chain trace_roots_eq shape
    unfolding generic_fri_recorded_value_chain_evidence_def
    by simp
  have prefix_eq:
      "prefix =
        (staged_trace_root data, [], hd (staged_trace_fri_roots data))"
  proof -
    have zero_bound: "0 < rounds"
      by (rule rounds_positive)
    from
      ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain[
        OF wf controlled nonempty builder_out attacker_clean zero_bound]
    show ?thesis by blast
  qed
  have data_roots_nonempty: "staged_trace_fri_roots data \<noteq> []"
    using trace_roots_eq roots_nonempty by simp
  have root0:
      "map snd f_fl ! 0 = hd (staged_trace_fri_roots data)"
  proof (cases "staged_trace_fri_roots data")
    case Nil
    then show ?thesis using data_roots_nonempty by simp
  next
    case (Cons a xs)
    then show ?thesis using trace_roots_eq by simp
  qed  have first_table_eq:
      "first_trace_fri_root_prefix_first_table prefix prefix_state =
        conceptual_table prefix_state (map snd f_fl ! 0)
          (length (fri_canonical_domain_at 0))"
    unfolding prefix_eq first_trace_fri_root_prefix_first_table_def
      fri_canonical_domain_at_length
    using root0 by (simp add: mult.commute)

  have query_idxs_space:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in> fri_query_index_list_space"
  proof -
    have raws_len: "length raws = rounds"
      using
        ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
          OF wf controlled builder_out]
      by blast
    show ?thesis
      unfolding fri_query_index_list_space_def query_sample_space_def
      using raws_len index_less_query_sample_space by auto
  qed

  show ?thesis
  proof (cases
      "hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state")
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
            (merkle_prefix_path_targets {map snd f_fl ! 0} prefix_state)
            prefix_state final_state"
      proof

        assume hit:
            "hash_map_new_output_hit
              (merkle_prefix_path_targets {map snd f_fl ! 0} prefix_state)
              prefix_state final_state"
        have roots_set_subset:
            "{map snd f_fl ! 0} \<subseteq>
              {staged_trace_root data, hd (staged_trace_fri_roots data)}"
          using root0 by auto
        have target_subset:
            "merkle_prefix_path_targets {map snd f_fl ! 0} prefix_state \<subseteq>
              first_trace_fri_root_prefix_merkle_targets prefix prefix_state"
          unfolding prefix_eq
            first_trace_fri_root_prefix_merkle_targets_def
          using prefix_clean
          by (simp add: merkle_prefix_path_targets_mono[OF roots_set_subset])
        have            "hash_map_new_output_hit
              (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
              prefix_state final_state"
          by (rule hash_map_new_output_hit_subset[OF target_subset hit])
        then show False using no_prefix by contradiction
      qed
      have no_builder_trace_target:
          "\<not> hash_map_new_output_hit
            (merkle_prefix_path_targets (set (map snd f_fl)) attacker_state)
            attacker_state final_state"
      proof
        assume hit:
            "hash_map_new_output_hit
              (merkle_prefix_path_targets (set (map snd f_fl)) attacker_state)
              attacker_state final_state"
        have roots_subset:
            "set (map snd f_fl) \<subseteq>
              set (staged_trace_fri_roots data) \<union>
                set (staged_composition_fri_roots data)"
          using trace_roots_eq by auto
        have target_subset:
            "merkle_prefix_path_targets (set (map snd f_fl)) attacker_state \<subseteq>
              fri_checked_builder_merkle_targets data attacker_state"
          unfolding fri_checked_builder_merkle_targets_def
          by (rule merkle_prefix_path_targets_mono[OF roots_subset])
        have
            "hash_map_new_output_hit
              (fri_checked_builder_merkle_targets data attacker_state)
              attacker_state final_state"
          by (rule hash_map_new_output_hit_subset[OF target_subset hit])
        then show False
          using no_builder
          unfolding fri_checked_builder_merkle_target_hit_def
          by contradiction
      qed
      have prefix_stable:
          "conceptual_table final_state (map snd f_fl ! 0)
              (length (fri_canonical_domain_at 0)) =
            conceptual_table prefix_state (map snd f_fl ! 0)
              (length (fri_canonical_domain_at 0))"
        by (rule conceptual_table_prefix_stable_if_no_target[
          OF prefix_final_ext no_prefix_singleton])
      have no_builder_singleton:
          "\<not> hash_map_new_output_hit
            (merkle_prefix_path_targets {map snd f_fl ! 0} attacker_state)
            attacker_state final_state"
      proof
        assume hit:
            "hash_map_new_output_hit
              (merkle_prefix_path_targets {map snd f_fl ! 0} attacker_state)
              attacker_state final_state"
        have root_mem: "map snd f_fl ! 0 \<in> set (map snd f_fl)"
          using roots_nonempty by simp
        have target_subset:
            "merkle_prefix_path_targets {map snd f_fl ! 0} attacker_state \<subseteq>
              merkle_prefix_path_targets (set (map snd f_fl)) attacker_state"
          by (rule merkle_prefix_path_targets_mono)
            (use root_mem in auto)
        have
            "hash_map_new_output_hit
              (merkle_prefix_path_targets (set (map snd f_fl)) attacker_state)
              attacker_state final_state"
          by (rule hash_map_new_output_hit_subset[OF target_subset hit])
        then show False using no_builder_trace_target by contradiction
      qed
      have attacker_stable:
          "conceptual_table final_state (map snd f_fl ! 0)
              (length (fri_canonical_domain_at 0)) =
            conceptual_table attacker_state (map snd f_fl ! 0)
              (length (fri_canonical_domain_at 0))"
        by (rule conceptual_table_prefix_stable_if_no_target[
          OF attacker_final_ext no_builder_singleton])
      have first_table_attacker:
          "first_trace_fri_root_prefix_first_table prefix prefix_state =
            conceptual_table attacker_state (map snd f_fl ! 0)
              (length (fri_canonical_domain_at 0))"
        using first_table_eq prefix_stable attacker_stable by simp
      have layer0_eq:
          "fri_builder_conceptual_layers (map snd f_fl) attacker_state f_final ! 0 =
            first_trace_fri_root_prefix_first_table prefix prefix_state"
        using fri_builder_conceptual_layers_at[
            of 0 "map snd f_fl" attacker_state f_final]
          roots_nonempty first_table_attacker
        by simp
      have candidate_len:
          "length
            (first_trace_fri_root_prefix_first_table prefix prefix_state) =
              clength * scale"
        unfolding prefix_eq first_trace_fri_root_prefix_first_table_def
          conceptual_table_def
        by (simp add: mult.commute)
      have conditioned_layer0:
          "fri_conditioned_layer_table 0
              (fri_builder_conceptual_layers (map snd f_fl) attacker_state
                f_final ! 0) =
            first_trace_fri_root_prefix_first_table prefix prefix_state"
        using layer0_eq candidate_len
        unfolding fri_conditioned_layer_table_def
          fri_canonical_domain_at_length
        by simp


      have robust_layer0:
          "fri_robust_conditioned_layers (length (map fst f_fl))
              (fri_builder_conceptual_layers (map snd f_fl)
                attacker_state f_final) ! 0 =
            first_trace_fri_root_prefix_first_table prefix prefix_state"
proof -
          have at:
              "fri_robust_conditioned_layers (length (map fst f_fl))
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final) ! 0 =
                fri_conditioned_layer_table 0
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final ! 0)"
            by (rule fri_robust_conditioned_layers_nth) simp
          show ?thesis
            using at conditioned_layer0 by simp
        qed      have initial_not_close:
          "\<not> fri_canonical_layer_close (clength - 1)
            (fri_robust_conditioned_layers (length (map fst f_fl))
              (fri_builder_conceptual_layers (map snd f_fl)
                attacker_state f_final))
            (fri_balanced_radius (length (map fst f_fl)) C) 0"
        using candidate_far robust_layer0 challenge_len
        unfolding fri_canonical_layer_close_def
          fri_canonical_domain_at_0
        by simp
      have round_count:
          "length (map fst f_fl) = ceil_log (Suc (clength - 1))"
        using challenge_len clength_pos by simp
      have rounds_fit:
          "Suc (length (map fst f_fl)) \<le> N"
        using challenge_len trace_rounds_fit by simp
      have exact:
          "fri_balanced_exact_list_cap
            (clength - 1) (length (map fst f_fl)) C 2"
        using challenge_len trace_exact by simp
      have split_full:
          "fri_canonical_layer_close (clength - 1)
              (fri_robust_conditioned_layers (length (map fst f_fl))
                (fri_builder_conceptual_layers (map snd f_fl)
                  attacker_state f_final))
              (fri_balanced_radius (length (map fst f_fl)) C) 0 \<or>
            (\<exists>j < length (map fst f_fl).

              map fst f_fl ! j \<in>
                fri_online_balanced_bad_challenges
                  (clength - 1) (length (map fst f_fl)) C j
                  attacker_state (map snd f_fl ! j)) \<or>
            (\<exists>i < length (map fst f_fl).
              \<not> fri_canonical_layer_close (clength - 1)
                (fri_robust_conditioned_layers (length (map fst f_fl))
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final))
                (fri_balanced_radius (length (map fst f_fl)) C) i \<and>
              fri_canonical_layer_close (clength - 1)
                (fri_robust_conditioned_layers (length (map fst f_fl))
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final))
                (fri_balanced_radius (length (map fst f_fl)) C) (Suc i) \<and>
              ?query_idxs \<in>
                fri_robust_conditioned_residual_query_lists
                  (map snd f_fl) (map fst f_fl)
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final) i \<and>
              card (fri_robust_conditioned_agreement_indices
                (map fst f_fl)
                (fri_builder_conceptual_layers (map snd f_fl)
                  attacker_state f_final) i)
                \<le> length (fri_canonical_domain_at (Suc i)) -
                  fri_balanced_margin C i)"
        by (rule
          fri_builder_authenticated_chain_robust_online_or_residual_balanced_exact_two[
            OF trace_chain eval_power round_count rounds_fit exact
              attacker_final_ext attacker_clean no_builder_trace_target
              trace_authenticated])
      have split:
          "(\<exists>j < length (map fst f_fl).
              map fst f_fl ! j \<in>
                fri_online_balanced_bad_challenges
                  (clength - 1) (length (map fst f_fl)) C j
                  attacker_state (map snd f_fl ! j)) \<or>
            (\<exists>i < length (map fst f_fl).
              \<not> fri_canonical_layer_close (clength - 1)
                (fri_robust_conditioned_layers (length (map fst f_fl))
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final))
                (fri_balanced_radius (length (map fst f_fl)) C) i \<and>
              fri_canonical_layer_close (clength - 1)
                (fri_robust_conditioned_layers (length (map fst f_fl))
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final))
                (fri_balanced_radius (length (map fst f_fl)) C) (Suc i) \<and>
              ?query_idxs \<in>
                fri_robust_conditioned_residual_query_lists
                  (map snd f_fl) (map fst f_fl)
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final) i \<and>
              card (fri_robust_conditioned_agreement_indices
                (map fst f_fl)
                (fri_builder_conceptual_layers (map snd f_fl)
                  attacker_state f_final) i)
                \<le> length (fri_canonical_domain_at (Suc i)) -
                  fri_balanced_margin C i)"
        using split_full initial_not_close by blast
      from split show ?thesis
      proof
        assume online:
            "\<exists>j < length (map fst f_fl).
              map fst f_fl ! j \<in>
                fri_online_balanced_bad_challenges
                  (clength - 1) (length (map fst f_fl)) C j
                  attacker_state (map snd f_fl ! j)"
        have staged_online:
            "\<exists>j < length (staged_trace_fri_roots data).
              staged_trace_fri_challenges data ! j \<in>
                fri_online_balanced_bad_challenges
                  (clength - 1)
                  (length (staged_trace_fri_roots data)) C j
                  attacker_state (staged_trace_fri_roots data ! j)"
          using online trace_challenges_eq trace_roots_eq trace_chain
          unfolding generic_fri_recorded_value_chain_evidence_def
          by simp
        have transition:
            "hash_state_relation_transition
              (conditioned_fri_relation_bounded
                (ro_checked_staged_transcript_hash_query_budget_for budgets)
                (balanced_conditioned_trace_fri_bad_challenge_relation C))
              (HashMap adversary_initial_state) (HashMap attacker_state)"
          by (rule
            checked_builder_trace_balanced_online_bad_imp_bounded_relation_transition[
              OF wf controlled builder_out attacker_clean no_initial
                staged_online])
        then show ?thesis by simp
      next
        assume residual:
            "\<exists>i < length (map fst f_fl).
              \<not> fri_canonical_layer_close (clength - 1)
                (fri_robust_conditioned_layers (length (map fst f_fl))
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final))
                (fri_balanced_radius (length (map fst f_fl)) C) i \<and>
              fri_canonical_layer_close (clength - 1)
                (fri_robust_conditioned_layers (length (map fst f_fl))
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final))
                (fri_balanced_radius (length (map fst f_fl)) C) (Suc i) \<and>
              ?query_idxs \<in>
                fri_robust_conditioned_residual_query_lists
                  (map snd f_fl) (map fst f_fl)
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final) i \<and>
              card (fri_robust_conditioned_agreement_indices
                (map fst f_fl)
                (fri_builder_conceptual_layers (map snd f_fl)
                  attacker_state f_final) i)
                \<le> length (fri_canonical_domain_at (Suc i)) -
                  fri_balanced_margin C i"
        have quantitative:
            "?query_idxs \<in>
              fri_balanced_quantitative_residual_query_lists
                (clength - 1) C (map snd f_fl) (map fst f_fl)
                f_final attacker_state"
          unfolding fri_balanced_quantitative_residual_query_lists_def
            fri_balanced_residual_active_layers_def
          using query_idxs_space residual by blast
        have trace_head:
            "?query_idxs \<in>
              fri_balanced_trace_query_head_lists C
                prefix prefix_state data attacker_state"
          using quantitative trace_roots_eq trace_challenges_eq trace_final_eq
          unfolding fri_balanced_trace_query_head_lists_def
            fri_balanced_trace_residual_query_lists_def
          by simp
        have combined_head:
            "?query_idxs \<in>
              fri_balanced_combined_query_head_lists C
                prefix prefix_state data attacker_state"
          using trace_head
          unfolding fri_balanced_combined_query_head_lists_def by blast
        have actual_or_target:
            "hash_map_new_output_hit
                (fri_checked_builder_merkle_targets data query_start)
                query_start attacker_state \<or>
              ro_query_head_dependent_actual_query_index_list_hit
                (fri_balanced_combined_query_head_lists C)
                (Some ((((prefix, prefix_state), data, query_start, raws,
                  query_states), attacker_state)))"
          by (rule
            checked_builder_balanced_residual_imp_actual_or_query_phase_target[
              OF wf controlled builder_out combined_head])
        then show ?thesis by blast
      qed
    qed
  qed
qed

end
end
