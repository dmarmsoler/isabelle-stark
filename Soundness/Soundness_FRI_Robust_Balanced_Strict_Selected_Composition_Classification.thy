theory Soundness_FRI_Robust_Balanced_Strict_Selected_Composition_Classification
  imports
    Stark.Soundness_FRI_Robust_Composition_Classification
    Stark.Soundness_FRI_Robust_Balanced_Strict_Selected_Actual_Query
    Stark.Soundness_FRI_Robust_Balanced_Challenge_Relation
    Stark.Soundness_FRI_Robust_Balanced_Strict_Selected_Query_Phase_Transport
begin

context soundness
begin

lemma checked_builder_composition_not_robust_close_imp_strict_selected_residual_or_targets_balanced_exact_two:
  fixes final_state :: "'f protocol_channel"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and eval_power: "clength * scale = 2 ^ N"
    and composition_rounds_fit:
      "Suc (ceil_log (Suc maxDegree)) \<le> N"
    and composition_exact:
      "\<And>d. d \<le> maxDegree \<Longrightarrow>
        fri_balanced_exact_list_cap d (ceil_log (Suc d)) C 2"
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
    and candidate_far:
      "\<not> fri_rs_distance_to_code
        (fri_padded_degree_bound (to_nat (staged_degree data))) eval_domain
        (nth (ro_actual_query_composition_candidate data query_start))
        \<le> fri_balanced_radius
          (ceil_log (Suc (to_nat (staged_degree data)))) C 0"
  shows
    "hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets data query_start)
        query_start final_state \<or>
     fri_checked_builder_merkle_target_hit data attacker_state final_state \<or>
     hash_state_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          (balanced_conditioned_composition_fri_bad_challenge_relation C))
        (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
     hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data query_start)
        query_start attacker_state \<or>
     ro_query_head_dependent_actual_query_index_list_hit
        (fri_balanced_strict_selected_combined_query_head_lists C)
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
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
    have table_low:
        "fri_table_low_degree_on
          (fri_padded_degree_bound (to_nat (staged_degree data)))
          eval_domain
          (ro_actual_query_composition_candidate data query_start)"
      using low
      unfolding
        composition_table_low_degree_iff_fri_table_low_degree_on_eval_domain .
    have distance_zero:
        "fri_rs_distance_to_code
          (fri_padded_degree_bound (to_nat (staged_degree data)))
          eval_domain
          (nth (ro_actual_query_composition_candidate data query_start)) = 0"
      by (rule fri_table_low_degree_distance_zero[OF table_low])
    show False
      using candidate_far distance_zero by simp
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


      have robust_layer0:
          "fri_robust_conditioned_layers (length (map fst fl))
              (fri_builder_conceptual_layers (map snd fl)
                attacker_state final) ! 0 =
            ro_actual_query_composition_candidate data query_start"
      proof -
        have at:
            "fri_robust_conditioned_layers (length (map fst fl))
                (fri_builder_conceptual_layers (map snd fl)
                  attacker_state final) ! 0 =
              fri_conditioned_layer_table 0
                (fri_builder_conceptual_layers (map snd fl)
                  attacker_state final ! 0)"
          by (rule fri_robust_conditioned_layers_nth) simp
        show ?thesis
          using at conditioned_layer0 by simp
      qed
      have round_count:
          "length (map fst fl) =
            ceil_log (Suc (to_nat (staged_degree data)))"
        using composition_challenges_eq shape by simp
      have initial_not_close:
          "\<not> fri_canonical_layer_close
            (to_nat (staged_degree data))
            (fri_robust_conditioned_layers (length (map fst fl))
              (fri_builder_conceptual_layers (map snd fl)
                attacker_state final))
            (fri_balanced_radius (length (map fst fl)) C) 0"
        using candidate_far robust_layer0 round_count
        unfolding fri_canonical_layer_close_def
          fri_canonical_domain_at_0
        by simp
      have log_mono:
          "ceil_log (Suc (to_nat (staged_degree data))) \<le>
            ceil_log (Suc maxDegree)"
        by (rule ceil_log_mono) (use degree_bound in simp)
      have rounds_fit:
          "Suc (length (map fst fl)) \<le> N"
        using round_count log_mono composition_rounds_fit by linarith
      have exact:
          "fri_balanced_exact_list_cap
            (to_nat (staged_degree data))
            (length (map fst fl)) C 2"
      proof -
        have at_log:
            "fri_balanced_exact_list_cap
              (to_nat (staged_degree data))
              (ceil_log (Suc (to_nat (staged_degree data)))) C 2"
          by (rule composition_exact[OF degree_bound])
        show ?thesis
          using at_log round_count by simp
      qed
      have raws_len: "length raws = rounds"
        using ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
          OF wf controlled builder_out] by blast
      have query_space: "?query_idxs \<in> fri_query_index_list_space"
        unfolding fri_query_index_list_space_def query_sample_space_def
        using raws_len index_less_query_sample_space by auto
      have split_full:
          "fri_canonical_layer_close (to_nat (staged_degree data))
              (fri_robust_conditioned_layers (length (map fst fl))
                (fri_builder_conceptual_layers (map snd fl)
                  attacker_state final))
              (fri_balanced_radius (length (map fst fl)) C) 0 \<or>
            (\<exists>j < length (map fst fl).
              map fst fl ! j \<in>
                fri_online_balanced_bad_challenges
                  (to_nat (staged_degree data)) (length (map fst fl)) C j
                  attacker_state (map snd fl ! j)) \<or>
            ?query_idxs \<in> fri_balanced_strict_selected_residual_query_lists
              (to_nat (staged_degree data)) C
              (map snd fl) (map fst fl) final attacker_state"
        by (rule
          fri_builder_authenticated_chain_robust_online_or_strict_selected_residual_balanced_exact_two[
            OF composition_chain eval_power round_count rounds_fit exact
              attacker_final_ext attacker_clean no_builder_target
              composition_authenticated query_space])
      have split:
          "(\<exists>j < length (map fst fl).
              map fst fl ! j \<in>
                fri_online_balanced_bad_challenges
                  (to_nat (staged_degree data)) (length (map fst fl)) C j
                  attacker_state (map snd fl ! j)) \<or>
            ?query_idxs \<in> fri_balanced_strict_selected_residual_query_lists
              (to_nat (staged_degree data)) C
              (map snd fl) (map fst fl) final attacker_state"
        using split_full initial_not_close by blast
      from split show ?thesis
      proof
        assume online:
            "\<exists>j < length (map fst fl).
              map fst fl ! j \<in>
                fri_online_balanced_bad_challenges
                  (to_nat (staged_degree data)) (length (map fst fl)) C j
                  attacker_state (map snd fl ! j)"
        have staged_online:
            "\<exists>j < length (staged_composition_fri_roots data).
              staged_composition_fri_challenges data ! j \<in>
                fri_online_balanced_bad_challenges
                  (to_nat (staged_degree data))
                  (length (staged_composition_fri_roots data)) C j
                  attacker_state
                  (staged_composition_fri_roots data ! j)"
          using online composition_challenges_eq composition_roots_eq
            composition_chain
          unfolding generic_fri_recorded_value_chain_evidence_def
          by simp
        have transition:
            "hash_state_relation_transition
              (conditioned_fri_relation_bounded
                (ro_checked_staged_transcript_hash_query_budget_for budgets)
                (balanced_conditioned_composition_fri_bad_challenge_relation C))
              (HashMap adversary_initial_state) (HashMap attacker_state)"
          by (rule
            checked_builder_composition_balanced_online_bad_imp_bounded_relation_transition[
              OF wf controlled builder_out attacker_clean no_initial
                degree_bound staged_online])
        then show ?thesis by simp
      next
        assume residual:
            "?query_idxs \<in> fri_balanced_strict_selected_residual_query_lists
              (to_nat (staged_degree data)) C
              (map snd fl) (map fst fl) final attacker_state"
        have composition_head:
            "?query_idxs \<in>
              fri_balanced_strict_selected_composition_query_head_lists C
                prefix prefix_state data attacker_state"
          using degree_bound residual composition_roots_eq
            composition_challenges_eq composition_final_eq
          unfolding fri_balanced_strict_selected_composition_query_head_lists_def
            fri_balanced_strict_selected_composition_residual_query_lists_def
          by simp
        have combined_head:
            "?query_idxs \<in>
              fri_balanced_strict_selected_combined_query_head_lists C
                prefix prefix_state data attacker_state"
          using composition_head
          unfolding fri_balanced_strict_selected_combined_query_head_lists_def by blast
        have actual_or_target:
            "hash_map_new_output_hit
                (fri_checked_builder_merkle_targets data query_start)
                query_start attacker_state \<or>
              ro_query_head_dependent_actual_query_index_list_hit
                (fri_balanced_strict_selected_combined_query_head_lists C)
                (Some ((((prefix, prefix_state), data, query_start, raws,
                  query_states), attacker_state)))"
          by (rule
            checked_builder_balanced_strict_selected_residual_imp_actual_or_query_phase_target[
              OF wf controlled builder_out combined_head])
        then show ?thesis by blast
      qed
    qed
  qed
qed

end
end
