theory Soundness_FRI_Conditioned_Explicit_Residual_Complete_List_Classification
  imports Soundness_FRI_Conditioned_Explicit_Security_Target
begin

context soundness
begin

lemma fri_builder_conceptual_layers_stable_if_no_target:
  assumes ext: "s \<le> t"
    and no_target:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets (set roots) s) s t"
  shows
    "fri_builder_conceptual_layers roots t final_value =
      fri_builder_conceptual_layers roots s final_value"
proof -
  have table_eq:
      "\<And>j. j < length roots \<Longrightarrow>
        conceptual_table t (roots ! j)
            (length (fri_canonical_domain_at j)) =
          conceptual_table s (roots ! j)
            (length (fri_canonical_domain_at j))"
  proof -
    fix j
    assume j_bound: "j < length roots"
    have root_mem: "roots ! j \<in> set roots"
      by (rule nth_mem[OF j_bound])
    have singleton_subset:
        "merkle_prefix_path_targets {roots ! j} s \<subseteq>
          merkle_prefix_path_targets (set roots) s"
      by (rule merkle_prefix_path_targets_mono) (use root_mem in auto)
    have no_singleton:
        "\<not> hash_map_new_output_hit
          (merkle_prefix_path_targets {roots ! j} s) s t"
      using no_target
        hash_map_new_output_hit_subset[OF singleton_subset]
      by blast
    show
      "conceptual_table t (roots ! j)
          (length (fri_canonical_domain_at j)) =
        conceptual_table s (roots ! j)
          (length (fri_canonical_domain_at j))"
      by (rule conceptual_table_prefix_stable_if_no_target[
          OF ext no_singleton])
  qed
  show ?thesis
    unfolding fri_builder_conceptual_layers_def
    by (simp add: table_eq)
qed



lemma fri_conditioned_trace_residual_query_lists_stable_if_no_builder_target:
  assumes ext: "s \<le> t"
    and no_target:
      "\<not> hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data s) s t"
  shows
    "fri_conditioned_trace_residual_query_lists data t =
      fri_conditioned_trace_residual_query_lists data s"
proof -
  have targets_subset:
      "merkle_prefix_path_targets (set (staged_trace_fri_roots data)) s \<subseteq>
        fri_checked_builder_merkle_targets data s"
    unfolding fri_checked_builder_merkle_targets_def
    by (rule merkle_prefix_path_targets_mono) auto
  have no_trace:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets (set (staged_trace_fri_roots data)) s)
        s t"
    using no_target hash_map_new_output_hit_subset[OF targets_subset]
    by blast
  have layers:
      "fri_builder_conceptual_layers (staged_trace_fri_roots data) t
          (staged_trace_final data) =
        fri_builder_conceptual_layers (staged_trace_fri_roots data) s
          (staged_trace_final data)"
    by (rule fri_builder_conceptual_layers_stable_if_no_target[
        OF ext no_trace])
  show ?thesis
    unfolding fri_conditioned_trace_residual_query_lists_def
      fri_conditioned_quantitative_residual_query_lists_def
    by (simp add: layers)
qed

lemma fri_conditioned_composition_residual_query_lists_stable_if_no_builder_target:
  assumes ext: "s \<le> t"
    and no_target:
      "\<not> hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data s) s t"
  shows
    "fri_conditioned_composition_residual_query_lists data t =
      fri_conditioned_composition_residual_query_lists data s"
proof -
  have targets_subset:
      "merkle_prefix_path_targets
          (set (staged_composition_fri_roots data)) s \<subseteq>
        fri_checked_builder_merkle_targets data s"
    unfolding fri_checked_builder_merkle_targets_def
    by (rule merkle_prefix_path_targets_mono) auto
  have no_composition:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets
          (set (staged_composition_fri_roots data)) s) s t"
    using no_target hash_map_new_output_hit_subset[OF targets_subset]
    by blast
  have layers:
      "fri_builder_conceptual_layers
          (staged_composition_fri_roots data) t
          (staged_composition_final data) =
        fri_builder_conceptual_layers
          (staged_composition_fri_roots data) s
          (staged_composition_final data)"
    by (rule fri_builder_conceptual_layers_stable_if_no_target[
        OF ext no_composition])
  show ?thesis
    unfolding fri_conditioned_composition_residual_query_lists_def
      fri_conditioned_quantitative_residual_query_lists_def
    by (simp add: layers)
qed

lemma fri_conditioned_combined_query_head_lists_stable_if_no_builder_target:
  assumes ext: "s \<le> t"
    and no_target:
      "\<not> hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data s) s t"
  shows
    "fri_conditioned_combined_query_head_lists
        prefix prefix_state data t =
      fri_conditioned_combined_query_head_lists
        prefix prefix_state data s"
  unfolding fri_conditioned_combined_query_head_lists_def
    fri_conditioned_trace_query_head_lists_def
    fri_conditioned_composition_query_head_lists_def
  using
    fri_conditioned_trace_residual_query_lists_stable_if_no_builder_target[
      OF ext no_target]
    fri_conditioned_composition_residual_query_lists_stable_if_no_builder_target[
      OF ext no_target]
  by simp



lemma checked_builder_conditioned_residual_imp_actual_or_query_phase_target:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and residual:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        fri_conditioned_combined_query_head_lists
          prefix prefix_state data attacker_state"
  shows
    "hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data query_start)
        query_start attacker_state \<or>
      ro_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_combined_query_head_lists
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
proof (cases
    "hash_map_new_output_hit
      (fri_checked_builder_merkle_targets data query_start)
      query_start attacker_state")
  case True
  then show ?thesis by simp
next
  case False
  have props:
      "length raws = rounds \<and>
       length query_states = rounds \<and>
       length (staged_query_chunks data) = rounds \<and>
       query_start \<le> attacker_state"
    using
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
        OF wf controlled outcome]
    by blast
  have stable:
      "fri_conditioned_combined_query_head_lists
          prefix prefix_state data attacker_state =
        fri_conditioned_combined_query_head_lists
          prefix prefix_state data query_start"
    by (rule
      fri_conditioned_combined_query_head_lists_stable_if_no_builder_target[
        OF _ False])
      (use props in blast)
  have residual_start:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        fri_conditioned_combined_query_head_lists
          prefix prefix_state data query_start"
    using residual stable by simp
  have data_eq:
      "fri_conditioned_combined_query_head_lists
          prefix prefix_state (ro_query_head_data data) query_start =
        fri_conditioned_combined_query_head_lists
          prefix prefix_state data query_start"
    unfolding fri_conditioned_combined_query_head_lists_def
      fri_conditioned_trace_query_head_lists_def
      fri_conditioned_composition_query_head_lists_def
      fri_conditioned_trace_residual_query_lists_def
      fri_conditioned_composition_residual_query_lists_def
      ro_query_head_data_def
    by simp
  have actual:
      "ro_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_combined_query_head_lists
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
    unfolding ro_query_head_dependent_actual_query_index_list_hit_def
    using residual_start data_eq by simp
  then show ?thesis by simp
qed



lemma fri_checked_builder_merkle_targets_card_bound_from_head:
  assumes trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    and composition_len:
      "length (staged_composition_fri_roots data) \<le>
        ceil_log (maxDegree + 1)"
    and domain:
      "card (fmdom' (HashMap s)) \<le> q"
  shows
    "card (fri_checked_builder_merkle_targets data s) \<le>
      ceil_log clength + ceil_log (maxDegree + 1) + 2 * q"
proof -
  have roots_card:
      "card
          (set (staged_trace_fri_roots data) \<union>
            set (staged_composition_fri_roots data)) \<le>
        ceil_log clength + ceil_log (maxDegree + 1)"
  proof -
    have "card
        (set (staged_trace_fri_roots data) \<union>
          set (staged_composition_fri_roots data)) \<le>
        card (set (staged_trace_fri_roots data)) +
          card (set (staged_composition_fri_roots data))"
      by (rule card_Un_le)
    also have "... \<le>
        length (staged_trace_fri_roots data) +
          length (staged_composition_fri_roots data)"
      by (rule add_mono; rule card_length)
    also have "... \<le>
        ceil_log clength + ceil_log (maxDegree + 1)"
      using trace_len composition_len by simp
    finally show ?thesis .
  qed
  have target_card:
      "card (fri_checked_builder_merkle_targets data s) \<le>
        card
          (set (staged_trace_fri_roots data) \<union>
            set (staged_composition_fri_roots data)) +
          2 * card (fmdom' (HashMap s))"
    unfolding fri_checked_builder_merkle_targets_def
    by (rule card_merkle_prefix_path_targets_le) simp
  show ?thesis
    using target_card roots_card domain by linarith
qed



lemma fri_conditioned_trace_quantitative_at_imp_combined_query_head:
  assumes i_bound: "i < length challenges"
    and quantitative:
      "query_idxs \<in>
        fri_conditioned_quantitative_residual_query_lists_at
          (clength - 1) roots challenges final_value attacker_state i"
    and roots_eq: "roots = staged_trace_fri_roots data"
    and challenges_eq: "challenges = staged_trace_fri_challenges data"
    and final_eq: "final_value = staged_trace_final data"
  shows
    "query_idxs \<in>
      fri_conditioned_combined_query_head_lists
        prefix prefix_state data attacker_state"
proof -
  have full:
      "query_idxs \<in>
        fri_conditioned_quantitative_residual_query_lists
          (clength - 1) roots challenges final_value attacker_state"
    unfolding fri_conditioned_quantitative_residual_query_lists_union
    using i_bound quantitative by blast
  have trace:
      "query_idxs \<in>
        fri_conditioned_trace_residual_query_lists data attacker_state"
    using full roots_eq challenges_eq final_eq
    unfolding fri_conditioned_trace_residual_query_lists_def
    by simp
  show ?thesis
    unfolding fri_conditioned_combined_query_head_lists_def
      fri_conditioned_trace_query_head_lists_def
    using trace by blast
qed

lemma fri_conditioned_composition_quantitative_at_imp_combined_query_head:
  assumes degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and i_bound: "i < length challenges"
    and quantitative:
      "query_idxs \<in>
        fri_conditioned_quantitative_residual_query_lists_at
          (to_nat (staged_degree data)) roots challenges final_value
          attacker_state i"
    and roots_eq: "roots = staged_composition_fri_roots data"
    and challenges_eq:
      "challenges = staged_composition_fri_challenges data"
    and final_eq: "final_value = staged_composition_final data"
  shows
    "query_idxs \<in>
      fri_conditioned_combined_query_head_lists
        prefix prefix_state data attacker_state"
proof -
  have full:
      "query_idxs \<in>
        fri_conditioned_quantitative_residual_query_lists
          (to_nat (staged_degree data)) roots challenges final_value
          attacker_state"
    unfolding fri_conditioned_quantitative_residual_query_lists_union
    using i_bound quantitative by blast
  have composition:
      "query_idxs \<in>
        fri_conditioned_composition_residual_query_lists data attacker_state"
    using full degree_bound roots_eq challenges_eq final_eq
    unfolding fri_conditioned_composition_residual_query_lists_def
    by simp
  show ?thesis
    unfolding fri_conditioned_combined_query_head_lists_def
      fri_conditioned_composition_query_head_lists_def
    using composition by blast
qed



lemma
  checked_builder_trace_candidate_bad_imp_actual_residual_or_targets:
  fixes final_state :: "'f protocol_channel"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
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
    and candidate_bad:
      "\<not> trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)"
  shows
    "hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state \<or>
      fri_checked_builder_merkle_target_hit data attacker_state final_state \<or>
      hash_state_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          conditioned_trace_fri_bad_challenge_relation)
        (HashMap adversary_initial_state) (HashMap attacker_state) \<or>
      hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data query_start)
        query_start attacker_state \<or>
      ro_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_combined_query_head_lists
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
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have rounds_le: "ceil_log clength \<le> N"
  proof -
    have clength_le: "clength \<le> clength * scale"
      using scale_pos by simp
    show ?thesis
      by (rule ceil_log_le_power) (use clength_le eval_power in simp)
  qed

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
      have start_not_low:
          "\<not> fri_table_low_degree_on
            (fri_padded_degree_bound (clength - 1))
            (fri_canonical_domain_at 0)
            (fri_conditioned_layer_table 0
              (fri_builder_conceptual_layers (map snd f_fl) attacker_state
                f_final ! 0))"
        using candidate_bad conditioned_layer0
        unfolding fri_padded_degree_bound_clength_pred
          fri_canonical_domain_at_0
          trace_table_low_degree_iff_fri_table_low_degree_on_eval_domain
        by simp

      have round_count:
          "length (map fst f_fl) = ceil_log (Suc (clength - 1))"
        using challenge_len clength_pos by simp
      have padded_rounds_le:
          "ceil_log (Suc (clength - 1)) \<le> N"
        using rounds_le clength_pos by simp
      have split:
          "(\<exists>j < length (map fst f_fl).
              map fst f_fl ! j \<in>
                fri_online_bad_challenges (clength - 1) j attacker_state
                  (map snd f_fl ! j)) \<or>
            (\<exists>i < length (map fst f_fl).
              map fst f_fl ! i \<notin>
                fri_conditioned_bad_challenges (clength - 1)
                  (\<lambda>j _. fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final ! j)
                  i (take i (map fst f_fl)) \<and>
              \<not> fri_table_low_degree_on
                (fri_degree_after i
                  (fri_padded_degree_bound (clength - 1)))
                (fri_canonical_domain_at i)
                (fri_conditioned_layer_table i
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final ! i)) \<and>
              fri_table_low_degree_on
                (fri_degree_after (Suc i)
                  (fri_padded_degree_bound (clength - 1)))
                (fri_canonical_domain_at (Suc i))
                (fri_conditioned_layer_table (Suc i)
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final ! Suc i)) \<and>
              map (\<lambda>raw. index (to_nat raw)) raws \<in>
                fri_conditioned_residual_query_lists
                  (map snd f_fl) (map fst f_fl)
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final) i)"
        by (rule fri_builder_authenticated_chain_online_or_quantitative_residual[
          OF trace_chain eval_power round_count padded_rounds_le
            attacker_final_ext attacker_clean no_builder_trace_target
            trace_authenticated start_not_low])

      have final_map:
          "HashMap
              (channel_for_hash_map (HashMap attacker_state)) =
            HashMap attacker_state"
        unfolding channel_for_hash_map_def adversary_initial_state_def by simp
      have builder_layers_map:
          "fri_builder_conceptual_layers (map snd f_fl)
              (channel_for_hash_map (HashMap attacker_state))
              (staged_trace_final data) =
            fri_builder_conceptual_layers (map snd f_fl)
              attacker_state f_final"
      proof -
        have table_map:
            "\<And>root len.
              conceptual_table
                  (channel_for_hash_map (HashMap attacker_state)) root len =
                conceptual_table attacker_state root len"
          by (rule conceptual_table_cong_hash_map[OF final_map])
        show ?thesis
          unfolding fri_builder_conceptual_layers_def trace_final_eq
          by (simp add: table_map)
      qed
      have challenge_prefixes:
          "length (staged_trace_fri_roots data) = ceil_log clength \<and>
           length (staged_trace_fri_challenges data) = ceil_log clength \<and>
           (\<forall>j < length (staged_trace_fri_roots data). \<exists>final.
             ro_absorb_lookup_chain attacker_state
               (PState adversary_initial_state)
               (staged_trace_root data #
                 take (Suc j) (staged_trace_fri_roots data)) final \<and>
             fmlookup (HashMap attacker_state) (TraceFriChallenge j final) =
               Some (staged_trace_fri_challenges data ! j)) \<and>
           length (staged_alphas data) = length spec \<and>
           length (staged_composition_fri_roots data) =
             ceil_log (Suc (to_nat (staged_degree data))) \<and>
           length (staged_composition_fri_challenges data) =
             ceil_log (Suc (to_nat (staged_degree data))) \<and>
           (\<forall>j < length (staged_composition_fri_roots data). \<exists>final.
             ro_absorb_lookup_chain attacker_state
               (PState adversary_initial_state)
               (composition_fri_challenge_prefix_messages
                 (staged_trace_root data)
                 (staged_trace_fri_roots data)
                 (staged_trace_final data)
                 (staged_alphas data)
                 (staged_degree data)
                 (staged_composition_fri_roots data) j) final \<and>
             fmlookup (HashMap attacker_state)
               (CompositionFriChallenge j final) =
               Some (staged_composition_fri_challenges data ! j))"
        by (rule
          ro_checked_staged_transcript_program_conditioned_challenge_prefixes[
            OF wf controlled original_out])
      have trace_challenge_evidence:
          "ro_conditioned_trace_challenge_evidence
            (HashMap attacker_state)
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_fri_challenges data)"
      proof -
        have lengths:
            "length (staged_trace_fri_challenges data) =
              length (staged_trace_fri_roots data)"
          using challenge_prefixes by simp
        have at:
            "\<forall>j < length (staged_trace_fri_roots data). \<exists>final.
              ro_absorb_lookup_chain
                (channel_for_hash_map (HashMap attacker_state))
                (PState adversary_initial_state)
                (staged_trace_root data #
                  take (Suc j) (staged_trace_fri_roots data)) final \<and>
              fmlookup (HashMap attacker_state)
                (TraceFriChallenge j final) =
                Some (staged_trace_fri_challenges data ! j)"
        proof (intro allI impI)
          fix j
          assume j_bound: "j < length (staged_trace_fri_roots data)"
          from challenge_prefixes j_bound obtain state where
            chain:
              "ro_absorb_lookup_chain attacker_state
                (PState adversary_initial_state)
                (staged_trace_root data #
                  take (Suc j) (staged_trace_fri_roots data)) state"
            and lookup:
              "fmlookup (HashMap attacker_state)
                (TraceFriChallenge j state) =
                Some (staged_trace_fri_challenges data ! j)"
            by blast
          have chain':
              "ro_absorb_lookup_chain
                (channel_for_hash_map (HashMap attacker_state))
                (PState adversary_initial_state)
                (staged_trace_root data #
                  take (Suc j) (staged_trace_fri_roots data)) state"
            by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
              (rule chain)
          show "\<exists>final.
              ro_absorb_lookup_chain
                (channel_for_hash_map (HashMap attacker_state))
                (PState adversary_initial_state)
                (staged_trace_root data #
                  take (Suc j) (staged_trace_fri_roots data)) final \<and>
              fmlookup (HashMap attacker_state)
                (TraceFriChallenge j final) =
                Some (staged_trace_fri_challenges data ! j)"
            using chain' lookup by blast
        qed
        show ?thesis
          unfolding ro_conditioned_trace_challenge_evidence_def
          using lengths at by blast
      qed

      from split show ?thesis
      proof
        assume online:
            "\<exists>j < length (map fst f_fl).
              map fst f_fl ! j \<in>
                fri_online_bad_challenges (clength - 1) j attacker_state
                  (map snd f_fl ! j)"
        have staged_online:
            "\<exists>j < length (staged_trace_fri_roots data).
              staged_trace_fri_challenges data ! j \<in>
                fri_online_bad_challenges (clength - 1) j attacker_state
                  (staged_trace_fri_roots data ! j)"
          using online trace_challenges_eq trace_roots_eq trace_chain
          unfolding generic_fri_recorded_value_chain_evidence_def
          by simp
        have transition:
            "hash_state_relation_transition
              (conditioned_fri_relation_bounded
                (ro_checked_staged_transcript_hash_query_budget_for budgets)
                conditioned_trace_fri_bad_challenge_relation)
              (HashMap adversary_initial_state) (HashMap attacker_state)"
          by (rule
            checked_builder_trace_online_bad_imp_bounded_relation_transition[
              OF wf controlled builder_out attacker_clean no_initial
                staged_online])
        then show ?thesis by simp
      next
        assume residual:
            "\<exists>i < length (map fst f_fl).
              map fst f_fl ! i \<notin>
                fri_conditioned_bad_challenges (clength - 1)
                  (\<lambda>j _. fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final ! j)
                  i (take i (map fst f_fl)) \<and>
              \<not> fri_table_low_degree_on
                (fri_degree_after i
                  (fri_padded_degree_bound (clength - 1)))
                (fri_canonical_domain_at i)
                (fri_conditioned_layer_table i
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final ! i)) \<and>
              fri_table_low_degree_on
                (fri_degree_after (Suc i)
                  (fri_padded_degree_bound (clength - 1)))
                (fri_canonical_domain_at (Suc i))
                (fri_conditioned_layer_table (Suc i)
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final ! Suc i)) \<and>
              map (\<lambda>raw. index (to_nat raw)) raws \<in>
                fri_conditioned_residual_query_lists
                  (map snd f_fl) (map fst f_fl)
                  (fri_builder_conceptual_layers (map snd f_fl)
                    attacker_state f_final) i"
        then obtain i where
          i_bound: "i < length (map fst f_fl)"
          and not_bad:
            "map fst f_fl ! i \<notin>
              fri_conditioned_bad_challenges (clength - 1)
                (\<lambda>j _. fri_builder_conceptual_layers (map snd f_fl)
                  attacker_state f_final ! j)
                i (take i (map fst f_fl))"
          and current_bad:
            "\<not> fri_table_low_degree_on
              (fri_degree_after i
                (fri_padded_degree_bound (clength - 1)))
              (fri_canonical_domain_at i)
              (fri_conditioned_layer_table i
                (fri_builder_conceptual_layers (map snd f_fl)
                  attacker_state f_final ! i))"
          and next_low:
            "fri_table_low_degree_on
              (fri_degree_after (Suc i)
                (fri_padded_degree_bound (clength - 1)))
              (fri_canonical_domain_at (Suc i))
              (fri_conditioned_layer_table (Suc i)
                (fri_builder_conceptual_layers (map snd f_fl)
                  attacker_state f_final ! Suc i))"
          and residual_query:
            "map (\<lambda>raw. index (to_nat raw)) raws \<in>
              fri_conditioned_residual_query_lists
                (map snd f_fl) (map fst f_fl)
                (fri_builder_conceptual_layers (map snd f_fl)
                  attacker_state f_final) i"
          by blast
        have quantitative:
            "map (\<lambda>raw. index (to_nat raw)) raws \<in>
              fri_conditioned_quantitative_residual_query_lists_at
                (clength - 1) (map snd f_fl) (map fst f_fl) f_final
                attacker_state i"
          unfolding fri_conditioned_quantitative_residual_query_lists_at_def
          using query_idxs_space not_bad current_bad next_low residual_query
          by blast
        have combined_head:
            "map (\<lambda>raw. index (to_nat raw)) raws \<in>
              fri_conditioned_combined_query_head_lists
                prefix prefix_state data attacker_state"
          by (rule
            fri_conditioned_trace_quantitative_at_imp_combined_query_head[
              where i=i, OF i_bound quantitative])
            (use trace_roots_eq trace_challenges_eq trace_final_eq in simp_all)
        have actual_or_target:
            "hash_map_new_output_hit
                (fri_checked_builder_merkle_targets data query_start)
                query_start attacker_state \<or>
              ro_query_head_dependent_actual_query_index_list_hit
                fri_conditioned_combined_query_head_lists
                (Some ((((prefix, prefix_state), data, query_start, raws,
                  query_states), attacker_state)))"
          by (rule
            checked_builder_conditioned_residual_imp_actual_or_query_phase_target[
              OF wf controlled builder_out combined_head])
        then show ?thesis by blast
      qed
    qed
  qed
qed


lemma checked_builder_composition_padded_candidate_bad_imp_actual_residual_or_targets:
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
     hash_map_new_output_hit
        (fri_checked_builder_merkle_targets data query_start)
        query_start attacker_state \<or>
     ro_query_head_dependent_actual_query_index_list_hit
        fri_conditioned_combined_query_head_lists
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
        have combined_head:
            "?query_idxs \<in>
              fri_conditioned_combined_query_head_lists
                prefix prefix_state data attacker_state"
          by (rule
            fri_conditioned_composition_quantitative_at_imp_combined_query_head[
              where i=i, OF degree_bound i_bound quantitative])
            (use composition_roots_eq composition_challenges_eq
              composition_final_eq in simp_all)
        have actual_or_target:
            "hash_map_new_output_hit
                (fri_checked_builder_merkle_targets data query_start)
                query_start attacker_state \<or>
              ro_query_head_dependent_actual_query_index_list_hit
                fri_conditioned_combined_query_head_lists
                (Some ((((prefix, prefix_state), data, query_start, raws,
                  query_states), attacker_state)))"
          by (rule
            checked_builder_conditioned_residual_imp_actual_or_query_phase_target[
              OF wf controlled builder_out combined_head])
        then show ?thesis by blast
      qed    qed
  qed
qed




end
end
