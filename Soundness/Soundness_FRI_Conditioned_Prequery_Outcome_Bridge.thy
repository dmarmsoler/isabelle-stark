theory Soundness_FRI_Conditioned_Prequery_Outcome_Bridge
  imports Stark.Soundness_FRI_Conditioned_Prequery_Transition_Bound
begin

context soundness
begin

lemma ro_conditioned_residual_absorbed_query_relation_activeI:
  assumes clean:
      "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
    and trace_len: "length trace_roots = ceil_log clength"
    and alpha_len: "length as = length spec"
    and composition_len:
      "length composition_roots = ceil_log (Suc (to_nat dg))"
    and degree_bound: "to_nat dg \<le> maxDegree"
    and header_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        query_start"
    and query_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M) query_start
        (List.concat (take j query_chunks)) final"
    and raws_len: "length raws = rounds"
    and raws_in:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_conditioned_combined_residual_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final"
    and j_bound: "j < rounds"
    and lookup:
      "fmlookup M (QueryIndexChallenge j final) = Some (raws ! j)"
  shows
    "hash_state_relation_active
      ro_conditioned_augmented_absorbed_query_relation M
      (QueryIndexChallenge j final) (raws ! j)"
proof -
  have rel:
      "ro_conditioned_residual_absorbed_query_relation M
        (QueryIndexChallenge j final) (raws ! j)"
    unfolding ro_conditioned_residual_absorbed_query_relation_def Let_def
    using clean no_initial trace_len alpha_len composition_len degree_bound
      header_chain query_chain raws_len raws_in j_bound
    by blast
  show ?thesis
    unfolding hash_state_relation_active_def
      ro_conditioned_augmented_absorbed_query_relation_def
    using lookup rel by blast
qed

lemma ro_conditioned_degenerate_absorbed_query_relation_activeI:
  assumes clean:
      "\<not> hash_map_output_collision (channel_for_hash_map M)"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values (channel_for_hash_map M)"
    and trace_len: "length trace_roots = ceil_log clength"
    and alpha_len: "length as = length spec"
    and composition_len:
      "length composition_roots = ceil_log (Suc (to_nat dg))"
    and degree_bound: "to_nat dg \<le> maxDegree"
    and header_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M)
        (PState adversary_initial_state)
        (verifier_header_messages fr trace_roots trace_final as dg
          composition_roots composition_final)
        query_start"
    and query_chain:
      "ro_absorb_lookup_chain (channel_for_hash_map M) query_start
        (List.concat (take j query_chunks)) final"
    and raws_len: "length raws = rounds"
    and degenerate:
      "(\<exists>i < length trace_roots.
          map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_trace_degenerate_query_lists_at
              M trace_roots trace_final i j) \<or>
       (\<exists>i < length composition_roots.
          map (\<lambda>raw. index (to_nat raw)) raws \<in>
            ro_conditioned_composition_degenerate_query_lists_at
              M dg composition_roots composition_final i j)"
    and j_bound: "j < rounds"
    and lookup:
      "fmlookup M (QueryIndexChallenge j final) = Some (raws ! j)"
  shows
    "hash_state_relation_active
      ro_conditioned_augmented_absorbed_query_relation M
      (QueryIndexChallenge j final) (raws ! j)"
proof -
  have rel:
      "ro_conditioned_degenerate_absorbed_query_relation M
        (QueryIndexChallenge j final) (raws ! j)"
    unfolding ro_conditioned_degenerate_absorbed_query_relation_def Let_def
    using clean no_initial trace_len alpha_len composition_len degree_bound
      header_chain query_chain raws_len degenerate j_bound
    by blast
  show ?thesis
    unfolding hash_state_relation_active_def
      ro_conditioned_augmented_absorbed_query_relation_def
    using lookup rel by blast
qed


lemma fri_conditioned_trace_quantitative_residual_imp_combined:
  assumes evidence:
      "ro_conditioned_trace_challenge_evidence M fr trace_roots trace_bs"
    and i_bound: "i < length trace_roots"
    and residual:
      "query_idxs \<in>
        fri_conditioned_quantitative_residual_query_lists_at_value
          (clength - 1) trace_roots (trace_bs ! i) trace_final
          (channel_for_hash_map M) i"
  shows
    "query_idxs \<in>
      ro_conditioned_combined_residual_query_lists M
        fr trace_roots trace_final as dg composition_roots
        composition_final"
proof -
  have challenge:
      "trace_bs ! i \<in>
        ro_conditioned_trace_challenge_values_at M fr trace_roots i"
    unfolding ro_conditioned_trace_challenge_values_at_def
    using ro_conditioned_trace_challenge_evidence_imp_at[
      OF evidence i_bound] by simp
  have local:
      "query_idxs \<in>
        ro_conditioned_trace_residual_query_lists_at M fr trace_roots
          trace_final i"
    unfolding ro_conditioned_trace_residual_query_lists_at_def
      ro_conditioned_trace_residual_query_lists_at_value_def
    using challenge residual by blast
  have trace:
      "query_idxs \<in>
        ro_conditioned_trace_residual_query_lists M fr trace_roots
          trace_final"
    unfolding ro_conditioned_trace_residual_query_lists_def
    using i_bound local by blast
  show ?thesis
    unfolding ro_conditioned_combined_residual_query_lists_def
    using trace by blast
qed

lemma fri_conditioned_composition_quantitative_residual_imp_combined:
  assumes evidence:
      "ro_conditioned_composition_challenge_evidence M
        fr trace_roots trace_final as dg composition_roots composition_bs"
    and degree_bound: "to_nat dg \<le> maxDegree"
    and i_bound: "i < length composition_roots"
    and residual:
      "query_idxs \<in>
        fri_conditioned_quantitative_residual_query_lists_at_value
          (to_nat dg) composition_roots (composition_bs ! i)
          composition_final (channel_for_hash_map M) i"
  shows
    "query_idxs \<in>
      ro_conditioned_combined_residual_query_lists M
        fr trace_roots trace_final as dg composition_roots
        composition_final"
proof -
  have challenge:
      "composition_bs ! i \<in>
        ro_conditioned_composition_challenge_values_at M
          fr trace_roots trace_final as dg composition_roots i"
    unfolding ro_conditioned_composition_challenge_values_at_def
    using ro_conditioned_composition_challenge_evidence_imp_at[
      OF evidence i_bound] by simp
  have local:
      "query_idxs \<in>
        ro_conditioned_composition_residual_query_lists_at M
          fr trace_roots trace_final as dg composition_roots
          composition_final i"
    unfolding ro_conditioned_composition_residual_query_lists_at_def
      ro_conditioned_composition_residual_query_lists_at_value_def
      if_P[OF degree_bound]
    using challenge residual by blast
  have composition:
      "query_idxs \<in>
        ro_conditioned_composition_residual_query_lists M
          fr trace_roots trace_final as dg composition_roots
          composition_final"
    unfolding ro_conditioned_composition_residual_query_lists_def
    using i_bound local by blast
  show ?thesis
    unfolding ro_conditioned_combined_residual_query_lists_def
    using composition by blast
qed


lemma checked_builder_conditioned_residual_imp_bounded_relation_transition:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin>
        hash_map_output_values attacker_state"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and residual:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_conditioned_combined_residual_query_lists
          (HashMap attacker_state)
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
  shows
    "hash_state_relation_transition
      (conditioned_fri_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets)
        ro_conditioned_augmented_absorbed_query_relation)
      (HashMap adversary_initial_state)
      (HashMap attacker_state)"
proof -
  have outcome_props:
      "length raws = rounds \<and>
       length query_states = rounds \<and>
       length (staged_query_chunks data) = rounds \<and>
       query_start \<le> attacker_state \<and>
       (\<forall>j < rounds.
         fmlookup (HashMap attacker_state)
           (QueryIndexChallenge
             (PQueryCounter (query_states ! j))
             (PState (query_states ! j))) =
           Some (raws ! j))"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
        OF wf controlled outcome])
  have witness_props:
      "length raws = rounds \<and>
       length query_states = rounds \<and>
       length (staged_query_chunks data) = rounds \<and>
       query_start \<le> attacker_state \<and>
       PQueryCounter attacker_state = PQueryCounter query_start + rounds \<and>
       (\<forall>j < rounds.
         query_states ! j \<le> attacker_state \<and>
         PQueryCounter (query_states ! j) =
           PQueryCounter query_start + j \<and>
         fmlookup (HashMap attacker_state)
           (QueryIndexChallenge
             (PQueryCounter (query_states ! j))
             (PState (query_states ! j))) =
           Some (raws ! j) \<and>
         verifier_query_round_chunk
           (index (to_nat (raws ! j)))
           (staged_trace_fri_roots data)
           (staged_composition_fri_roots data)
           (staged_query_chunks data ! j)) \<and>
       (\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale)"
    by (rule
      ro_checked_staged_transcript_program_with_query_witnesses_outcome[
        OF wf controlled
          ro_checked_staged_transcript_program_with_first_root_witnesses_projection_outcome[
            OF nonempty outcome]])
  have good_fields:
      "prefix_state \<le> attacker_state \<and>
       PQueryCounter query_start = 0"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_good_fields[
        OF wf controlled nonempty outcome])
  have zero_bound: "0 < rounds"
    by (rule rounds_positive)
  have chains:
      "prefix =
          (staged_trace_root data, [],
            hd (staged_trace_fri_roots data)) \<and>
       ro_absorb_lookup_chain attacker_state
         (PState adversary_initial_state)
         (verifier_header_messages
           (staged_trace_root data)
           (staged_trace_fri_roots data)
           (staged_trace_final data)
           (staged_alphas data)
           (staged_degree data)
           (staged_composition_fri_roots data)
           (staged_composition_final data))
         (PState query_start) \<and>
       ro_absorb_lookup_chain attacker_state
         (PState query_start)
         (List.concat (take 0 (staged_query_chunks data)))
         (PState (query_states ! 0))"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain[
        OF wf controlled nonempty outcome clean zero_bound])
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome[
        OF nonempty outcome])
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
    by (rule ro_checked_staged_transcript_program_outcome_shape[
      OF original_out])
  have counter0: "PQueryCounter (query_states ! 0) = 0"
    using witness_props good_fields zero_bound by simp
  have lookup0:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! 0))
          (PState (query_states ! 0))) =
        Some (raws ! 0)"
    using outcome_props zero_bound by blast
  have lookup:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge 0 (PState (query_states ! 0))) =
        Some (raws ! 0)"
    using lookup0 counter0 by simp
  have final_map:
      "HashMap (channel_for_hash_map (HashMap attacker_state)) =
        HashMap attacker_state"
    unfolding channel_for_hash_map_def adversary_initial_state_def by simp
  have clean_map:
      "\<not> hash_map_output_collision
        (channel_for_hash_map (HashMap attacker_state))"
    using clean final_map unfolding hash_map_output_collision_def by simp
  have no_initial_map:
      "PState adversary_initial_state \<notin>
        hash_map_output_values
          (channel_for_hash_map (HashMap attacker_state))"
    using no_initial final_map unfolding hash_map_output_values_def by simp
  have header_chain:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (HashMap attacker_state))
        (PState adversary_initial_state)
        (verifier_header_messages
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data))
        (PState query_start)"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (use chains in blast)
  have query_chain:
      "ro_absorb_lookup_chain
        (channel_for_hash_map (HashMap attacker_state))
        (PState query_start)
        (List.concat (take 0 (staged_query_chunks data)))
        (PState (query_states ! 0))"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (use chains in blast)
  have active:
      "hash_state_relation_active
        ro_conditioned_augmented_absorbed_query_relation
        (HashMap attacker_state)
        (QueryIndexChallenge 0 (PState (query_states ! 0)))
        (raws ! 0)"
    by (rule ro_conditioned_residual_absorbed_query_relation_activeI[
      OF clean_map no_initial_map])
      (use shape degree_bound header_chain query_chain outcome_props residual
        zero_bound lookup in simp_all)
  have domain:
      "card (fmdom' (HashMap attacker_state)) \<le>
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound[
        OF wf controlled nonempty outcome clean])
  show ?thesis
    by (rule conditioned_relation_active_imp_bounded_initial_transition[
      OF _ domain])
      (use active in blast)
qed


lemma ceil_log_clength_exact:
  "ceil_log clength = k"
  if clength_eq: "clength = 2 ^ k"
proof -
  have upper: "ceil_log clength \<le> k"
    by (rule ceil_log_le_power) (simp add: clength_eq)
  have lower_power: "clength \<le> 2 ^ ceil_log clength"
    using ceil_log_Suc_power_gt_soundness[of "clength - 1"] clength_pos
    by simp
  have lower: "k \<le> ceil_log clength"
    using lower_power unfolding clength_eq by simp
  show ?thesis
    using upper lower by simp
qed

lemma fri_padded_degree_bound_clength_pred:
  "fri_padded_degree_bound (clength - 1) = clength - 1"
proof -
  obtain k where clength_eq: "clength = 2 ^ k"
    using clength_pow by blast
  have log_eq: "ceil_log clength = k"
    by (rule ceil_log_clength_exact[OF clength_eq])
  show ?thesis
    unfolding fri_padded_degree_bound_def
    using clength_pos clength_eq log_eq
    by simp
qed

lemma
  checked_builder_trace_candidate_bad_imp_conditioned_transitions_or_targets:
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
      hash_state_relation_transition
        (conditioned_fri_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets)
          ro_conditioned_augmented_absorbed_query_relation)
        (HashMap adversary_initial_state) (HashMap attacker_state)"
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
        have quantitative_at:
            "map (\<lambda>raw. index (to_nat raw)) raws \<in>
              fri_conditioned_quantitative_residual_query_lists_at_value
                (clength - 1) (map snd f_fl) (map fst f_fl ! i)
                f_final attacker_state i"
          using quantitative
          unfolding
            fri_conditioned_quantitative_residual_query_lists_at_value_eq[
              OF i_bound]
          .
        have i_bound_staged:
            "i < length (staged_trace_fri_roots data)"
          using i_bound trace_roots_eq trace_challenges_eq trace_chain
          unfolding generic_fri_recorded_value_chain_evidence_def
          by simp
        have builder_layers_staged_map:
            "fri_builder_conceptual_layers (staged_trace_fri_roots data)
                (channel_for_hash_map (HashMap attacker_state))
                (staged_trace_final data) =
              fri_builder_conceptual_layers (map snd f_fl)
                attacker_state f_final"
          using builder_layers_map trace_roots_eq by simp
        have quantitative_staged:
            "map (\<lambda>raw. index (to_nat raw)) raws \<in>
              fri_conditioned_quantitative_residual_query_lists_at_value
                (clength - 1) (staged_trace_fri_roots data)
                (staged_trace_fri_challenges data ! i)
                (staged_trace_final data)
                (channel_for_hash_map (HashMap attacker_state)) i"
          using quantitative_at trace_roots_eq trace_challenges_eq
            builder_layers_staged_map
          unfolding
            fri_conditioned_quantitative_residual_query_lists_at_value_def
            Let_def
          by simp
        have combined:
            "map (\<lambda>raw. index (to_nat raw)) raws \<in>
              ro_conditioned_combined_residual_query_lists
                (HashMap attacker_state)
                (staged_trace_root data)
                (staged_trace_fri_roots data)
                (staged_trace_final data)
                (staged_alphas data)
                (staged_degree data)
                (staged_composition_fri_roots data)
                (staged_composition_final data)"
          by (rule fri_conditioned_trace_quantitative_residual_imp_combined[
              where i = i, OF trace_challenge_evidence i_bound_staged
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
      qed
    qed
  qed
qed

end
end
