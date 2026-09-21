theory Soundness_FRI_RO_Actual_Query_Obstruction_Collapse
  imports Soundness_FRI_RO_Actual_Query_Obstruction_Bounds
begin

context soundness
begin

lemma generic_fri_authenticated_base_opening_conflict_imp_prefix_target:
  assumes len_eq: "length challenges = length roots"
    and ext: "s \<le> final_state"
    and clean: "\<not> hash_map_output_collision s"
    and authenticated:
      "generic_fri_recorded_chunks_authenticated roots query_idxs
        round_layers final_state"
    and query_bound:
      "\<And>round_idx. round_idx < length query_idxs \<Longrightarrow>
        fri_evidence_layer_idx roots query_idxs round_idx 0 <
          fri_evidence_layer_len roots 0"
    and conflict:
      "generic_fri_sampled_base_opening_conflict
        (conceptual_table s (roots ! 0) (fri_evidence_layer_len roots 0))
        roots challenges query_idxs round_layers"
  shows
    "hash_map_new_output_hit
      (merkle_prefix_path_targets {roots ! 0} s) s final_state"
proof (rule ccontr)
  assume no_target:
    "\<not> hash_map_new_output_hit
      (merkle_prefix_path_targets {roots ! 0} s) s final_state"
  from conflict obtain round_idx xp xp_path xn xn_path where
    challenges_nonempty: "0 < length challenges"
    and round_bound: "round_idx < length query_idxs"
    and step:
      "fri_layer_step_evidence
        (roots ! 0) (challenges ! 0)
        (fri_evidence_layer_len roots 0)
        (fri_evidence_layer_idx roots query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len roots 0)
          (fri_evidence_layer_idx roots query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx 0)
        (fri_evidence_next_value roots challenges query_idxs round_idx 0 xp xn)
        (round_layers ! round_idx ! 0)"
    and no_match:
      "\<not> fri_opening_matches_table (fri_evidence_layer_len roots 0)
        (fri_evidence_layer_idx roots query_idxs round_idx 0)
        (conceptual_table s (roots ! 0) (fri_evidence_layer_len roots 0))
        xp xn"
    unfolding generic_fri_sampled_base_opening_conflict_def
    by blast
  have root_bound: "0 < length roots"
    using challenges_nonempty len_eq by simp
  have auth:
    "fri_layer_chunk_authenticated
      (roots ! 0) (fri_evidence_layer_len roots 0)
      (fri_evidence_layer_idx roots query_idxs round_idx 0)
      (round_layers ! round_idx ! 0) final_state"
    using authenticated round_bound root_bound
    unfolding generic_fri_recorded_chunks_authenticated_def
    by blast
  from
    fri_layer_chunk_authenticated_agrees_with_prefix_conceptual_table_or_prefix_target_hit[
      OF ext clean auth]
  obtain yp yp_path yn yn_path where
    chunk:
      "fri_layer_opening_chunk (fri_evidence_layer_len roots 0)
        yp yp_path yn yn_path (round_layers ! round_idx ! 0)"
    and base:
      "conceptual_table s (roots ! 0) (fri_evidence_layer_len roots 0) !
        fri_evidence_layer_idx roots query_idxs round_idx 0 = yp"
    and sibling:
      "conceptual_table s (roots ! 0) (fri_evidence_layer_len roots 0) !
        fri_sibling_index (fri_evidence_layer_len roots 0)
          (fri_evidence_layer_idx roots query_idxs round_idx 0) = yn"
    using no_target by blast
  have step_chunk:
    "fri_layer_opening_chunk (fri_evidence_layer_len roots 0)
      xp xp_path xn xn_path (round_layers ! round_idx ! 0)"
    by (rule fri_layer_step_evidenceD(4)[OF step])
  have xp_eq: "yp = xp"
    by (rule fri_layer_opening_chunk_values_unique(1)[OF chunk step_chunk])
  have xn_eq: "yn = xn"
    by (rule fri_layer_opening_chunk_values_unique(2)[OF chunk step_chunk])
  have match:
    "fri_opening_matches_table (fri_evidence_layer_len roots 0)
      (fri_evidence_layer_idx roots query_idxs round_idx 0)
      (conceptual_table s (roots ! 0) (fri_evidence_layer_len roots 0))
      xp xn"
    unfolding fri_opening_matches_table_def
    using query_bound[OF round_bound] base sibling xp_eq xn_eq
    by simp
  show False
    using no_match match by blast
qed


lemma
  ro_absorb_checked_staged_first_root_actual_query_first_not_low_degree_obstruction_collapsed:
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
    and clean: "\<not> hash_map_output_collision final_state"
    and candidate_bad:
      "\<not> trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)"
  shows
    "\<exists>f_fl f_final trace_round_layers.
      map fst f_fl = staged_trace_fri_challenges data \<and>
      map snd f_fl = staged_trace_fri_roots data \<and>
      (generic_fri_sampled_query_candidate_evidence trace_table_low_degree
         (Not \<circ> trace_table_low_degree)
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (clength - 1) (map snd f_fl) (map fst f_fl) f_final
         (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers
         (generic_fri_sampled_assignment_layers
           (first_trace_fri_root_prefix_first_table prefix prefix_state)
           (map snd f_fl) (map fst f_fl) f_final
           (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers) \<or>
       hash_map_new_output_hit
         (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
         prefix_state final_state \<or>
       partial_merkle_inconsistency_bad
         (verifier_state_from_adversary attacker_state
           (staged_proof_transcript data))
         (Some (results, final_state)))"
proof -
  from
    ro_absorb_checked_staged_first_root_actual_query_joint_fri_evidence[
      OF wf controlled nonempty builder_out verifier_out clean,
      where composition_table="[]"]
  obtain f_fl fl f_final final trace_round_layers
      composition_round_layers where
    trace_challenges_eq:
      "map fst f_fl = staged_trace_fri_challenges data"
    and trace_roots_eq:
      "map snd f_fl = staged_trace_fri_roots data"
    and composition_challenges_eq:
      "map fst fl = staged_composition_fri_challenges data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and f_fl_nonempty: "f_fl \<noteq> []"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and trace_partial:
      "generic_fri_partial_evidence trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (clength - 1) (map snd f_fl) (map fst f_fl) f_final
        (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers"
    and composition_partial:
      "generic_fri_partial_evidence
        (composition_table_low_degree (to_nat (staged_degree data))) []
        (to_nat (staged_degree data)) (map snd fl) (map fst fl) final
        (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    and trace_chain:
      "generic_fri_recorded_value_chain_evidence
        (map snd f_fl) (map fst f_fl) f_final
        (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers"
    and composition_chain:
      "generic_fri_recorded_value_chain_evidence
        (map snd fl) (map fst fl) final
        (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    and trace_authenticated:
      "generic_fri_recorded_chunks_authenticated
        (map snd f_fl) (map (\<lambda>raw. index (to_nat raw)) raws)
        trace_round_layers final_state"
    and composition_authenticated:
      "generic_fri_recorded_chunks_authenticated
        (map snd fl) (map (\<lambda>raw. index (to_nat raw)) raws)
        composition_round_layers final_state"
    and raw_bound:
      "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
    .

  let ?query_idxs = "map (\<lambda>raw. index (to_nat raw)) raws"
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have query_bounds:
      "\<And>round_idx. round_idx < length ?query_idxs \<Longrightarrow>
        ?query_idxs ! round_idx < clength * scale"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length ?query_idxs"
    have raw_at: "raws ! round_idx \<in> set raws"
      using round_bound by simp
    show "?query_idxs ! round_idx < clength * scale"
      using raw_bound raw_at round_bound by simp
  qed
  have challenges_nonempty: "0 < length (map fst f_fl)"
    using f_fl_nonempty by simp
  have rounds_bound: "length (map fst f_fl) \<le> N"
  proof -
    have original_out:
        "Some (data, attacker_state) \<in>
          set_dist
            (execute (ro_checked_staged_transcript_program A)
              adversary_initial_state)"
      by (rule
          ro_checked_staged_transcript_program_with_first_root_projection_outcome[
            OF nonempty builder_out])
    have shape:
        "length (staged_trace_fri_roots data) = ceil_log clength"
      using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
      by simp
    have clength_bound: "clength \<le> clength * scale"
      using scale_pos by simp
    have ceil_bound: "ceil_log clength \<le> N"
      by (rule ceil_log_le_power)
        (use clength_bound eval_power in simp)
    have pair_lengths:
        "length (map fst f_fl) = length (map snd f_fl)"
      by simp
    have challenge_len: "length (map fst f_fl) = ceil_log clength"
      using pair_lengths trace_roots_eq shape by simp
    show ?thesis
      using challenge_len ceil_bound by simp
  qed

  have obstruction:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
         (Not \<circ> trace_table_low_degree)
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (clength - 1) (map snd f_fl) (map fst f_fl) f_final
         ?query_idxs trace_round_layers
         (generic_fri_sampled_assignment_layers
           (first_trace_fri_root_prefix_first_table prefix prefix_state)
           (map snd f_fl) (map fst f_fl) f_final
           ?query_idxs trace_round_layers) \<or>
       generic_fri_sampled_base_opening_conflict
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (map snd f_fl) (map fst f_fl) ?query_idxs trace_round_layers \<or>
       partial_merkle_inconsistency_bad
         (verifier_state_from_adversary attacker_state
           (staged_proof_transcript data))
         (Some (results, final_state))"
    by (rule generic_fri_recorded_accepted_obstruction_reduction[
          OF trace_partial trace_chain trace_authenticated candidate_bad
            challenges_nonempty query_bounds eval_power rounds_bound])

  from ro_checked_staged_transcript_program_with_first_root_outcomeE[OF builder_out]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
    and after_out:
      "Some (head_data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A prefix)
            prefix_final)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    by blast
  obtain fr trace_bs first_root where prefix_eq:
    "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  have prefix_props:
      "trace_bs = [] \<and> prefix_state = prefix_final"
    using ro_staged_first_trace_fri_root_prefix_program_chain[
      OF wf controlled nonempty prefix_out[unfolded prefix_eq]]
    by blast
  have prefix_eq': "prefix = (fr, [], first_root)"
    using prefix_eq prefix_props by simp
  have after_fields:
      "staged_trace_root head_data = fr \<and>
       (\<exists>roots. staged_trace_fri_roots head_data = first_root # roots)"
    by (rule ro_checked_staged_after_first_trace_fri_root_prefix_program_fields[
          OF nonempty])
      (use after_out prefix_eq in simp)
  obtain root_tail where data_roots:
      "staged_trace_fri_roots data = first_root # root_tail"
    using after_fields data_eq by auto
  have root0: "map snd f_fl ! 0 = first_root"
    using trace_roots_eq data_roots by simp
  have roots_nonempty: "map snd f_fl \<noteq> []"
    using f_fl_nonempty by simp
  have len0:
      "fri_evidence_layer_len (map snd f_fl) 0 = scale * clength"
    using roots_nonempty
    unfolding fri_evidence_layer_len_def
    by (cases "map snd f_fl") (simp_all add: mult.commute)
  have candidate_eq:
      "first_trace_fri_root_prefix_first_table prefix prefix_state =
       conceptual_table prefix_state (map snd f_fl ! 0)
         (fri_evidence_layer_len (map snd f_fl) 0)"
    unfolding prefix_eq' first_trace_fri_root_prefix_first_table_def
    using root0 len0 by simp

  have prefix_attacker_ext: "prefix_state \<le> attacker_state"
    using ro_checked_staged_transcript_program_with_first_root_good_fields[
      OF wf controlled nonempty builder_out]
    by blast
  have attacker_verifier_ext:
      "attacker_state \<le>
        verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
    by (rule hash_extends_verifier_state_from_adversary_right)
      (rule hash_ext_refl)
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
        ro_checked_staged_transcript_program_with_first_root_projection_outcome[
          OF nonempty builder_out])
  have verifier_final_ext:
      "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data) \<le> final_state"
    using ro_checked_staged_transcript_program_ro_verify_monad_sync[
      OF wf controlled original_out verifier_out]
    by blast
  have prefix_final_ext: "prefix_state \<le> final_state"
    by (rule hash_ext_trans[
          OF prefix_attacker_ext
            hash_ext_trans[OF attacker_verifier_ext verifier_final_ext]])
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_final_ext])
    then show False using clean by contradiction
  qed
  have query_bounds0:
      "\<And>round_idx. round_idx < length ?query_idxs \<Longrightarrow>
        fri_evidence_layer_idx (map snd f_fl) ?query_idxs round_idx 0 <
          fri_evidence_layer_len (map snd f_fl) 0"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length ?query_idxs"
    have idx0:
        "fri_evidence_layer_idx (map snd f_fl) ?query_idxs round_idx 0 =
          ?query_idxs ! round_idx"
      using roots_nonempty
      unfolding fri_evidence_layer_idx_def
      by (cases "map snd f_fl") simp_all
    show
      "fri_evidence_layer_idx (map snd f_fl) ?query_idxs round_idx 0 <
        fri_evidence_layer_len (map snd f_fl) 0"
      using query_bounds[OF round_bound] idx0 len0
      by (simp add: mult.commute)
  qed

  have base_imp_target:
      "generic_fri_sampled_base_opening_conflict
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (map snd f_fl) (map fst f_fl) ?query_idxs trace_round_layers \<Longrightarrow>
       hash_map_new_output_hit
         (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
         prefix_state final_state"
  proof -
    assume base:
      "generic_fri_sampled_base_opening_conflict
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (map snd f_fl) (map fst f_fl) ?query_idxs trace_round_layers"
    have singleton_target:
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {map snd f_fl ! 0} prefix_state)
        prefix_state final_state"
      by (rule
          generic_fri_authenticated_base_opening_conflict_imp_prefix_target[
            OF _ prefix_final_ext prefix_clean trace_authenticated
              query_bounds0])
        (use base candidate_eq in simp_all)
    have target_subset:
      "merkle_prefix_path_targets {map snd f_fl ! 0} prefix_state \<subseteq>
        merkle_prefix_path_targets {fr, first_root} prefix_state"
      by (rule merkle_prefix_path_targets_mono)
        (use root0 in auto)
    have broad_target:
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {fr, first_root} prefix_state)
        prefix_state final_state"
      by (rule hash_map_new_output_hit_subset[OF target_subset singleton_target])
    show
      "hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state"
      using broad_target prefix_clean
      unfolding prefix_eq' first_trace_fri_root_prefix_merkle_targets_def
      by simp
  qed

  show ?thesis
    using trace_challenges_eq trace_roots_eq obstruction base_imp_target
    by blast
qed



lemma
  ro_absorb_checked_staged_security_with_first_root_clean_first_not_low_degree_obstruction_collapsed:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and first_bad:
      "ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
        out"
    and clean: "\<not> final_hash_collision_event out"
  shows
    "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
       out"
proof -
  from first_bad obtain full where out_eq: "out = Some full"
    unfolding
      ro_absorb_checked_staged_security_with_first_root_first_not_low_degree_def
    by (cases out) auto
  obtain prefix prefix_state data query_start raws query_states
      attacker_state result final_state where
    full_eq:
      "full =
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state)"
    by (cases full) (auto split: prod.splits)
  have outcome:
      "Some
          (((((prefix, prefix_state), data, query_start, raws, query_states),
              attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    using support out_eq full_eq by simp
  from
    ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses_outcomeE[
      OF outcome]
  have builder_out:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and verifier_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute ro_verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    by blast+
  have final_clean: "\<not> hash_map_output_collision final_state"
    using clean
    unfolding out_eq full_eq final_hash_collision_event_def
    by simp
  have candidate_bad:
      "\<not> trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)"
    using first_bad
    unfolding out_eq full_eq
      ro_absorb_checked_staged_security_with_first_root_first_not_low_degree_def
    by simp
  from
    ro_absorb_checked_staged_first_root_actual_query_first_not_low_degree_obstruction_collapsed[
      OF wf controlled nonempty builder_out verifier_out final_clean
        candidate_bad]
  obtain f_fl f_final trace_round_layers where
    trace_challenges_eq:
      "map fst f_fl = staged_trace_fri_challenges data"
    and trace_roots_eq: "map snd f_fl = staged_trace_fri_roots data"
    and obstruction:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
         (Not \<circ> trace_table_low_degree)
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (clength - 1) (map snd f_fl) (map fst f_fl) f_final
         (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers
         (generic_fri_sampled_assignment_layers
           (first_trace_fri_root_prefix_first_table prefix prefix_state)
           (map snd f_fl) (map fst f_fl) f_final
           (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers) \<or>
       hash_map_new_output_hit
         (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
         prefix_state final_state \<or>
       partial_merkle_inconsistency_bad
         (verifier_state_from_adversary attacker_state
           (staged_proof_transcript data))
         (Some (result, final_state))"
    by blast
  have no_partial:
      "\<not> partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state))"
  proof
    assume partial:
      "partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state))"
    have collision:
        "hash_map_output_collision_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (Some (result, final_state))"
      by (rule partial_merkle_inconsistency_bad_imp_hash_map_output_collision_bad[
            OF partial])
    show False
      using collision final_clean
      unfolding hash_map_output_collision_bad_def accepted_def
      by simp
  qed
  from obstruction no_partial have sampled_or_target:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
         (Not \<circ> trace_table_low_degree)
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (clength - 1) (map snd f_fl) (map fst f_fl) f_final
         (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers
         (generic_fri_sampled_assignment_layers
           (first_trace_fri_root_prefix_first_table prefix prefix_state)
           (map snd f_fl) (map fst f_fl) f_final
           (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers) \<or>
       hash_map_new_output_hit
         (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
         prefix_state final_state"
    by blast
  then show ?thesis
  proof
    assume sampled:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
         (Not \<circ> trace_table_low_degree)
         (first_trace_fri_root_prefix_first_table prefix prefix_state)
         (clength - 1) (map snd f_fl) (map fst f_fl) f_final
         (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers
         (generic_fri_sampled_assignment_layers
           (first_trace_fri_root_prefix_first_table prefix prefix_state)
           (map snd f_fl) (map fst f_fl) f_final
           (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers)"
    have pair:
        "(map (\<lambda>raw. index (to_nat raw)) raws, map fst f_fl) \<in>
          generic_fri_sampled_query_bad_pair_union trace_table_low_degree
            (Not \<circ> trace_table_low_degree) (clength - 1)"
      using sampled
      unfolding generic_fri_sampled_query_bad_pair_union_def
        generic_fri_sampled_query_bad_pair_set_def
      by blast
    have event_concrete:
        "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
          (Some
            (((((prefix, prefix_state), data, query_start, raws, query_states),
                attacker_state), result), final_state))"
      unfolding
        ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair_def
      using trace_challenges_eq pair by auto
    have event:
        "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
          out"
      using event_concrete out_eq full_eq by simp
    show ?thesis
      using event by simp
  next
    assume target:
      "hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state"
    have event_concrete:
        "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
          (Some
            (((((prefix, prefix_state), data, query_start, raws, query_states),
                attacker_state), result), final_state))"
      unfolding
        ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_def
      using target by simp
    have event:
        "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
          out"
      using event_concrete out_eq full_eq by simp
    show ?thesis
      using event by simp
  qed
qed


lemma
  ro_absorb_checked_staged_security_with_first_root_clean_outcome_obstruction_collapsed_classification:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and accepted_out: "accepted out"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and clean: "\<not> final_hash_collision_event out"
  shows
    "ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
        first_trace_fri_root_prefix_good_agreement_query_lists out \<or>
     ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_tables_equal out"
proof -
  have classified:
      "ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
          first_trace_fri_root_prefix_good_agreement_query_lists out \<or>
       ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_tables_equal out"
    by (rule
        ro_absorb_checked_staged_security_with_first_root_clean_outcome_classification[
          OF wf controlled nonempty accepted_out support clean])
  have first_reduction:
      "ro_absorb_checked_staged_security_with_first_root_first_not_low_degree
          out \<Longrightarrow>
       ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
          out \<or>
       ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
          out"
    by (rule
        ro_absorb_checked_staged_security_with_first_root_clean_first_not_low_degree_obstruction_collapsed[
          OF wf controlled nonempty support _ clean])
  show ?thesis
    using classified first_reduction by blast
qed


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_acceptance_le_obstruction_collapsed_union:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le>
      wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        (\<lambda>out.
          final_hash_collision_event out \<or>
          ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
            first_trace_fri_root_prefix_good_agreement_query_lists out \<or>
          ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
            out \<or>
          ro_absorb_checked_staged_security_with_first_root_tables_equal out)
        adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and accepted_out: "accepted out"
  show
      "final_hash_collision_event out \<or>
       ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
         first_trace_fri_root_prefix_good_agreement_query_lists out \<or>
       ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair
         out \<or>
       ro_absorb_checked_staged_security_with_first_root_tables_equal out"
  proof (cases "final_hash_collision_event out")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis
      using
        ro_absorb_checked_staged_security_with_first_root_clean_outcome_obstruction_collapsed_classification[
          OF wf controlled nonempty accepted_out support False]
      by simp
  qed
qed



definition
  active_route_ro_absorb_first_root_base_conflict_collapsed_bound_for
    :: "staged_budgets \<Rightarrow> 'f staged_adversary \<Rightarrow> prob"
where
  "active_route_ro_absorb_first_root_base_conflict_collapsed_bound_for budgets A =
    hash_collision_budget_value 0
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
    ro_checked_staged_first_root_good_actual_query_error budgets +
    ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
    active_route_ro_absorb_first_root_trace_not_low_degree_error_for A +
    active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for A +
    active_route_ro_absorb_first_root_tables_equal_error_for A"


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_acceptance_base_conflict_collapsed_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le> active_route_ro_absorb_first_root_base_conflict_collapsed_bound_for
          budgets A"
proof -
  let ?M =
    "ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
      A"
  let ?Collision = "final_hash_collision_event"
  let ?Query =
    "ro_absorb_checked_staged_security_with_first_root_dependent_actual_query_index_list_hit
      first_trace_fri_root_prefix_good_agreement_query_lists"
  let ?Target =
    "ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit"
  let ?Trace =
    "ro_absorb_checked_staged_security_with_first_root_trace_not_low_degree"
  let ?Sampled =
    "ro_absorb_checked_staged_security_with_first_root_trace_sampled_bad_pair"
  let ?Equal =
    "ro_absorb_checked_staged_security_with_first_root_tables_equal"

  have classified:
      "wp_event ?M accepted adversary_initial_state \<le>
       wp_event ?M
         (\<lambda>out.
           ?Collision out \<or> ?Query out \<or> ?Target out \<or> ?Trace out \<or>
           ?Sampled out \<or> ?Equal out)
         adversary_initial_state"
    by (rule
        wp_ro_absorb_checked_staged_security_with_first_root_acceptance_le_obstruction_collapsed_union[
          OF wf controlled nonempty])
  have union:
      "wp_event ?M
          (\<lambda>out.
            ?Collision out \<or> ?Query out \<or> ?Target out \<or> ?Trace out \<or>
            ?Sampled out \<or> ?Equal out)
          adversary_initial_state
        \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M ?Query adversary_initial_state +
        wp_event ?M ?Target adversary_initial_state +
        wp_event ?M ?Trace adversary_initial_state +
        wp_event ?M ?Sampled adversary_initial_state +
        wp_event ?M ?Equal adversary_initial_state"
  proof -
    have
      "wp_event ?M
          (\<lambda>out.
            ?Collision out \<or> ?Query out \<or> ?Target out \<or> ?Trace out \<or>
            ?Sampled out \<or> ?Equal out)
          adversary_initial_state
        \<le>
        wp_event ?M ?Collision adversary_initial_state +
        wp_event ?M
          (\<lambda>out.
            ?Query out \<or> ?Target out \<or> ?Trace out \<or>
            ?Sampled out \<or> ?Equal out)
          adversary_initial_state"
      by (rule wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         wp_event ?M
           (\<lambda>out.
             ?Target out \<or> ?Trace out \<or> ?Sampled out \<or> ?Equal out)
           adversary_initial_state)"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         (wp_event ?M ?Target adversary_initial_state +
          wp_event ?M
            (\<lambda>out. ?Trace out \<or> ?Sampled out \<or> ?Equal out)
            adversary_initial_state))"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         (wp_event ?M ?Target adversary_initial_state +
          (wp_event ?M ?Trace adversary_initial_state +
           wp_event ?M (\<lambda>out. ?Sampled out \<or> ?Equal out)
             adversary_initial_state)))"
      by (intro add_mono order_refl wp_event_union_bound)
    also have "... \<le>
        wp_event ?M ?Collision adversary_initial_state +
        (wp_event ?M ?Query adversary_initial_state +
         (wp_event ?M ?Target adversary_initial_state +
          (wp_event ?M ?Trace adversary_initial_state +
           (wp_event ?M ?Sampled adversary_initial_state +
            wp_event ?M ?Equal adversary_initial_state))))"
      by (intro add_mono order_refl wp_event_union_bound)
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  have collision:
      "wp_event ?M ?Collision adversary_initial_state
        \<le> hash_collision_budget_value 0
            (ro_absorb_checked_staged_security_hash_query_budget_for budgets)"
    by (rule
        wp_ro_absorb_checked_staged_security_with_first_root_final_hash_collision_bound[
          OF wf controlled nonempty])
  have query:
      "wp_event ?M ?Query adversary_initial_state
        \<le> ro_checked_staged_first_root_good_actual_query_error budgets"
    using
      active_route_ro_absorb_first_root_good_actual_query_bound[
        OF wf controlled nonempty]
    unfolding active_route_ro_absorb_first_root_good_actual_query_error_for_def
    .
  have target:
      "wp_event ?M ?Target adversary_initial_state
        \<le> ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets"
    by (rule
        wp_ro_absorb_checked_staged_security_with_first_root_prefix_merkle_target_hit_bound[
          OF nonempty wf controlled])
  have closed:
      "wp_event ?M ?Collision adversary_initial_state +
       wp_event ?M ?Query adversary_initial_state +
       wp_event ?M ?Target adversary_initial_state +
       wp_event ?M ?Trace adversary_initial_state +
       wp_event ?M ?Sampled adversary_initial_state +
       wp_event ?M ?Equal adversary_initial_state
       \<le>
       hash_collision_budget_value 0
         (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
       ro_checked_staged_first_root_good_actual_query_error budgets +
       ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
       wp_event ?M ?Trace adversary_initial_state +
       wp_event ?M ?Sampled adversary_initial_state +
       wp_event ?M ?Equal adversary_initial_state"
    by (intro add_mono collision query target order_refl)
  show ?thesis
    unfolding
      active_route_ro_absorb_first_root_base_conflict_collapsed_bound_for_def
      active_route_ro_absorb_first_root_trace_not_low_degree_error_for_def
      active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for_def
      active_route_ro_absorb_first_root_tables_equal_error_for_def
    by (rule order_trans[OF classified order_trans[OF union closed]])
qed


definition
  active_route_ro_absorb_first_root_base_conflict_collapsed_query_parameter_bound_for
    :: "staged_budgets \<Rightarrow> 'f staged_adversary \<Rightarrow> prob"
where
  "active_route_ro_absorb_first_root_base_conflict_collapsed_query_parameter_bound_for
      budgets A =
    hash_collision_budget_value 0
      (ro_absorb_checked_staged_security_hash_query_budget_for budgets) +
    ro_checked_staged_first_root_good_actual_query_error budgets +
    ro_absorb_checked_staged_first_root_prefix_merkle_target_error budgets +
    active_route_ro_absorb_first_root_trace_not_low_degree_error_for A +
    trace_sampled_bad_actual_query_parameter_bound budgets +
    active_route_ro_absorb_first_root_tables_equal_error_for A"


lemma
  wp_ro_absorb_checked_staged_security_with_first_root_acceptance_base_conflict_collapsed_query_parameter_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
        (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
          A)
        accepted adversary_initial_state
      \<le>
      active_route_ro_absorb_first_root_base_conflict_collapsed_query_parameter_bound_for
        budgets A"
proof -
  have collapsed:
      "wp_event
          (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
            A)
          accepted adversary_initial_state
        \<le> active_route_ro_absorb_first_root_base_conflict_collapsed_bound_for
            budgets A"
    by (rule
        wp_ro_absorb_checked_staged_security_with_first_root_acceptance_base_conflict_collapsed_bound[
          OF wf controlled nonempty])
  have sampled:
      "active_route_ro_absorb_first_root_trace_sampled_bad_pair_error_for A
        \<le> trace_sampled_bad_actual_query_parameter_bound budgets"
    by (rule
        active_route_ro_absorb_first_root_trace_sampled_bad_pair_parameter_bound[
          OF wf controlled nonempty])
  have sharpened:
      "active_route_ro_absorb_first_root_base_conflict_collapsed_bound_for
          budgets A
        \<le> active_route_ro_absorb_first_root_base_conflict_collapsed_query_parameter_bound_for
            budgets A"
    unfolding
      active_route_ro_absorb_first_root_base_conflict_collapsed_bound_for_def
      active_route_ro_absorb_first_root_base_conflict_collapsed_query_parameter_bound_for_def
    by (intro add_mono order_refl sampled)
  show ?thesis
    by (rule order_trans[OF collapsed sharpened])
qed



end
end
