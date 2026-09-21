theory Soundness_FRI_RO_Actual_Query_Composition_Candidate
  imports Soundness_FRI_RO_Actual_Query_Trace_Candidate
begin

text \<open>
  The composition candidate is fixed at the checked query boundary, after its
  complete FRI header has been absorbed but before any query index is sampled.
  In the positive-round case it is the conceptual table bound by the first
  composition-FRI root.  In the zero-round case it is the constant table
  checked against the composition final value.  The query-evidence layer
  below keeps the zero- and positive-round cases explicit.
\<close>

context soundness
begin

definition ro_actual_query_composition_candidate
where
  "ro_actual_query_composition_candidate data query_start =
    (if staged_composition_fri_roots data = []
     then replicate (scale * clength) (staged_composition_final data)
     else conceptual_table query_start
       (hd (staged_composition_fri_roots data)) (scale * clength))"

definition ro_actual_query_composition_prefix_targets
where
  "ro_actual_query_composition_prefix_targets data query_start =
    (if staged_composition_fri_roots data = []
     then {}
     else merkle_prefix_path_targets
       {hd (staged_composition_fri_roots data)} query_start)"

definition
  ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
where
  "ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        (map (\<lambda>raw. index (to_nat raw)) raws,
          staged_composition_fri_challenges data) \<in>
        composition_fri_sampled_query_bad_pair_union
          (staged_degree data))"

definition
  ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
where
  "ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        hash_map_new_output_hit
          (ro_actual_query_composition_prefix_targets data query_start)
          query_start final_state)"

lemma ro_actual_query_composition_candidate_zero_round_low_degree:
  assumes empty: "staged_composition_fri_roots data = []"
  shows
    "composition_table_low_degree maxDegree
      (ro_actual_query_composition_candidate data query_start)"
proof -
  have zero_degree: "degree (0 :: 'f poly) \<le> maxDegree"
    by simp
  have table:
      "replicate (scale * clength) (staged_composition_final data) =
        map (poly [:staged_composition_final data:]) eval_domain"
    proof (rule nth_equalityI)
      show
        "length (replicate (scale * clength)
            (staged_composition_final data)) =
          length (map (poly [:staged_composition_final data:]) eval_domain)"
        using eval_domain_length by (simp add: mult.commute)
    next
      fix i
      assume
        "i < length
          (replicate (scale * clength) (staged_composition_final data))"
      then show
        "replicate (scale * clength) (staged_composition_final data) ! i =
          map (poly [:staged_composition_final data:]) eval_domain ! i"
        using eval_domain_length by (simp add: mult.commute)
    qed
  show ?thesis
    unfolding ro_actual_query_composition_candidate_def empty
      composition_table_low_degree_def
    by (intro exI[of _ "[:staged_composition_final data:]"])
      (use table in simp)
qed



lemma
  ro_absorb_checked_staged_first_root_actual_query_composition_not_low_degree_obstruction_collapsed:
  fixes final_state :: "'f protocol_channel"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_nonempty: "0 < ceil_log clength"
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
    and composition_nonempty:
      "staged_composition_fri_roots data \<noteq> []"
    and candidate_bad:
      "\<not> composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate data query_start)"
  shows
    "\<exists>fl final composition_round_layers.
      map fst fl = staged_composition_fri_challenges data \<and>
      map snd fl = staged_composition_fri_roots data \<and>
      (generic_fri_sampled_query_candidate_evidence
         (composition_table_low_degree (to_nat (staged_degree data)))
         (Not \<circ>
           composition_table_low_degree (to_nat (staged_degree data)))
         (ro_actual_query_composition_candidate data query_start)
         (to_nat (staged_degree data))
         (map snd fl) (map fst fl) final
         (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers
         (generic_fri_sampled_assignment_layers
           (ro_actual_query_composition_candidate data query_start)
           (map snd fl) (map fst fl) final
           (map (\<lambda>raw. index (to_nat raw)) raws)
           composition_round_layers) \<or>
       hash_map_new_output_hit
         (ro_actual_query_composition_prefix_targets data query_start)
         query_start final_state \<or>
       partial_merkle_inconsistency_bad
         (verifier_state_from_adversary attacker_state
           (staged_proof_transcript data))
         (Some (results, final_state)))"
proof -
  from
    ro_absorb_checked_staged_first_root_actual_query_joint_fri_evidence[
      OF wf controlled trace_nonempty builder_out verifier_out clean,
      where composition_table=
        "ro_actual_query_composition_candidate data query_start"]
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
        (composition_table_low_degree (to_nat (staged_degree data)))
        (ro_actual_query_composition_candidate data query_start)
        (to_nat (staged_degree data))
        (map snd fl) (map fst fl) final
        (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    and trace_chain:
      "generic_fri_recorded_value_chain_evidence
        (map snd f_fl) (map fst f_fl) f_final
        (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers"
    and composition_chain:
      "generic_fri_recorded_value_chain_evidence
        (map snd fl) (map fst fl) final
        (map (\<lambda>raw. index (to_nat raw)) raws)
        composition_round_layers"
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
  have candidate_bad_current:
      "\<not> composition_table_low_degree (to_nat (staged_degree data))
        (ro_actual_query_composition_candidate data query_start)"
    by (rule composition_table_not_low_degree_mono[
          OF degree_bound candidate_bad])
  have rounds_bound: "length (map fst fl) \<le> N"
  proof -
    have original_out:
        "Some (data, attacker_state) \<in>
          set_dist
            (execute (ro_checked_staged_transcript_program A)
              adversary_initial_state)"
      by (rule
          ro_checked_staged_transcript_program_with_first_root_projection_outcome[
            OF trace_nonempty builder_out])
    have shape:
        "length (staged_composition_fri_roots data) =
           ceil_log (to_nat (staged_degree data) + 1) \<and>
         ceil_log (to_nat (staged_degree data) + 1) \<le>
           ceil_log (maxDegree + 1)"
      using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
      by blast
    have max_degree_bound: "maxDegree + 1 \<le> clength * scale"
      using maxDegree_less_eval_domain by linarith
    have ceil_bound: "ceil_log (maxDegree + 1) \<le> N"
      by (rule ceil_log_le_power)
        (use max_degree_bound eval_power in simp)
    have challenge_len:
        "length (map fst fl) =
          ceil_log (to_nat (staged_degree data) + 1)"
    proof -
      have pair_lengths:
          "length (map fst fl) = length (map snd fl)"
        by simp
      show ?thesis
        using pair_lengths composition_roots_eq shape by simp
    qed
    show ?thesis
      using challenge_len shape ceil_bound by linarith
  qed

  have obstruction:
      "generic_fri_sampled_query_candidate_evidence
         (composition_table_low_degree (to_nat (staged_degree data)))
         (Not \<circ>
           composition_table_low_degree (to_nat (staged_degree data)))
         (ro_actual_query_composition_candidate data query_start)
         (to_nat (staged_degree data))
         (map snd fl) (map fst fl) final ?query_idxs
         composition_round_layers
         (generic_fri_sampled_assignment_layers
           (ro_actual_query_composition_candidate data query_start)
           (map snd fl) (map fst fl) final ?query_idxs
           composition_round_layers) \<or>
       generic_fri_sampled_base_opening_conflict
         (ro_actual_query_composition_candidate data query_start)
         (map snd fl) (map fst fl) ?query_idxs composition_round_layers \<or>
       partial_merkle_inconsistency_bad
         (verifier_state_from_adversary attacker_state
           (staged_proof_transcript data))
         (Some (results, final_state)) \<or>
       (length (map fst fl) = 0 \<and>
         \<not> fri_final_constant_consistent
           (ro_actual_query_composition_candidate data query_start) final)"
    by (rule
        generic_fri_recorded_accepted_obstruction_reduction_or_zero_round[
          OF composition_partial composition_chain composition_authenticated
            candidate_bad_current query_bounds eval_power rounds_bound])

  have roots_nonempty: "map snd fl \<noteq> []"
    using composition_roots_eq composition_nonempty by simp
  have challenges_nonempty: "map fst fl \<noteq> []"
    using roots_nonempty by simp
  have root0:
      "map snd fl ! 0 = hd (staged_composition_fri_roots data)"
    using composition_roots_eq composition_nonempty
    by (cases "staged_composition_fri_roots data") simp_all
  have len0:
      "fri_evidence_layer_len (map snd fl) 0 = scale * clength"
    using roots_nonempty
    unfolding fri_evidence_layer_len_def
    by (cases "map snd fl") (simp_all add: mult.commute)
  have candidate_eq:
      "ro_actual_query_composition_candidate data query_start =
       conceptual_table query_start (map snd fl ! 0)
         (fri_evidence_layer_len (map snd fl) 0)"
    unfolding ro_actual_query_composition_candidate_def
    using composition_nonempty root0 len0 by simp

  have query_start_attacker: "query_start \<le> attacker_state"
    using
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
        OF wf controlled builder_out]
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
          OF trace_nonempty builder_out])
  have verifier_final_ext:
      "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data) \<le> final_state"
    using ro_checked_staged_transcript_program_ro_verify_monad_sync[
      OF wf controlled original_out verifier_out]
    by blast
  have query_start_final_ext: "query_start \<le> final_state"
    by (rule hash_ext_trans[
          OF query_start_attacker
            hash_ext_trans[OF attacker_verifier_ext verifier_final_ext]])
  have query_start_clean: "\<not> hash_map_output_collision query_start"
  proof
    assume collision: "hash_map_output_collision query_start"
    have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[
            OF collision query_start_final_ext])
    then show False using clean by contradiction
  qed
  have query_bounds0:
      "\<And>round_idx. round_idx < length ?query_idxs \<Longrightarrow>
        fri_evidence_layer_idx (map snd fl) ?query_idxs round_idx 0 <
          fri_evidence_layer_len (map snd fl) 0"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length ?query_idxs"
    have idx0:
        "fri_evidence_layer_idx (map snd fl) ?query_idxs round_idx 0 =
          ?query_idxs ! round_idx"
      using roots_nonempty
      unfolding fri_evidence_layer_idx_def
      by (cases "map snd fl") simp_all
    show
      "fri_evidence_layer_idx (map snd fl) ?query_idxs round_idx 0 <
        fri_evidence_layer_len (map snd fl) 0"
      using query_bounds[OF round_bound] idx0 len0
      by (simp add: mult.commute)
  qed

  have base_imp_target:
      "generic_fri_sampled_base_opening_conflict
         (ro_actual_query_composition_candidate data query_start)
         (map snd fl) (map fst fl) ?query_idxs composition_round_layers
       \<Longrightarrow>
       hash_map_new_output_hit
         (ro_actual_query_composition_prefix_targets data query_start)
         query_start final_state"
  proof -
    assume base:
      "generic_fri_sampled_base_opening_conflict
         (ro_actual_query_composition_candidate data query_start)
         (map snd fl) (map fst fl) ?query_idxs composition_round_layers"
    have singleton_target:
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {map snd fl ! 0} query_start)
        query_start final_state"
      by (rule
          generic_fri_authenticated_base_opening_conflict_imp_prefix_target[
            OF _ query_start_final_ext query_start_clean
              composition_authenticated query_bounds0])
        (use base candidate_eq in simp_all)
    show ?thesis
      using singleton_target composition_nonempty root0
      unfolding ro_actual_query_composition_prefix_targets_def
      by simp
  qed

  show ?thesis
    using composition_challenges_eq composition_roots_eq obstruction
      base_imp_target challenges_nonempty
    by blast
qed




lemma ro_verifier_query_round_program_empty_composition_consistent_with_lookup:
  fixes s t :: "'f protocol_channel"
  assumes fl_empty: "fl = []"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (ro_verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx trace_openings where
    "idx = index (to_nat raw)"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "cp_eval as (map opening_value trace_openings) (h ^ idx * shift) =
      final"
proof -
  from outcome obtain raw s1 fv s2 f_i f_x f_len f_pow s3 s4
      i x len pw s5 where
    challenge:
      "Some (raw, s1) \<in> set_dist (execute receive_query_index_challenge s)"
    and decommit:
      "Some (fv, s2) \<in>
        set_dist
          (execute
            (mmap (ro_check_decommit_on_query fr (index (to_nat raw)))) s1)"
    and trace_fri:
      "Some ((f_i, f_x, f_len, f_pow), s3) \<in>
        set_dist
          (execute
            (mfold (index (to_nat raw), hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl)) s2)"
    and trace_assert:
      "Some ((), s4) \<in> set_dist (execute (assert (f_x = f_final)) s3)"
    and composition_fri:
      "Some ((i, x, len, pw), s5) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat raw),
                cp_eval as fv (h ^ index (to_nat raw) * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl)) s4)"
    and composition_assert:
      "Some ((), t) \<in> set_dist (execute (assert (x = final)) s5)"
    unfolding ro_verifier_query_round_program_def
    by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)
  let ?idx = "index (to_nat raw)"
  have idx_sample: "?idx \<in> query_sample_space"
    using index_less_query_sample_space
    unfolding query_sample_space_def by simp
  from ro_check_decommit_on_query_authenticated_openings[
      OF idx_sample decommit]
  obtain trace_openings where
    trace_values: "map opening_value trace_openings = fv"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled ?idx"
    and trace_table_s2:
      "partial_authenticated_table fr (scale * clength)
        trace_openings s2"
    by blast
  have s2_s3: "s2 \<le> s3"
    using ro_receive_query_commits_outcome_extends_counter[OF trace_fri]
    by blast
  have s4_eq: "s4 = s3"
    using trace_assert unfolding assert_def
    by (cases "f_x = f_final") (auto simp: throw_no_outcome)
  have comp_out:
      "(i, x, len, pw) =
        (?idx, cp_eval as fv (h ^ ?idx * shift), clength * scale, 1) \<and>
       s5 = s4"
    using composition_fri fl_empty
    unfolding ro_receive_query_commits_def by simp
  have final_eq:
      "cp_eval as fv (h ^ ?idx * shift) = final"
  proof (rule ccontr)
    assume "\<not> cp_eval as fv (h ^ ?idx * shift) = final"
    then have "Some ((), t) \<in> set_dist (execute throw s4)"
      using composition_assert comp_out unfolding assert_def by simp
    then show False
      by (simp add: throw_no_outcome)
  qed
  have t_eq: "t = s5"
    using composition_assert comp_out final_eq
    unfolding assert_def by simp
  have s2_t: "s2 \<le> t"
    using s2_s3 s4_eq comp_out t_eq by simp
  have trace_table_t:
      "partial_authenticated_table fr (scale * clength)
        trace_openings t"
    by (rule partial_authenticated_table_mono[OF trace_table_s2 s2_t])
  have final_eq':
      "cp_eval as (map opening_value trace_openings) (h ^ ?idx * shift) =
        final"
    using final_eq trace_values by simp
  have challenge_lookup_s1:
      "fmlookup (HashMap s1)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF challenge] by simp
  have s1_s2: "s1 \<le> s2"
    using ro_check_decommit_on_query_outcome_with_lookup_chain[OF decommit]
    by blast
  have s1_t: "s1 \<le> t"
    by (rule hash_ext_trans[OF s1_s2 s2_t])
  have lookup_t:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF challenge_lookup_s1 s1_t])
  show ?thesis
    by (rule that[OF refl lookup_t trace_indices trace_table_t final_eq'])
qed

lemma ro_verifier_query_round_program_authenticated_openings_consistent_with_lookup:
  fixes s t :: "'f protocol_channel"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (ro_verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx trace_openings composition_openings where
    "idx = index (to_nat raw)"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    "partial_query_openings_consistent trace_openings composition_openings
      as idx"
proof -
  from outcome obtain raw s1 fv s2 f_i f_x f_len f_pow s3 s4
      i x len pw s5 where
    challenge:
      "Some (raw, s1) \<in> set_dist (execute receive_query_index_challenge s)"
    and decommit:
      "Some (fv, s2) \<in>
        set_dist
          (execute
            (mmap (ro_check_decommit_on_query fr (index (to_nat raw)))) s1)"
    and trace_fri:
      "Some ((f_i, f_x, f_len, f_pow), s3) \<in>
        set_dist
          (execute
            (mfold (index (to_nat raw), hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl)) s2)"
    and trace_assert:
      "Some ((), s4) \<in> set_dist (execute (assert (f_x = f_final)) s3)"
    and composition_fri:
      "Some ((i, x, len, pw), s5) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat raw),
                cp_eval as fv (h ^ index (to_nat raw) * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl)) s4)"
    and composition_assert:
      "Some ((), t) \<in> set_dist (execute (assert (x = final)) s5)"
    unfolding ro_verifier_query_round_program_def
    by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)
  let ?idx = "index (to_nat raw)"
  have idx_sample: "?idx \<in> query_sample_space"
    using index_less_query_sample_space
    unfolding query_sample_space_def by simp
  from ro_check_decommit_on_query_authenticated_openings[
      OF idx_sample decommit]
  obtain trace_openings where
    trace_values: "map opening_value trace_openings = fv"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled ?idx"
    and trace_table_s2:
      "partial_authenticated_table fr (scale * clength)
        trace_openings s2"
    by blast
  have domain_pos: "0 < clength * scale"
    using eval_domain_nontrivial by linarith
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  from mfold_ro_receive_query_commits_first_partial_authenticated_table[
      OF fl_eq domain_pos idx_bound composition_fri]
  obtain composition_openings where
    composition_table_s5:
      "partial_authenticated_table composition_root (clength * scale)
        composition_openings s5"
    and composition_indices0:
      "map opening_index composition_openings =
        [?idx, (?idx + (clength * scale) div 2) mod (clength * scale)]"
    and composition_len: "length composition_openings = 2"
    and composition_value:
      "opening_value (composition_openings ! 0) =
        cp_eval as fv (h ^ ?idx * shift)"
    by blast
  have s2_s3: "s2 \<le> s3"
    using ro_receive_query_commits_outcome_extends_counter[OF trace_fri]
    by blast
  have s4_eq: "s4 = s3"
    using trace_assert unfolding assert_def
    by (cases "f_x = f_final") (auto simp: throw_no_outcome)
  have s4_s5: "s4 \<le> s5"
    using ro_receive_query_commits_outcome_extends_counter[
      OF composition_fri]
    by blast
  have t_eq: "t = s5"
    using composition_assert unfolding assert_def
    by (cases "x = final") (auto simp: throw_no_outcome)
  have s2_t: "s2 \<le> t"
    using s2_s3 s4_s5 unfolding s4_eq t_eq
    by (rule hash_ext_trans)
  have trace_table_t:
      "partial_authenticated_table fr (scale * clength)
        trace_openings t"
    by (rule partial_authenticated_table_mono[OF trace_table_s2 s2_t])
  have composition_table_t:
      "partial_authenticated_table composition_root (scale * clength)
        composition_openings t"
    using composition_table_s5 unfolding t_eq
    by (simp add: mult.commute)
  have composition_indices:
      "map opening_index composition_openings =
        [?idx, fri_sibling_index (scale * clength) ?idx]"
    using composition_indices0
    unfolding fri_sibling_index_def
    by (simp add: mult.commute)
  have consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        as ?idx"
    by (rule partial_query_openings_consistentI[
          OF idx_sample trace_indices composition_indices])
      (use composition_value trace_values in simp)
  have challenge_lookup_s1:
      "fmlookup (HashMap s1)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF challenge] by simp
  have s1_s2: "s1 \<le> s2"
    using ro_check_decommit_on_query_outcome_with_lookup_chain[OF decommit]
    by blast
  have s1_t: "s1 \<le> t"
    by (rule hash_ext_trans[OF s1_s2 s2_t])
  have lookup_t:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF challenge_lookup_s1 s1_t])
  show ?thesis
    by (rule that[OF refl lookup_t trace_indices trace_table_t
          composition_table_t composition_indices consistent])
qed
definition ro_composition_query_round_evidence
where
  "ro_composition_query_round_evidence fr as fl final idx
      trace_openings composition_openings final_state \<longleftrightarrow>
    idx \<in> query_sample_space \<and>
    map opening_index trace_openings = powers_scaled idx \<and>
    partial_authenticated_table fr (scale * clength)
      trace_openings final_state \<and>
    (if fl = []
     then composition_openings = [] \<and>
       cp_eval as (map opening_value trace_openings)
         (h ^ idx * shift) = final
     else
       map opening_index composition_openings =
         [idx, fri_sibling_index (scale * clength) idx] \<and>
       partial_authenticated_table (snd (hd fl)) (scale * clength)
         composition_openings final_state \<and>
       partial_query_openings_consistent trace_openings
         composition_openings as idx)"

lemma
  partial_query_openings_consistent_imp_query_consistent_at_if_tables_agree:
  assumes consistent:
      "partial_query_openings_consistent trace_openings composition_openings
        as idx"
    and trace_agrees:
      "table_agrees_with_authenticated_openings trace_table
        (scale * clength) trace_openings"
    and composition_agrees:
      "table_agrees_with_authenticated_openings composition_table
        (scale * clength) composition_openings"
  shows "query_consistent_at trace_table composition_table as idx"
proof -
  have idx_sample: "idx \<in> query_sample_space"
    using consistent
    unfolding partial_query_openings_consistent_def by simp
  have trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    using consistent
    unfolding partial_query_openings_consistent_def by simp
  have composition_indices:
      "map opening_index composition_openings =
        [idx, fri_sibling_index (scale * clength) idx]"
    using consistent
    unfolding partial_query_openings_consistent_def by simp
  have opened_value:
      "opening_value (composition_openings ! 0) =
        cp_eval as (map opening_value trace_openings)
          (h ^ idx * shift)"
    using consistent
    unfolding partial_query_openings_consistent_def by simp
  have trace_len: "length trace_table = scale * clength"
    using trace_agrees
    unfolding table_agrees_with_authenticated_openings_def by simp
  have composition_len: "length composition_table = scale * clength"
    using composition_agrees
    unfolding table_agrees_with_authenticated_openings_def by simp
  have trace_values:
      "map ((!) trace_table) (powers_scaled idx) =
        map opening_value trace_openings"
    by (rule table_agrees_with_authenticated_openings_values[
          OF trace_agrees trace_indices])
  have composition_openings_len: "length composition_openings = 2"
    using arg_cong[OF composition_indices, of length] by simp
  have composition_head_in:
      "composition_openings ! 0 \<in> set composition_openings"
    by (rule nth_mem) (use composition_openings_len in simp)
  have composition_head_index:
      "opening_index (composition_openings ! 0) = idx"
  proof -
    have "map opening_index composition_openings ! 0 = idx"
      using composition_indices by simp
    then show ?thesis
      using composition_openings_len by simp
  qed
  have composition_value:
      "composition_table ! idx =
        opening_value (composition_openings ! 0)"
    using composition_agrees composition_head_in composition_head_index
    unfolding table_agrees_with_authenticated_openings_def by auto
  have idx_domain: "idx < clength * scale"
    by (rule query_sample_space_less_domain[OF idx_sample])
  have powers_bound:
      "\<forall>j \<in> set (powers_scaled idx). j < length trace_table"
    using query_sample_space_powers_scaled_bound[OF idx_sample] trace_len
    by (simp add: mult.commute)
  show ?thesis
    unfolding query_consistent_at_def
    using idx_domain trace_len composition_len powers_bound trace_values
      composition_value opened_value
    by (simp add: mult.commute)
qed

lemma
  ro_composition_query_round_evidence_prefix_conceptual_consistency_or_targets:
  fixes prefix_state query_start final_state :: "'f protocol_channel"
  assumes prefix_ext: "prefix_state \<le> final_state"
    and query_ext: "query_start \<le> final_state"
    and clean: "\<not> hash_map_output_collision final_state"
    and evidence:
      "ro_composition_query_round_evidence fr as fl final idx
        trace_openings composition_openings final_state"
  shows
    "query_consistent_at
       (conceptual_table prefix_state fr (scale * clength))
       (if fl = []
        then replicate (scale * clength) final
        else conceptual_table query_start (snd (hd fl))
          (scale * clength))
       as idx \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {fr} prefix_state)
       prefix_state final_state \<or>
     (fl \<noteq> [] \<and>
       hash_map_new_output_hit
         (merkle_prefix_path_targets {snd (hd fl)} query_start)
         query_start final_state)"
proof -
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_ext])
    then show False
      using clean by contradiction
  qed
  have query_clean: "\<not> hash_map_output_collision query_start"
  proof
    assume collision: "hash_map_output_collision query_start"
    have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[OF collision query_ext])
    then show False
      using clean by contradiction
  qed
  show ?thesis
  proof (cases fl)
    case Nil
    have idx_sample: "idx \<in> query_sample_space"
      and trace_indices:
        "map opening_index trace_openings = powers_scaled idx"
      and trace_partial:
        "partial_authenticated_table fr (scale * clength)
          trace_openings final_state"
      and final_eq:
        "cp_eval as (map opening_value trace_openings)
          (h ^ idx * shift) = final"
      using evidence Nil
      unfolding ro_composition_query_round_evidence_def by simp_all
    from
      partial_authenticated_table_agrees_with_prefix_conceptual_table_or_prefix_target_hit[
        OF prefix_ext prefix_clean trace_partial]
    show ?thesis
    proof
      assume trace_agrees:
          "table_agrees_with_authenticated_openings
            (conceptual_table prefix_state fr (scale * clength))
            (scale * clength) trace_openings"
      have trace_values:
          "map ((!) (conceptual_table prefix_state fr (scale * clength)))
              (powers_scaled idx) =
            map opening_value trace_openings"
        by (rule table_agrees_with_authenticated_openings_values[
              OF trace_agrees trace_indices])
      have idx_domain: "idx < clength * scale"
        by (rule query_sample_space_less_domain[OF idx_sample])
      have powers_bound:
          "\<forall>j \<in> set (powers_scaled idx).
            j < length
              (conceptual_table prefix_state fr (scale * clength))"
        using query_sample_space_powers_scaled_bound[OF idx_sample]
        by (simp add: mult.commute)
      have consistent:
          "query_consistent_at
            (conceptual_table prefix_state fr (scale * clength))
            (replicate (scale * clength) final) as idx"
        unfolding query_consistent_at_def
        using idx_domain powers_bound trace_values final_eq
        by (simp add: mult.commute)
      show ?thesis
        using consistent Nil by simp
    next
      assume target:
          "hash_map_new_output_hit
            (merkle_prefix_path_targets {fr} prefix_state)
            prefix_state final_state"
      then show ?thesis by simp
    qed
  next
    case (Cons a fl_tail)
    obtain b composition_root where a_eq: "a = (b, composition_root)"
      by (cases a)
    have fl_eq: "fl = (b, composition_root) # fl_tail"
      using Cons a_eq by simp
    have trace_partial:
        "partial_authenticated_table fr (scale * clength)
          trace_openings final_state"
      and composition_partial:
        "partial_authenticated_table composition_root (scale * clength)
          composition_openings final_state"
      and consistent:
        "partial_query_openings_consistent trace_openings
          composition_openings as idx"
      using evidence fl_eq
      unfolding ro_composition_query_round_evidence_def by simp_all
    from
      partial_authenticated_table_agrees_with_prefix_conceptual_table_or_prefix_target_hit[
        OF prefix_ext prefix_clean trace_partial]
    show ?thesis
    proof
      assume trace_agrees:
          "table_agrees_with_authenticated_openings
            (conceptual_table prefix_state fr (scale * clength))
            (scale * clength) trace_openings"
      from
        partial_authenticated_table_agrees_with_prefix_conceptual_table_or_prefix_target_hit[
          OF query_ext query_clean composition_partial]
      show ?thesis
      proof
        assume composition_agrees:
            "table_agrees_with_authenticated_openings
              (conceptual_table query_start composition_root
                (scale * clength))
              (scale * clength) composition_openings"
        have conceptual_consistent:
            "query_consistent_at
              (conceptual_table prefix_state fr (scale * clength))
              (conceptual_table query_start composition_root
                (scale * clength))
              as idx"
          by (rule
              partial_query_openings_consistent_imp_query_consistent_at_if_tables_agree[
                OF consistent trace_agrees composition_agrees])
        show ?thesis
          using conceptual_consistent fl_eq by simp
      next
        assume target:
            "hash_map_new_output_hit
              (merkle_prefix_path_targets {composition_root} query_start)
              query_start final_state"
        show ?thesis
          using target fl_eq by simp
      qed
    next
      assume target:
          "hash_map_new_output_hit
            (merkle_prefix_path_targets {fr} prefix_state)
            prefix_state final_state"
      then show ?thesis by simp
    qed
  qed
qed

lemma ro_composition_query_round_evidence_mono:
  assumes evidence:
      "ro_composition_query_round_evidence fr as fl final idx
        trace_openings composition_openings s"
    and ext: "s \<le> t"
  shows
      "ro_composition_query_round_evidence fr as fl final idx
        trace_openings composition_openings t"
  using evidence
  unfolding ro_composition_query_round_evidence_def
  by (cases fl)
    (auto intro: partial_authenticated_table_mono[OF _ ext])

lemma ro_verifier_query_round_program_composition_query_evidence_with_lookup:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (ro_verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx trace_openings composition_openings where
    "idx = index (to_nat raw)"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    "ro_composition_query_round_evidence fr as fl final idx
      trace_openings composition_openings t"
proof (cases fl)
  case Nil
  from ro_verifier_query_round_program_empty_composition_consistent_with_lookup[
      OF Nil outcome]
  obtain raw idx trace_openings where
    idx_eq: "idx = index (to_nat raw)"
    and lookup:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and trace_table:
      "partial_authenticated_table fr (scale * clength) trace_openings t"
    and final_eq:
      "cp_eval as (map opening_value trace_openings) (h ^ idx * shift) =
        final"
    .
  have idx_sample: "idx \<in> query_sample_space"
    using idx_eq index_less_query_sample_space
    unfolding query_sample_space_def by simp
  have evidence:
      "ro_composition_query_round_evidence fr as fl final idx
        trace_openings [] t"
    using idx_sample trace_indices trace_table final_eq Nil
    unfolding ro_composition_query_round_evidence_def by simp
  show ?thesis
    by (rule that[OF idx_eq lookup evidence])
next
  case (Cons a fl_tail)
  obtain b composition_root where a_eq: "a = (b, composition_root)"
    by (cases a)
  have fl_eq: "fl = (b, composition_root) # fl_tail"
    using Cons a_eq by simp
  from ro_verifier_query_round_program_authenticated_openings_consistent_with_lookup[
      OF fl_eq outcome]
  obtain raw idx trace_openings composition_openings where
    idx_eq: "idx = index (to_nat raw)"
    and lookup:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and trace_table:
      "partial_authenticated_table fr (scale * clength) trace_openings t"
    and composition_table:
      "partial_authenticated_table composition_root (scale * clength)
        composition_openings t"
    and composition_indices:
      "map opening_index composition_openings =
        [idx, fri_sibling_index (scale * clength) idx]"
    and consistent:
      "partial_query_openings_consistent trace_openings
        composition_openings as idx"
    .
  have idx_sample: "idx \<in> query_sample_space"
    using consistent
    unfolding partial_query_openings_consistent_def by simp
  have evidence:
      "ro_composition_query_round_evidence fr as fl final idx
        trace_openings composition_openings t"
    using idx_sample trace_indices trace_table composition_table
      composition_indices consistent fl_eq
    unfolding ro_composition_query_round_evidence_def by simp
  show ?thesis
    by (rule that[OF idx_eq lookup evidence])
qed

lemma
  ro_recorded_query_fri_accepted_evidence_composition_query_round_evidence:
  fixes final_state :: "'f protocol_channel"
  assumes accepted:
      "ro_recorded_query_fri_accepted_evidence
        fr f_fl f_final as fl final raw trace_layers composition_layers
        final_state"
  obtains trace_openings composition_openings where
    "ro_composition_query_round_evidence fr as fl final
      (index (to_nat raw)) trace_openings composition_openings final_state"
proof -
  from accepted
  obtain round_state round_final fv s0 s1 trace_chunk
      f_i f_len f_pow s2 composition_chunk c_i c_len c_pow where
    round_out:
      "Some ((), round_final) \<in>
        set_dist
          (execute
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            round_state)"
    and final_ext: "round_final \<le> final_state"
    and trace_shape:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layers trace_chunk"
    and composition_shape:
      "fri_layers_transcript (length fl) (clength * scale)
        composition_layers composition_chunk"
    and raw_challenge:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge round_state)"
    and query_decommit:
      "Some (fv, s1) \<in>
        set_dist
          (execute
            (mmap (ro_check_decommit_on_query fr (index (to_nat raw))))
            s0)"
    and trace_fri:
      "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat raw), hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl))
            s1)"
    and composition_fri:
      "Some ((c_i, final, c_len, c_pow), round_final) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat raw),
                cp_eval as fv (h ^ index (to_nat raw) * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl))
            s2)"
    unfolding ro_recorded_query_fri_accepted_evidence_def
    by blast
  have s0_s1: "s0 \<le> s1"
    using ro_check_decommit_on_query_outcome_with_lookup_chain[
      OF query_decommit]
    by blast
  have s1_s2: "s1 \<le> s2"
    using ro_receive_query_commits_outcome_extends_counter[OF trace_fri]
    by blast
  have s2_round: "s2 \<le> round_final"
    using ro_receive_query_commits_outcome_extends_counter[
      OF composition_fri]
    by blast
  have s0_round: "s0 \<le> round_final"
    by (rule hash_ext_trans[OF s0_s1])
      (rule hash_ext_trans[OF s1_s2 s2_round])
  have recorded_lookup_s0:
      "fmlookup (HashMap s0)
        (QueryIndexChallenge
          (PQueryCounter round_state) (PState round_state)) = Some raw"
    using receive_query_index_challenge_outcome[OF raw_challenge] by simp
  have recorded_lookup_round:
      "fmlookup (HashMap round_final)
        (QueryIndexChallenge
          (PQueryCounter round_state) (PState round_state)) = Some raw"
    by (rule hash_extension_lookup[OF recorded_lookup_s0 s0_round])
  from
    ro_verifier_query_round_program_composition_query_evidence_with_lookup[
      OF round_out]
  obtain auth_raw idx trace_openings composition_openings where
    idx_eq: "idx = index (to_nat auth_raw)"
    and auth_lookup:
      "fmlookup (HashMap round_final)
        (QueryIndexChallenge
          (PQueryCounter round_state) (PState round_state)) = Some auth_raw"
    and evidence_round:
      "ro_composition_query_round_evidence fr as fl final idx
        trace_openings composition_openings round_final"
    .
  have auth_raw_eq: "auth_raw = raw"
    using auth_lookup recorded_lookup_round by simp
  have evidence_final:
      "ro_composition_query_round_evidence fr as fl final idx
        trace_openings composition_openings final_state"
    by (rule ro_composition_query_round_evidence_mono[
          OF evidence_round final_ext])
  have evidence_final':
      "ro_composition_query_round_evidence fr as fl final
        (index (to_nat raw)) trace_openings composition_openings final_state"
    using evidence_final idx_eq auth_raw_eq by simp
  show ?thesis
    by (rule that[OF evidence_final'])
qed

lemma
  ro_absorb_checked_staged_first_root_actual_query_composition_query_round_evidence:
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
  obtains f_fl fl fr f_final as final trace_openings_at
      composition_openings_at where
    "fr = staged_trace_root data"
    "query_start \<le> final_state"
    "prefix_state \<le> final_state"
    "map fst f_fl = staged_trace_fri_challenges data"
    "map snd f_fl = staged_trace_fri_roots data"
    "f_final = staged_trace_final data"
    "as = staged_alphas data"
    "map fst fl = staged_composition_fri_challenges data"
    "map snd fl = staged_composition_fri_roots data"
    "final = staged_composition_final data"
    "f_fl \<noteq> []"
    "to_nat (staged_degree data) \<le> maxDegree"
    "\<forall>j < length raws.
      ro_composition_query_round_evidence fr as fl final
        (index (to_nat (raws ! j))) (trace_openings_at j)
        (composition_openings_at j) final_state"
proof -
  from ro_absorb_checked_staged_first_root_actual_query_accepted_evidence[
      OF wf controlled nonempty builder_out verifier_out clean]
  obtain f_fl fl fr f_final as final trace_round_layers
      composition_round_layers where
    fr_eq: "fr = staged_trace_root data"
    and query_start_final: "query_start \<le> final_state"
    and prefix_state_final: "prefix_state \<le> final_state"
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
    and composition_final_eq: "final = staged_composition_final data"
    and f_fl_nonempty: "f_fl \<noteq> []"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and accepted:
      "\<forall>j < length raws.
        ro_recorded_query_fri_accepted_evidence
          fr f_fl f_final as fl final (raws ! j)
          (trace_round_layers ! j) (composition_round_layers ! j)
          final_state"
    .
  have each:
      "\<forall>j. \<exists>p.
        j < length raws \<longrightarrow>
          ro_composition_query_round_evidence fr as fl final
            (index (to_nat (raws ! j))) (fst p) (snd p) final_state"
  proof
    fix j
    show
      "\<exists>p.
        j < length raws \<longrightarrow>
          ro_composition_query_round_evidence fr as fl final
            (index (to_nat (raws ! j))) (fst p) (snd p) final_state"
    proof (cases "j < length raws")
      case True
      from
        ro_recorded_query_fri_accepted_evidence_composition_query_round_evidence[
          OF accepted[rule_format, OF True]]
      obtain trace_openings composition_openings where
        evidence:
          "ro_composition_query_round_evidence fr as fl final
            (index (to_nat (raws ! j))) trace_openings
            composition_openings final_state"
        .
      show ?thesis
        by (intro exI[of _ "(trace_openings, composition_openings)"])
          (use evidence in simp)
    next
      case False
      show ?thesis
        by (intro exI[of _ "([], [])"]) (use False in simp)
    qed
  qed
  from choice[OF each]
  obtain pair_at where pair_at:
      "\<forall>j. j < length raws \<longrightarrow>
        ro_composition_query_round_evidence fr as fl final
          (index (to_nat (raws ! j))) (fst (pair_at j))
          (snd (pair_at j)) final_state"
    by blast
  show ?thesis
    by (rule that[
          OF fr_eq query_start_final prefix_state_final
            trace_challenges_eq trace_roots_eq trace_final_eq alphas_eq
            composition_challenges_eq composition_roots_eq
            composition_final_eq f_fl_nonempty
            degree_bound])
      (use pair_at in simp)
qed

lemma
  ro_absorb_checked_staged_first_root_actual_query_conceptual_consistency_or_targets:
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
  shows
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
  proof -
  from
    ro_absorb_checked_staged_first_root_actual_query_composition_query_round_evidence[
      OF wf controlled nonempty builder_out verifier_out clean]
  obtain f_fl fl fr f_final as final trace_openings_at
      composition_openings_at where
    fr_eq: "fr = staged_trace_root data"
    and query_ext: "query_start \<le> final_state"
    and prefix_ext: "prefix_state \<le> final_state"
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
    and composition_final_eq: "final = staged_composition_final data"
    and f_fl_nonempty: "f_fl \<noteq> []"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and evidence:
      "\<forall>j < length raws.
        ro_composition_query_round_evidence fr as fl final
          (index (to_nat (raws ! j))) (trace_openings_at j)
          (composition_openings_at j) final_state"
    .

  from ro_checked_staged_transcript_program_with_first_root_outcomeE[
      OF builder_out]
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
  obtain prefix_fr prefix_trace_bs first_root where
    prefix_eq: "prefix = (prefix_fr, prefix_trace_bs, first_root)"
    by (cases prefix) auto
  have prefix_props:
      "prefix_trace_bs = [] \<and> prefix_state = prefix_final"
    using ro_staged_first_trace_fri_root_prefix_program_chain[
      OF wf controlled nonempty prefix_out[unfolded prefix_eq]]
    by blast
  have prefix_eq': "prefix = (prefix_fr, [], first_root)"
    using prefix_eq prefix_props by simp
  have after_fields:
      "staged_trace_root head_data = prefix_fr \<and>
       (\<exists>roots. staged_trace_fri_roots head_data = first_root # roots)"
    by (rule ro_checked_staged_after_first_trace_fri_root_prefix_program_fields[
          OF nonempty])
      (use after_out prefix_eq in simp)
  have fr_prefix: "fr = prefix_fr"
    using fr_eq after_fields data_eq by simp
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_ext])
    then show False using clean by contradiction
  qed

  have each:
      "\<forall>j < length raws.
        query_consistent_at
          (conceptual_table prefix_state fr (scale * clength))
          (if fl = []
           then replicate (scale * clength) final
           else conceptual_table query_start (snd (hd fl))
             (scale * clength))
          as (index (to_nat (raws ! j))) \<or>
        hash_map_new_output_hit
          (merkle_prefix_path_targets {fr} prefix_state)
          prefix_state final_state \<or>
        (fl \<noteq> [] \<and>
          hash_map_new_output_hit
            (merkle_prefix_path_targets {snd (hd fl)} query_start)
            query_start final_state)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length raws"
    show
      "query_consistent_at
        (conceptual_table prefix_state fr (scale * clength))
        (if fl = []
         then replicate (scale * clength) final
         else conceptual_table query_start (snd (hd fl))
           (scale * clength))
        as (index (to_nat (raws ! j))) \<or>
       hash_map_new_output_hit
        (merkle_prefix_path_targets {fr} prefix_state)
        prefix_state final_state \<or>
       (fl \<noteq> [] \<and>
        hash_map_new_output_hit
          (merkle_prefix_path_targets {snd (hd fl)} query_start)
          query_start final_state)"
      by (rule
          ro_composition_query_round_evidence_prefix_conceptual_consistency_or_targets[
            OF prefix_ext query_ext clean evidence[rule_format, OF j_bound]])
  qed

  have trace_singleton_imp_target:
      "hash_map_new_output_hit
          (merkle_prefix_path_targets {fr} prefix_state)
          prefix_state final_state \<Longrightarrow>
        hash_map_new_output_hit
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
          prefix_state final_state"
  proof -
    assume singleton:
      "hash_map_new_output_hit
        (merkle_prefix_path_targets {fr} prefix_state)
        prefix_state final_state"
    have target_subset:
        "merkle_prefix_path_targets {fr} prefix_state \<subseteq>
          merkle_prefix_path_targets {prefix_fr, first_root} prefix_state"
      by (rule merkle_prefix_path_targets_mono)
        (use fr_prefix in auto)
    have broad:
        "hash_map_new_output_hit
          (merkle_prefix_path_targets {prefix_fr, first_root} prefix_state)
          prefix_state final_state"
      by (rule hash_map_new_output_hit_subset[OF target_subset singleton])
    show
      "hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state"
      using broad prefix_clean
      unfolding prefix_eq' first_trace_fri_root_prefix_merkle_targets_def
      by simp
  qed

  have composition_singleton_imp_target:
      "fl \<noteq> [] \<Longrightarrow>
        hash_map_new_output_hit
          (merkle_prefix_path_targets {snd (hd fl)} query_start)
          query_start final_state \<Longrightarrow>
        hash_map_new_output_hit
          (ro_actual_query_composition_prefix_targets data query_start)
          query_start final_state"
  proof -
    assume fl_nonempty: "fl \<noteq> []"
      and singleton:
        "hash_map_new_output_hit
          (merkle_prefix_path_targets {snd (hd fl)} query_start)
          query_start final_state"
    have roots_nonempty: "staged_composition_fri_roots data \<noteq> []"
      using composition_roots_eq fl_nonempty by auto
    have root_eq:
        "snd (hd fl) = hd (staged_composition_fri_roots data)"
      using arg_cong[OF composition_roots_eq, of hd] fl_nonempty
      by (cases fl) simp_all
    show
      "hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets data query_start)
        query_start final_state"
      using singleton roots_nonempty root_eq
      unfolding ro_actual_query_composition_prefix_targets_def
      by simp
  qed

  have candidate_eq:
      "(if fl = []
        then replicate (scale * clength) final
        else conceptual_table query_start (snd (hd fl))
          (scale * clength)) =
       ro_actual_query_composition_candidate data query_start"
  proof (cases fl)
    case Nil
    then show ?thesis
      using composition_roots_eq composition_final_eq
      unfolding ro_actual_query_composition_candidate_def
      by simp
  next
    case (Cons a fl_tail)
    have roots_eq:
        "staged_composition_fri_roots data = snd a # map snd fl_tail"
      using composition_roots_eq Cons by simp
    show ?thesis
      using Cons roots_eq
      unfolding ro_actual_query_composition_candidate_def
      by simp
  qed

  show ?thesis
  proof (cases
      "hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state")
    case True
    then show ?thesis by simp
  next
    case no_trace_target: False
    have no_trace_singleton:
        "\<not> hash_map_new_output_hit
          (merkle_prefix_path_targets {fr} prefix_state)
          prefix_state final_state"
      using trace_singleton_imp_target no_trace_target by blast
    show ?thesis
    proof (cases
        "hash_map_new_output_hit
          (ro_actual_query_composition_prefix_targets data query_start)
          query_start final_state")
      case True
      then show ?thesis by simp
    next
      case no_composition_target: False
      have no_composition_singleton:
          "\<not> (fl \<noteq> [] \<and>
            hash_map_new_output_hit
              (merkle_prefix_path_targets {snd (hd fl)} query_start)
              query_start final_state)"
        using composition_singleton_imp_target no_composition_target by blast
      have consistent:
          "\<forall>j < length raws.
            query_consistent_at
              (conceptual_table prefix_state fr (scale * clength))
              (if fl = []
               then replicate (scale * clength) final
               else conceptual_table query_start (snd (hd fl))
                 (scale * clength))
              as (index (to_nat (raws ! j)))"
        using each no_trace_singleton no_composition_singleton by blast
      have consistent':
          "\<forall>j < length raws.
            query_consistent_at
              (conceptual_table prefix_state (staged_trace_root data)
                (scale * clength))
              (ro_actual_query_composition_candidate data query_start)
              (staged_alphas data) (index (to_nat (raws ! j)))"
        using consistent fr_eq alphas_eq candidate_eq by simp
      then show ?thesis by simp
    qed
  qed
qed


definition
  ro_absorb_checked_staged_security_with_first_root_composition_not_low_degree
where
  "ro_absorb_checked_staged_security_with_first_root_composition_not_low_degree
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        \<not> composition_table_low_degree maxDegree
          (ro_actual_query_composition_candidate data query_start))"

lemma
  ro_absorb_checked_staged_security_with_first_root_clean_composition_not_low_degree_collapsed:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_nonempty: "0 < ceil_log clength"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_absorb_checked_staged_security_experiment_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and composition_bad:
      "ro_absorb_checked_staged_security_with_first_root_composition_not_low_degree
        out"
    and clean: "\<not> final_hash_collision_event out"
  shows
    "ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
       out"
proof -
  from composition_bad obtain full where out_eq: "out = Some full"
    unfolding
      ro_absorb_checked_staged_security_with_first_root_composition_not_low_degree_def
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
      "\<not> composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate data query_start)"
    using composition_bad
    unfolding out_eq full_eq
      ro_absorb_checked_staged_security_with_first_root_composition_not_low_degree_def
    by simp
  have composition_nonempty:
      "staged_composition_fri_roots data \<noteq> []"
  proof
    assume empty: "staged_composition_fri_roots data = []"
    have low:
        "composition_table_low_degree maxDegree
          (ro_actual_query_composition_candidate data query_start)"
      by (rule
          ro_actual_query_composition_candidate_zero_round_low_degree[
            OF empty])
    show False using candidate_bad low by contradiction
  qed
  from
    ro_absorb_checked_staged_first_root_actual_query_composition_not_low_degree_obstruction_collapsed[
      OF wf controlled trace_nonempty builder_out verifier_out final_clean
        composition_nonempty candidate_bad]
  obtain fl final composition_round_layers where
    composition_challenges_eq:
      "map fst fl = staged_composition_fri_challenges data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and obstruction:
      "generic_fri_sampled_query_candidate_evidence
         (composition_table_low_degree (to_nat (staged_degree data)))
         (Not \<circ>
           composition_table_low_degree (to_nat (staged_degree data)))
         (ro_actual_query_composition_candidate data query_start)
         (to_nat (staged_degree data))
         (map snd fl) (map fst fl) final
         (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers
         (generic_fri_sampled_assignment_layers
           (ro_actual_query_composition_candidate data query_start)
           (map snd fl) (map fst fl) final
           (map (\<lambda>raw. index (to_nat raw)) raws)
           composition_round_layers) \<or>
       hash_map_new_output_hit
         (ro_actual_query_composition_prefix_targets data query_start)
         query_start final_state \<or>
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
      "generic_fri_sampled_query_candidate_evidence
         (composition_table_low_degree (to_nat (staged_degree data)))
         (Not \<circ>
           composition_table_low_degree (to_nat (staged_degree data)))
         (ro_actual_query_composition_candidate data query_start)
         (to_nat (staged_degree data))
         (map snd fl) (map fst fl) final
         (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers
         (generic_fri_sampled_assignment_layers
           (ro_actual_query_composition_candidate data query_start)
           (map snd fl) (map fst fl) final
           (map (\<lambda>raw. index (to_nat raw)) raws)
           composition_round_layers) \<or>
       hash_map_new_output_hit
         (ro_actual_query_composition_prefix_targets data query_start)
         query_start final_state"
    by blast
  then show ?thesis
  proof
    assume sampled:
      "generic_fri_sampled_query_candidate_evidence
         (composition_table_low_degree (to_nat (staged_degree data)))
         (Not \<circ>
           composition_table_low_degree (to_nat (staged_degree data)))
         (ro_actual_query_composition_candidate data query_start)
         (to_nat (staged_degree data))
         (map snd fl) (map fst fl) final
         (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers
         (generic_fri_sampled_assignment_layers
           (ro_actual_query_composition_candidate data query_start)
           (map snd fl) (map fst fl) final
           (map (\<lambda>raw. index (to_nat raw)) raws)
           composition_round_layers)"
    have sampled_max:
        "generic_fri_sampled_query_candidate_evidence
          (composition_table_low_degree (to_nat (staged_degree data)))
          (Not \<circ> composition_table_low_degree maxDegree)
          (ro_actual_query_composition_candidate data query_start)
          (to_nat (staged_degree data))
          (map snd fl) (map fst fl) final
          (map (\<lambda>raw. index (to_nat raw)) raws)
          composition_round_layers
          (generic_fri_sampled_assignment_layers
            (ro_actual_query_composition_candidate data query_start)
            (map snd fl) (map fst fl) final
            (map (\<lambda>raw. index (to_nat raw)) raws)
            composition_round_layers)"
      using sampled candidate_bad
      unfolding generic_fri_sampled_query_candidate_evidence_def
      by simp
    have pair:
        "(map (\<lambda>raw. index (to_nat raw)) raws, map fst fl) \<in>
          composition_fri_sampled_query_bad_pair_union
            (staged_degree data)"
      using sampled_max
      unfolding composition_fri_sampled_query_bad_pair_union_def
        generic_fri_sampled_query_bad_pair_union_def
        generic_fri_sampled_query_bad_pair_set_def
      by blast    have event_concrete:
        "ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
          (Some
            (((((prefix, prefix_state), data, query_start, raws, query_states),
                attacker_state), result), final_state))"
      unfolding
        ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair_def
      using composition_challenges_eq pair by auto
    show ?thesis
      using event_concrete out_eq full_eq by simp
  next
    assume target:
      "hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets data query_start)
        query_start final_state"
    have event_concrete:
        "ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
          (Some
            (((((prefix, prefix_state), data, query_start, raws, query_states),
                attacker_state), result), final_state))"
      unfolding
        ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
      using target by simp
    show ?thesis
      using event_concrete out_eq full_eq by simp
  qed
qed


lemma
  ro_absorb_checked_staged_security_with_first_root_clean_composition_candidate_classification:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_nonempty: "0 < ceil_log clength"
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
    "(case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        composition_table_low_degree maxDegree
          (ro_actual_query_composition_candidate data query_start)) \<or>
     ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
       out"
proof (cases
    "ro_absorb_checked_staged_security_with_first_root_composition_not_low_degree
      out")
  case True
  then show ?thesis
    using
      ro_absorb_checked_staged_security_with_first_root_clean_composition_not_low_degree_collapsed[
        OF wf controlled trace_nonempty support True clean]
    by simp
next
  case False
  from accepted_out obtain full where out_eq: "out = Some full"
    unfolding accepted_def by (cases out) auto
  obtain prefix prefix_state data query_start raws query_states
      attacker_state result final_state where
    full_eq:
      "full =
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state)"
    by (cases full) (auto split: prod.splits)
  have low:
      "composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate data query_start)"
    using False
    unfolding out_eq full_eq
      ro_absorb_checked_staged_security_with_first_root_composition_not_low_degree_def
    by simp
  show ?thesis
    unfolding out_eq full_eq using low by simp
qed
end
end
