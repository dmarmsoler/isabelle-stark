theory Soundness_FRI_RO_Actual_Query_Zero_Round_Composition_Classification
  imports
    Soundness_FRI_RO_Actual_Query_Zero_Round_Security_Classification
    Soundness_FRI_RO_Actual_Query_Composition_Candidate
begin

text \<open>
  Composition and query-consistency classification for the zero trace-FRI
  branch.  The proof retains the sampled partial openings extracted from the
  query transcript; it never reconstructs a complete committed table.
\<close>

context soundness
begin

lemma ro_absorb_checked_staged_zero_round_actual_query_accepted_evidence:
  fixes final_state :: "'f protocol_channel"
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
  obtains f_fl fl fr f_final as final trace_round_layers
      composition_round_layers where
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
    "f_fl = []"
    "to_nat (staged_degree data) \<le> maxDegree"
    "length trace_round_layers = length raws"
    "length composition_round_layers = length raws"
    "\<forall>j < length raws.
      query_round_fri_layer_transcripts
        (map (\<lambda>raw. index (to_nat raw)) raws ! j)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (staged_query_chunks data ! j)
        (trace_round_layers ! j) (composition_round_layers ! j)"
    "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
    "\<forall>round_idx < length raws.
      ro_recorded_query_fri_accepted_evidence
        fr f_fl f_final as fl final (raws ! round_idx)
        (trace_round_layers ! round_idx)
        (composition_round_layers ! round_idx) final_state"
proof -
  from
    ro_checked_staged_transcript_program_with_first_root_actual_query_generic_partial_evidence_with_transcripts[
      OF wf controlled builder_out, where composition_table="[]"]
  obtain trace_round_layers composition_round_layers where
    trace_layers_len: "length trace_round_layers = length raws"
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
    by blast

  from ro_absorb_checked_staged_zero_round_actual_query_boundary_syncE[
      OF zero wf controlled builder_out verifier_out clean]
  obtain head_data query_chunks f_fl fl verifier_query_state
      fr f_final as final where
    query_out:
      "Some ((raws, query_states, query_chunks), attacker_state) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots head_data)
              (staged_composition_fri_roots head_data)
              query_start 0 rounds)
            query_start)"
    and data_eq:
      "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    and fr_eq: "fr = staged_trace_root data"
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
    and f_fl_empty: "f_fl = []"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and verifier_query_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            verifier_query_state)"
    and prefix_query_ext: "prefix_state \<le> query_start"
    and query_attacker_ext: "query_start \<le> attacker_state"
    and attacker_verifier_ext: "attacker_state \<le> verifier_query_state"
    and verifier_builder_state:
      "PState verifier_query_state = PState query_start"
    and counter_eq:
      "PQueryCounter verifier_query_state = PQueryCounter query_start"
    and verifier_transcript:
      "PTranscript verifier_query_state = List.concat query_chunks @ []"
    and raws_rounds: "length raws = rounds"
    and query_chunks_rounds: "length query_chunks = rounds"
    and raw_bound:
      "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
    .

  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF builder_out])
  have shape:
      "length (staged_composition_fri_roots data) =
          ceil_log (to_nat (staged_degree data) + 1) \<and>
       ceil_log (to_nat (staged_degree data) + 1) \<le>
          ceil_log (maxDegree + 1)"
    using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
    by blast
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have trace_count: "length f_fl \<le> N"
    using f_fl_empty by simp
  have composition_count: "length fl \<le> N"
  proof -
    have max_degree_bound: "maxDegree + 1 \<le> clength * scale"
      using maxDegree_less_eval_domain by linarith
    have ceil_bound: "ceil_log (maxDegree + 1) \<le> N"
      by (rule ceil_log_le_power)
        (use max_degree_bound eval_power in simp)
    have composition_len:
        "length fl = ceil_log (to_nat (staged_degree data) + 1)"
    proof -
      have len_eq:
          "length (map snd fl) =
            length (staged_composition_fri_roots data)"
        by (rule arg_cong[OF composition_roots_eq])
      show ?thesis
        using len_eq shape by simp
    qed
    show ?thesis
      using composition_len shape ceil_bound by linarith
  qed
  have query_bound:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have trace_layers_rounds: "length trace_round_layers = rounds"
    using trace_layers_len raws_rounds by simp
  have composition_layers_rounds:
      "length composition_round_layers = rounds"
    using composition_layers_len raws_rounds by simp
  have layer_transcripts':
      "\<forall>j < rounds.
        query_round_fri_layer_transcripts
          (index (to_nat (raws ! j)))
          (staged_trace_fri_roots head_data)
          (staged_composition_fri_roots head_data)
          (query_chunks ! j)
          (trace_round_layers ! j) (composition_round_layers ! j)"
    using layer_transcripts raws_rounds data_eq by simp

  have accepted_result:
      "verifier_query_state \<le> final_state \<and>
       length raws = rounds \<and>
       length query_states = rounds \<and>
       length query_chunks = rounds \<and>
       (\<forall>j < rounds.
        ro_recorded_query_fri_accepted_evidence
          fr f_fl f_final as fl final (raws ! j)
          (trace_round_layers ! j) (composition_round_layers ! j)
          final_state)"
    by (rule
      ro_checked_staged_query_program_with_witnesses_recorded_fri_accepted_evidence[
        OF eval_power trace_count composition_count controlled query_bound
          query_out attacker_verifier_ext verifier_builder_state counter_eq
          verifier_transcript _ _ verifier_query_out
          trace_layers_rounds composition_layers_rounds layer_transcripts'])
      (use trace_roots_eq composition_roots_eq data_eq in simp_all)
  have accepted:
      "\<forall>round_idx < length raws.
        ro_recorded_query_fri_accepted_evidence
          fr f_fl f_final as fl final (raws ! round_idx)
          (trace_round_layers ! round_idx)
          (composition_round_layers ! round_idx) final_state"
    using accepted_result raws_rounds by simp
  have query_start_final: "query_start \<le> final_state"
    using query_attacker_ext attacker_verifier_ext accepted_result
    by (meson hash_ext_trans)
  have prefix_state_final: "prefix_state \<le> final_state"
    by (rule hash_ext_trans[OF prefix_query_ext query_start_final])

  show ?thesis
    by (rule that[OF fr_eq query_start_final prefix_state_final
          trace_challenges_eq trace_roots_eq trace_final_eq alphas_eq
          composition_challenges_eq composition_roots_eq
          composition_final_eq f_fl_empty degree_bound
          trace_layers_len composition_layers_len layer_transcripts
          raw_bound accepted])
qed

lemma ro_absorb_checked_staged_zero_round_actual_query_composition_evidence:
  fixes composition_table :: "'f list"
    and final_state :: "'f protocol_channel"
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
  obtains f_fl fl fr f_final as final trace_round_layers
      composition_round_layers where
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
    "f_fl = []"
    "to_nat (staged_degree data) \<le> maxDegree"
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat (staged_degree data)))
      composition_table (to_nat (staged_degree data))
      (map snd fl) (map fst fl) final
      (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    "generic_fri_recorded_value_chain_evidence
      (map snd fl) (map fst fl) final
      (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    "generic_fri_recorded_chunks_authenticated
      (map snd fl) (map (\<lambda>raw. index (to_nat raw)) raws)
      composition_round_layers final_state"
    "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
    "\<forall>round_idx < length raws.
      ro_recorded_query_fri_accepted_evidence
        fr f_fl f_final as fl final (raws ! round_idx)
        (trace_round_layers ! round_idx)
        (composition_round_layers ! round_idx) final_state"
proof -
  from ro_absorb_checked_staged_zero_round_actual_query_accepted_evidence[
      OF zero wf controlled builder_out verifier_out clean]
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
    and f_fl_empty: "f_fl = []"
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
  have composition_all_layers:
      "fri_all_round_layer_evidence
        (map snd fl) (map fst fl) ?query_idxs composition_round_layers"
    by (rule
      query_round_fri_layer_transcripts_composition_all_round_layer_evidence[
        OF _ _ layer_transcripts'])
      (use composition_layers_len query_idxs_len in simp_all)

  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF builder_out])
  have shape:
      "length (staged_composition_fri_roots data) =
        ceil_log (to_nat (staged_degree data) + 1)"
    using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
    by blast
  have composition_count:
      "length (map snd fl) =
        fri_round_count_for_degree_bound (to_nat (staged_degree data))"
    using composition_roots_eq shape
    unfolding fri_round_count_for_degree_bound_def
    by simp
  have composition_partial:
      "generic_fri_partial_evidence
        (composition_table_low_degree (to_nat (staged_degree data)))
        composition_table (to_nat (staged_degree data))
        (map snd fl) (map fst fl) final
        ?query_idxs composition_round_layers"
    unfolding generic_fri_partial_evidence_def
    using composition_count composition_all_layers by simp
  have chains:
      "generic_fri_recorded_value_chain_evidence
        (map snd fl) (map fst fl) final
        ?query_idxs composition_round_layers"
    using ro_recorded_query_fri_accepted_evidence_all_value_chains[
      OF trace_layers_len composition_layers_len accepted]
    by simp
  have authenticated:
      "generic_fri_recorded_chunks_authenticated
        (map snd fl) ?query_idxs composition_round_layers final_state"
    using ro_recorded_query_fri_accepted_evidence_all_chunks_authenticated[
      OF trace_layers_len composition_layers_len accepted]
    by simp

  show ?thesis
    by (rule that[OF fr_eq query_start_final prefix_state_final
          trace_challenges_eq trace_roots_eq trace_final_eq alphas_eq
          composition_challenges_eq composition_roots_eq
          composition_final_eq f_fl_empty degree_bound composition_partial
          chains authenticated raw_bound accepted])
qed

lemma
  ro_absorb_checked_staged_zero_round_actual_query_composition_not_low_degree_obstruction_collapsed:
  fixes final_state :: "'f protocol_channel"
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
  from ro_absorb_checked_staged_zero_round_actual_query_composition_evidence[
      OF zero wf controlled builder_out verifier_out clean,
      where composition_table=
        "ro_actual_query_composition_candidate data query_start"]
  obtain f_fl fl fr f_final as final trace_round_layers
      composition_round_layers where
    fr_eq: "fr = staged_trace_root data"
    and trace_challenges_eq:
      "map fst f_fl = staged_trace_fri_challenges data"
    and trace_final_eq: "f_final = staged_trace_final data"
    and alphas_eq: "as = staged_alphas data"
    and f_fl_empty: "f_fl = []"
    and accepted:
      "\<forall>round_idx < length raws.
        ro_recorded_query_fri_accepted_evidence
          fr f_fl f_final as fl final (raws ! round_idx)
          (trace_round_layers ! round_idx)
          (composition_round_layers ! round_idx) final_state"
    and query_start_final: "query_start \<le> final_state"
    and composition_challenges_eq:
      "map fst fl = staged_composition_fri_challenges data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and composition_partial:
      "generic_fri_partial_evidence
        (composition_table_low_degree (to_nat (staged_degree data)))
        (ro_actual_query_composition_candidate data query_start)
        (to_nat (staged_degree data))
        (map snd fl) (map fst fl) final
        (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    and composition_chain:
      "generic_fri_recorded_value_chain_evidence
        (map snd fl) (map fst fl) final
        (map (\<lambda>raw. index (to_nat raw)) raws)
        composition_round_layers"
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
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF builder_out])
  have rounds_bound: "length (map fst fl) \<le> N"
  proof -
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
  have query_start_clean: "\<not> hash_map_output_collision query_start"
  proof
    assume collision: "hash_map_output_collision query_start"
    have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[
            OF collision query_start_final])
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
          OF _ query_start_final query_start_clean
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

lemma
  ro_absorb_checked_staged_security_clean_zero_round_composition_not_low_degree_collapsed:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
        ro_actual_query_composition_candidate_zero_round_low_degree[OF empty])
    show False using candidate_bad low by contradiction
  qed
  from
    ro_absorb_checked_staged_zero_round_actual_query_composition_not_low_degree_obstruction_collapsed[
      OF zero wf controlled builder_out verifier_out final_clean
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
      by blast
    have event_concrete:
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
  ro_absorb_checked_staged_security_clean_zero_round_composition_candidate_classification:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
      ro_absorb_checked_staged_security_clean_zero_round_composition_not_low_degree_collapsed[
        OF zero wf controlled support True clean]
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

lemma
  ro_absorb_checked_staged_zero_round_actual_query_composition_query_round_evidence:
  fixes final_state :: "'f protocol_channel"
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
    "f_fl = []"
    "to_nat (staged_degree data) \<le> maxDegree"
    "\<forall>j < length raws.
      ro_composition_query_round_evidence fr as fl final
        (index (to_nat (raws ! j))) (trace_openings_at j)
        (composition_openings_at j) final_state"
proof -
  from ro_absorb_checked_staged_zero_round_actual_query_accepted_evidence[
      OF zero wf controlled builder_out verifier_out clean]
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
    and f_fl_empty: "f_fl = []"
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
            composition_final_eq f_fl_empty degree_bound])
      (use pair_at in simp)
qed

lemma
  ro_absorb_checked_staged_zero_round_actual_query_conceptual_consistency_or_targets:
  fixes final_state :: "'f protocol_channel"
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
          (ro_actual_query_zero_round_trace_table data prefix_state)
          (ro_actual_query_composition_candidate data query_start)
          (staged_alphas data) (index (to_nat (raws ! j)))) \<or>
     hash_map_new_output_hit
       (ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state)
       prefix_state final_state \<or>
     hash_map_new_output_hit
       (ro_actual_query_composition_prefix_targets data query_start)
       query_start final_state"
proof -
  from
    ro_absorb_checked_staged_zero_round_actual_query_composition_query_round_evidence[
      OF zero wf controlled builder_out verifier_out clean]
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
    and f_fl_empty: "f_fl = []"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and evidence:
      "\<forall>j < length raws.
        ro_composition_query_round_evidence fr as fl final
          (index (to_nat (raws ! j))) (trace_openings_at j)
          (composition_openings_at j) final_state"
    .

  from ro_checked_staged_transcript_program_with_first_root_zero_fields[
      OF zero wf controlled builder_out]
  obtain prefix_fr where
    prefix_eq: "prefix = (prefix_fr, [], prefix_fr)"
    and trace_root_eq: "staged_trace_root data = prefix_fr"
    by blast
  have fr_prefix: "fr = prefix_fr"
    using fr_eq trace_root_eq by simp
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
          (ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state)
          prefix_state final_state"
    using prefix_eq fr_prefix prefix_clean
    unfolding ro_zero_round_first_root_prefix_merkle_targets_def
    by simp
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
        (ro_zero_round_first_root_prefix_merkle_targets prefix prefix_state)
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
              (ro_actual_query_zero_round_trace_table data prefix_state)
              (ro_actual_query_composition_candidate data query_start)
              (staged_alphas data) (index (to_nat (raws ! j)))"
        using consistent fr_eq alphas_eq candidate_eq
        unfolding ro_actual_query_zero_round_trace_table_def
        by simp
      then show ?thesis by simp
    qed
  qed
qed

definition
  ro_actual_query_zero_round_trace_composition_accepted_indices
where
  "ro_actual_query_zero_round_trace_composition_accepted_indices
      data prefix_state query_start =
    query_agreement_indices
      (ro_actual_query_zero_round_trace_table data prefix_state)
      (ro_actual_query_composition_candidate data query_start)
      (staged_alphas data)"

definition
  ro_actual_query_zero_round_trace_composition_accepted_query_lists
where
  "ro_actual_query_zero_round_trace_composition_accepted_query_lists
      data prefix_state query_start =
    query_index_lists_over
      (ro_actual_query_zero_round_trace_composition_accepted_indices
        data prefix_state query_start)"

definition
  ro_actual_query_zero_round_trace_composition_good_query_lists
where
  "ro_actual_query_zero_round_trace_composition_good_query_lists
      data prefix_state query_start =
    (if
      trace_table_low_degree
        (ro_actual_query_zero_round_trace_table data prefix_state) \<and>
      composition_table_low_degree maxDegree
        (ro_actual_query_composition_candidate data query_start) \<and>
      \<not> all_queries_consistent
        (ro_actual_query_zero_round_trace_table data prefix_state)
        (ro_actual_query_composition_candidate data query_start)
        (staged_alphas data)
     then
       ro_actual_query_zero_round_trace_composition_accepted_query_lists
         data prefix_state query_start
     else {})"

lemma
  ro_actual_query_zero_round_trace_composition_accepted_indices_subset:
  "ro_actual_query_zero_round_trace_composition_accepted_indices
      data prefix_state query_start
    \<subseteq> query_sample_space"
  unfolding
    ro_actual_query_zero_round_trace_composition_accepted_indices_def
    query_agreement_indices_def
  by auto

lemma
  ro_actual_query_zero_round_trace_composition_good_query_lists_subset:
  "ro_actual_query_zero_round_trace_composition_good_query_lists
      data prefix_state query_start
    \<subseteq> fri_query_index_list_space"
  unfolding
    ro_actual_query_zero_round_trace_composition_good_query_lists_def
    ro_actual_query_zero_round_trace_composition_accepted_query_lists_def
  using query_index_lists_over_subset_fri_query_index_list_space[
    OF ro_actual_query_zero_round_trace_composition_accepted_indices_subset]
  by auto

lemma
  ro_actual_query_zero_round_trace_composition_good_query_lists_card_bound:
  "card
      (ro_actual_query_zero_round_trace_composition_good_query_lists
        data prefix_state query_start)
    \<le> query_agreement_bound ^ rounds"
proof (cases
    "trace_table_low_degree
       (ro_actual_query_zero_round_trace_table data prefix_state) \<and>
     composition_table_low_degree maxDegree
       (ro_actual_query_composition_candidate data query_start) \<and>
     \<not> all_queries_consistent
       (ro_actual_query_zero_round_trace_table data prefix_state)
       (ro_actual_query_composition_candidate data query_start)
       (staged_alphas data)")
  case True
  have indices_bound:
      "card
        (ro_actual_query_zero_round_trace_composition_accepted_indices
          data prefix_state query_start)
       \<le> query_agreement_bound"
    unfolding
      ro_actual_query_zero_round_trace_composition_accepted_indices_def
    by (rule query_agreement_indices_card_bound)
      (use True in blast)+
  have finite_indices:
      "finite
        (ro_actual_query_zero_round_trace_composition_accepted_indices
          data prefix_state query_start)"
    by (rule finite_subset[
          OF ro_actual_query_zero_round_trace_composition_accepted_indices_subset
            finite_query_sample_space])
  have exact:
      "card
        (ro_actual_query_zero_round_trace_composition_accepted_query_lists
          data prefix_state query_start) =
       card
        (ro_actual_query_zero_round_trace_composition_accepted_indices
          data prefix_state query_start) ^ rounds"
    unfolding
      ro_actual_query_zero_round_trace_composition_accepted_query_lists_def
    by (rule card_query_index_lists_over[OF finite_indices])
  show ?thesis
    unfolding
      ro_actual_query_zero_round_trace_composition_good_query_lists_def
    using True exact power_mono[OF indices_bound, of rounds]
    by simp
next
  case False
  have empty:
      "ro_actual_query_zero_round_trace_composition_good_query_lists
        data prefix_state query_start = {}"
    unfolding
      ro_actual_query_zero_round_trace_composition_good_query_lists_def
    by (simp only: if_False False)
  show ?thesis
    using empty by simp
qed

lemma
  ro_actual_query_zero_round_trace_composition_good_query_lists_relation_fiber_bound:
  "query_index_raw_list_relation_fiber_bound
      (ro_actual_query_zero_round_trace_composition_good_query_lists
        data prefix_state query_start)
    \<le> rounds *
      (query_raw_preimage_card_envelope query_agreement_bound)"
proof (cases
    "trace_table_low_degree
       (ro_actual_query_zero_round_trace_table data prefix_state) \<and>
     composition_table_low_degree maxDegree
       (ro_actual_query_composition_candidate data query_start) \<and>
     \<not> all_queries_consistent
       (ro_actual_query_zero_round_trace_table data prefix_state)
       (ro_actual_query_composition_candidate data query_start)
       (staged_alphas data)")
  case True
  let ?indices =
    "ro_actual_query_zero_round_trace_composition_accepted_indices
      data prefix_state query_start"
  have base:
      "query_index_raw_list_relation_fiber_bound
        (query_index_lists_over ?indices)
       \<le> rounds * query_raw_preimage_card_envelope (card ?indices)"
    by (rule
      query_index_raw_list_relation_fiber_bound_query_index_lists_over[
        OF ro_actual_query_zero_round_trace_composition_accepted_indices_subset])
  have indices_bound: "card ?indices \<le> query_agreement_bound"
    unfolding
      ro_actual_query_zero_round_trace_composition_accepted_indices_def
    by (rule query_agreement_indices_card_bound)
      (use True in blast)+
  have envelope:
      "query_raw_preimage_card_envelope (card ?indices) \<le>
        query_raw_preimage_card_envelope query_agreement_bound"
    by (rule query_raw_preimage_card_envelope_mono[OF indices_bound])
  have product:
      "rounds * query_raw_preimage_card_envelope (card ?indices)
       \<le> rounds * query_raw_preimage_card_envelope query_agreement_bound"
    using envelope by simp
  have family_eq:
      "ro_actual_query_zero_round_trace_composition_good_query_lists
          data prefix_state query_start =
        query_index_lists_over ?indices"
    unfolding
      ro_actual_query_zero_round_trace_composition_good_query_lists_def
      ro_actual_query_zero_round_trace_composition_accepted_query_lists_def
    using True by simp
  have rewritten:
      "query_index_raw_list_relation_fiber_bound
        (ro_actual_query_zero_round_trace_composition_good_query_lists
          data prefix_state query_start) =
       query_index_raw_list_relation_fiber_bound
        (query_index_lists_over ?indices)"
    using family_eq by simp
  show ?thesis
    using base product rewritten by linarith
next
  case False
  have empty:
      "ro_actual_query_zero_round_trace_composition_good_query_lists
        data prefix_state query_start = {}"
    unfolding
      ro_actual_query_zero_round_trace_composition_good_query_lists_def
    by (simp only: if_False False)
  show ?thesis
    unfolding empty query_index_raw_list_relation_fiber_bound_def
      query_index_raw_list_position_values_def
      query_index_raw_list_preimage_def
    by simp
qed

definition
  ro_actual_query_zero_round_trace_composition_good_query_lists_for
where
  "ro_actual_query_zero_round_trace_composition_good_query_lists_for
      prefix prefix_state data query_start =
    ro_actual_query_zero_round_trace_composition_good_query_lists
      data prefix_state query_start"

lemma
  ro_actual_query_zero_round_trace_composition_good_query_lists_for_subset:
  "ro_actual_query_zero_round_trace_composition_good_query_lists_for
      prefix prefix_state data query_start
    \<subseteq> fri_query_index_list_space"
  unfolding
    ro_actual_query_zero_round_trace_composition_good_query_lists_for_def
  by (rule
    ro_actual_query_zero_round_trace_composition_good_query_lists_subset)

lemma
  ro_actual_query_zero_round_trace_composition_good_query_lists_for_card_bound:
  "card
      (ro_actual_query_zero_round_trace_composition_good_query_lists_for
        prefix prefix_state data query_start)
    \<le> query_agreement_bound ^ rounds"
  unfolding
    ro_actual_query_zero_round_trace_composition_good_query_lists_for_def
  by (rule
    ro_actual_query_zero_round_trace_composition_good_query_lists_card_bound)

lemma
  ro_actual_query_zero_round_trace_composition_good_query_lists_for_relation_fiber_bound:
  "query_index_raw_list_relation_fiber_bound
      (ro_actual_query_zero_round_trace_composition_good_query_lists_for
        prefix prefix_state data query_start)
    \<le> rounds *
      (query_raw_preimage_card_envelope query_agreement_bound)"
  unfolding
    ro_actual_query_zero_round_trace_composition_good_query_lists_for_def
  by (rule
    ro_actual_query_zero_round_trace_composition_good_query_lists_relation_fiber_bound)

definition
  ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent
where
  "ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        (((((prefix, prefix_state), data, query_start, raws, query_states),
            attacker_state), result), final_state) \<Rightarrow>
        trace_table_low_degree
          (ro_actual_query_zero_round_trace_table data prefix_state) \<and>
        composition_table_low_degree maxDegree
          (ro_actual_query_composition_candidate data query_start) \<and>
        all_queries_consistent
          (ro_actual_query_zero_round_trace_table data prefix_state)
          (ro_actual_query_composition_candidate data query_start)
          (staged_alphas data))"

lemma
  ro_absorb_checked_staged_security_clean_zero_round_trace_composition_classification:
  assumes zero: "ceil_log clength = 0"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
    "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_zero_round_bad_query_lists out \<or>
     ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit out \<or>
     ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_zero_round_trace_composition_good_query_lists_for out \<or>
     ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
       out \<or>
     ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
       out \<or>
     ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent
       out"
proof -
  from accepted_out obtain full where out_eq: "out = Some full"
    unfolding accepted_def by (cases out) auto
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
  have trace_class:
      "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
          ro_actual_query_zero_round_bad_query_lists out \<or>
       ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit out \<or>
       ro_absorb_checked_staged_security_zero_round_trace_low_degree out"
    by (rule
      ro_absorb_checked_staged_security_clean_zero_round_trace_classification[
        OF zero wf controlled accepted_out support clean])
  then consider
      (trace_bad)
        "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
          ro_actual_query_zero_round_bad_query_lists out"
    | (trace_target)
        "ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit out"
    | (trace_low)
        "ro_absorb_checked_staged_security_zero_round_trace_low_degree out"
    by blast
  then show ?thesis
  proof cases
    case trace_bad
    then show ?thesis by blast
  next
    case trace_target
    then show ?thesis by blast
  next
    case trace_low
    have trace_low_concrete:
        "trace_table_low_degree
          (ro_actual_query_zero_round_trace_table data prefix_state)"
      using trace_low
      unfolding out_eq full_eq
        ro_absorb_checked_staged_security_zero_round_trace_low_degree_def
      by simp
    have composition_class:
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
      by (rule
        ro_absorb_checked_staged_security_clean_zero_round_composition_candidate_classification[
          OF zero wf controlled accepted_out support clean])
    then consider
        (composition_low)
          "(case out of
            None \<Rightarrow> False
          | Some
              (((((prefix, prefix_state), data, query_start, raws, query_states),
                  attacker_state), result), final_state) \<Rightarrow>
              composition_table_low_degree maxDegree
                (ro_actual_query_composition_candidate data query_start))"
      | (composition_sampled)
          "ro_absorb_checked_staged_security_with_first_root_composition_sampled_bad_pair
            out"
      | (composition_target)
          "ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
            out"
      by blast
    then show ?thesis
    proof cases
      case composition_sampled
      then show ?thesis by blast
    next
      case composition_target
      then show ?thesis by blast
    next
      case composition_low
      have composition_low_concrete:
          "composition_table_low_degree maxDegree
            (ro_actual_query_composition_candidate data query_start)"
        using composition_low unfolding out_eq full_eq by simp
      have consistent_or_targets:
          "(\<forall>j < length raws.
            query_consistent_at
              (ro_actual_query_zero_round_trace_table data prefix_state)
              (ro_actual_query_composition_candidate data query_start)
              (staged_alphas data) (index (to_nat (raws ! j)))) \<or>
           hash_map_new_output_hit
             (ro_zero_round_first_root_prefix_merkle_targets
               prefix prefix_state)
             prefix_state final_state \<or>
           hash_map_new_output_hit
             (ro_actual_query_composition_prefix_targets data query_start)
             query_start final_state"
        by (rule
          ro_absorb_checked_staged_zero_round_actual_query_conceptual_consistency_or_targets[
            OF zero wf controlled builder_out verifier_out final_clean])
      then consider
          (sampled_consistent)
            "\<forall>j < length raws.
              query_consistent_at
                (ro_actual_query_zero_round_trace_table data prefix_state)
                (ro_actual_query_composition_candidate data query_start)
                (staged_alphas data) (index (to_nat (raws ! j)))"
        | (zero_target)
            "hash_map_new_output_hit
              (ro_zero_round_first_root_prefix_merkle_targets
                prefix prefix_state)
              prefix_state final_state"
        | (composition_target)
            "hash_map_new_output_hit
              (ro_actual_query_composition_prefix_targets data query_start)
              query_start final_state"
        by blast
      then show ?thesis
      proof cases
        case zero_target
        have event:
            "ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit
              out"
          using zero_target
          unfolding out_eq full_eq
            ro_absorb_checked_staged_security_zero_round_prefix_merkle_target_hit_def
          by simp
        then show ?thesis by blast
      next
        case composition_target
        have event:
            "ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit
              out"
          using composition_target
          unfolding out_eq full_eq
            ro_absorb_checked_staged_security_with_first_root_composition_prefix_target_hit_def
          by simp
        then show ?thesis by blast
      next
        case sampled_consistent
        show ?thesis
        proof (cases
            "all_queries_consistent
              (ro_actual_query_zero_round_trace_table data prefix_state)
              (ro_actual_query_composition_candidate data query_start)
              (staged_alphas data)")
          case True
          have event:
              "ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent
                out"
            using trace_low_concrete composition_low_concrete True
            unfolding out_eq full_eq
              ro_absorb_checked_staged_security_zero_round_trace_composition_all_queries_consistent_def
            by simp
          then show ?thesis by blast
        next
          case False
          have raws_rounds: "length raws = rounds"
          proof -
            from
              ro_absorb_checked_staged_zero_round_actual_query_boundary_syncE[
                OF zero wf controlled builder_out verifier_out final_clean]
            show ?thesis by blast
          qed
          have mapped_subset:
              "set (map (\<lambda>raw. index (to_nat raw)) raws) \<subseteq>
                ro_actual_query_zero_round_trace_composition_accepted_indices
                  data prefix_state query_start"
          proof
            fix idx
            assume idx_in:
              "idx \<in> set (map (\<lambda>raw. index (to_nat raw)) raws)"
            from idx_in obtain raw where
              raw_in: "raw \<in> set raws"
              and idx_raw: "idx = index (to_nat raw)"
              by auto
            from raw_in obtain j where j_bound: "j < length raws"
              and raw_eq: "raws ! j = raw"
              unfolding in_set_conv_nth by blast
            have idx_eq: "idx = index (to_nat (raws ! j))"
              using idx_raw raw_eq by simp
            have consistent:
                "query_consistent_at
                  (ro_actual_query_zero_round_trace_table data prefix_state)
                  (ro_actual_query_composition_candidate data query_start)
                  (staged_alphas data) idx"
              using sampled_consistent[rule_format, OF j_bound] idx_eq
              by simp
            have sample: "idx \<in> query_sample_space"
              using idx_eq index_less_query_sample_space
              unfolding query_sample_space_def by simp
            show
              "idx \<in>
                ro_actual_query_zero_round_trace_composition_accepted_indices
                  data prefix_state query_start"
              using sample consistent
              unfolding
                ro_actual_query_zero_round_trace_composition_accepted_indices_def
                query_agreement_indices_def
              by simp
          qed
          have sampled_member:
              "map (\<lambda>raw. index (to_nat raw)) raws \<in>
                ro_actual_query_zero_round_trace_composition_accepted_query_lists
                  data prefix_state query_start"
            using raws_rounds mapped_subset
            unfolding
              ro_actual_query_zero_round_trace_composition_accepted_query_lists_def
              query_index_lists_over_def
            by simp
          have good_member:
              "map (\<lambda>raw. index (to_nat raw)) raws \<in>
                ro_actual_query_zero_round_trace_composition_good_query_lists
                  data prefix_state query_start"
            unfolding
              ro_actual_query_zero_round_trace_composition_good_query_lists_def
            using trace_low_concrete composition_low_concrete False sampled_member
            by simp
          have trace_table_head_eq:
              "ro_actual_query_zero_round_trace_table
                  (ro_query_head_data data) prefix_state =
                ro_actual_query_zero_round_trace_table data prefix_state"
            unfolding ro_actual_query_zero_round_trace_table_def
              ro_query_head_data_def
            by simp
          have candidate_head_eq:
              "ro_actual_query_composition_candidate
                  (ro_query_head_data data) query_start =
                ro_actual_query_composition_candidate data query_start"
            unfolding ro_actual_query_composition_candidate_def
              ro_query_head_data_def
            by simp
          have alphas_head_eq:
              "staged_alphas (ro_query_head_data data) = staged_alphas data"
            unfolding ro_query_head_data_def by simp
          have accepted_lists_head_eq:
              "ro_actual_query_zero_round_trace_composition_accepted_query_lists
                  (ro_query_head_data data) prefix_state query_start =
                ro_actual_query_zero_round_trace_composition_accepted_query_lists
                  data prefix_state query_start"
            unfolding
              ro_actual_query_zero_round_trace_composition_accepted_query_lists_def
              ro_actual_query_zero_round_trace_composition_accepted_indices_def
            by (simp only: trace_table_head_eq candidate_head_eq alphas_head_eq)
          have good_eq:
              "ro_actual_query_zero_round_trace_composition_good_query_lists_for
                  prefix prefix_state (ro_query_head_data data) query_start =
                ro_actual_query_zero_round_trace_composition_good_query_lists
                  data prefix_state query_start"
            unfolding
              ro_actual_query_zero_round_trace_composition_good_query_lists_for_def
              ro_actual_query_zero_round_trace_composition_good_query_lists_def
            by (simp only: trace_table_head_eq candidate_head_eq alphas_head_eq
                accepted_lists_head_eq)
          have event:
              "ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit
                ro_actual_query_zero_round_trace_composition_good_query_lists_for
                out"
            using good_member good_eq
            unfolding out_eq full_eq
              ro_absorb_checked_staged_security_query_head_dependent_actual_query_index_list_hit_def
              ro_query_head_dependent_actual_query_index_list_hit_def
            by simp
          then show ?thesis by blast
        qed
      qed
    qed
  qed
qed

end
end
