theory Soundness_FRI_RO_Actual_Query_Joint_Evidence
  imports Soundness_FRI_RO_Actual_Query_Chain_Conflict_Collapse
begin


context soundness
begin

lemma ro_absorb_checked_staged_first_root_actual_query_boundary_syncE:
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
  obtains head_data query_chunks f_fl fl verifier_query_state
      fr f_final as final where
    "Some ((raws, query_states, query_chunks), attacker_state) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program_with_witnesses A
            (staged_trace_fri_roots head_data)
            (staged_composition_fri_roots head_data)
            query_start 0 rounds)
          query_start)"
    "data = head_data\<lparr>staged_query_chunks := query_chunks\<rparr>"
    "fr = staged_trace_root data"
    "map fst f_fl = staged_trace_fri_challenges data"
    "map snd f_fl = staged_trace_fri_roots data"
    "f_final = staged_trace_final data"
    "as = staged_alphas data"
    "map fst fl = staged_composition_fri_challenges data"
    "map snd fl = staged_composition_fri_roots data"
    "final = staged_composition_final data"
    "f_fl \<noteq> []"
    "to_nat (staged_degree data) \<le> maxDegree"
    "Some (results, final_state) \<in>
      set_dist
        (execute
          (ntimes
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          verifier_query_state)"
    "attacker_state \<le> verifier_query_state"
    "PState verifier_query_state = PState query_start"
    "PQueryCounter verifier_query_state = PQueryCounter query_start"
    "PTranscript verifier_query_state = List.concat query_chunks @ []"
    "length raws = rounds"
    "length query_chunks = rounds"
    "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
proof -
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
            (ro_checked_staged_after_first_trace_fri_root_prefix_program A
              prefix)
            prefix_final)"
    and query_out:
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
    by blast

  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
        ro_checked_staged_transcript_program_with_first_root_projection_outcome[
          OF nonempty builder_out])
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
  have query_bound:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_props:
      "length raws = rounds \<and>
       length query_states = rounds \<and>
       length query_chunks = rounds \<and>
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
         verifier_query_round_chunk (index (to_nat (raws ! j)))
           (staged_trace_fri_roots head_data)
           (staged_composition_fri_roots head_data)
           (query_chunks ! j)) \<and>
       (\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale)"
    by (rule ro_checked_staged_query_program_with_witnesses_outcome[
          OF controlled query_bound query_out])

  have boundary_trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    using shape by simp
  have boundary_composition_len:
      "length (staged_composition_fri_roots data) =
        ceil_log (to_nat (staged_degree data) + 1)"
    using shape by simp
  have boundary_alphas_len:
      "length (staged_alphas data) = length spec"
    using shape by simp
  have boundary_query_idxs_len:
      "length (map (\<lambda>raw. index (to_nat raw)) raws) = rounds"
    using query_props by simp
  have boundary_chunks_len:
      "length (staged_query_chunks data) = rounds"
    using shape by simp
  have boundary_chunk_shapes:
      "\<forall>j < rounds.
        verifier_query_round_chunk
          (map (\<lambda>raw. index (to_nat raw)) raws ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)"
    using query_props data_eq by simp

  have full_sync:
      "(PState final_state = PState attacker_state \<and>
        PTranscript final_state = [] \<and>
        verifier_state_from_adversary attacker_state
          (staged_proof_transcript data) \<le> final_state \<and>
        PQueryCounter final_state = rounds) \<and>
       (\<exists>fr trace_pairs f_final as dg composition_pairs final
            verifier_query_state.
          fr = staged_trace_root data \<and>
          map fst trace_pairs = staged_trace_fri_challenges data \<and>
          map snd trace_pairs = staged_trace_fri_roots data \<and>
          f_final = staged_trace_final data \<and>
          as = staged_alphas data \<and>
          dg = staged_degree data \<and>
          to_nat dg \<le> maxDegree \<and>
          map fst composition_pairs =
            staged_composition_fri_challenges data \<and>
          map snd composition_pairs =
            staged_composition_fri_roots data \<and>
          final = staged_composition_final data \<and>
          Some (results, final_state) \<in>
            set_dist
              (execute
                (ntimes
                  (ro_verifier_query_round_program fr trace_pairs f_final as
                    composition_pairs final)
                  rounds)
                verifier_query_state) \<and>
          attacker_state \<le> verifier_query_state \<and>
          PTranscript verifier_query_state =
            List.concat (staged_query_chunks data) \<and>
          PQueryCounter verifier_query_state = 0)"
    by (rule
        ro_checked_staged_transcript_program_ro_verify_monad_full_sync[
          OF wf controlled original_out verifier_out])
  then obtain fr f_fl f_final as dg fl final verifier_query_state where
    fr_eq: "fr = staged_trace_root data"
    and trace_challenges_eq:
      "map fst f_fl = staged_trace_fri_challenges data"
    and trace_roots_eq:
      "map snd f_fl = staged_trace_fri_roots data"
    and trace_final_eq: "f_final = staged_trace_final data"
    and alphas_eq: "as = staged_alphas data"
    and degree_eq: "dg = staged_degree data"
    and degree_bound_raw: "to_nat dg \<le> maxDegree"
    and composition_challenges_eq:
      "map fst fl = staged_composition_fri_challenges data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and composition_final_eq: "final = staged_composition_final data"
    and verifier_query_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            verifier_query_state)"
    and attacker_verifier_ext:
      "attacker_state \<le> verifier_query_state"
    and verifier_transcript:
      "PTranscript verifier_query_state =
        List.concat (staged_query_chunks data)"
    and verifier_counter: "PQueryCounter verifier_query_state = 0"
    by blast
  have f_fl_nonempty: "f_fl \<noteq> []"
    using trace_roots_eq boundary_trace_len nonempty by auto
  have degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    using degree_eq degree_bound_raw by simp
  have verifier_query_props:
      "PTranscript final_state = [] \<and>
       ro_absorb_lookup_chain final_state (PState verifier_query_state)
         (List.concat (staged_query_chunks data)) (PState final_state) \<and>
       verifier_query_state \<le> final_state \<and>
       PQueryCounter final_state =
         PQueryCounter verifier_query_state + rounds"
    by (rule
        ntimes_ro_verifier_query_round_program_aligns_expected_chunks[
          OF boundary_chunks_len boundary_query_idxs_len
            boundary_chunk_shapes _ _ _ verifier_query_out])
      (use verifier_transcript trace_roots_eq composition_roots_eq in simp_all)
  have verifier_chain:
      "ro_absorb_lookup_chain final_state (PState verifier_query_state)
        (List.concat (staged_query_chunks data)) (PState final_state)"
    using verifier_query_props by simp
  have verifier_ext: "verifier_query_state \<le> final_state"
    using verifier_query_props by simp

  have attacker_final_ext: "attacker_state \<le> final_state"
    by (rule hash_ext_trans[OF attacker_verifier_ext verifier_ext])
  have builder_chain_attacker:
      "ro_absorb_lookup_chain attacker_state (PState query_start)
        (List.concat query_chunks) (PState attacker_state)"
    using ro_checked_staged_query_program_with_witnesses_absorb_lookup_chain[
      OF controlled query_bound query_out]
    by blast
  have builder_chain_final:
      "ro_absorb_lookup_chain final_state (PState query_start)
        (List.concat query_chunks) (PState attacker_state)"
    by (rule ro_absorb_lookup_chain_mono[
          OF builder_chain_attacker attacker_final_ext])

  have sync:
      "PState final_state = PState attacker_state \<and>
       PTranscript final_state = [] \<and>
       verifier_state_from_adversary attacker_state
         (staged_proof_transcript data) \<le> final_state \<and>
       PQueryCounter final_state = rounds"
    by (rule ro_checked_staged_transcript_program_ro_verify_monad_sync[
          OF wf controlled original_out verifier_out])
  have builder_chain_final':
      "ro_absorb_lookup_chain final_state (PState query_start)
        (List.concat (staged_query_chunks data)) (PState final_state)"
    using builder_chain_final sync data_eq by simp
  have verifier_builder_state:
      "PState verifier_query_state = PState query_start"
    by (rule ro_absorb_lookup_chain_start_functional_if_clean[
          OF clean verifier_chain builder_chain_final'])

  have good_fields:
      "prefix_state \<le> attacker_state \<and> PQueryCounter query_start = 0"
    by (rule
        ro_checked_staged_transcript_program_with_first_root_good_fields[
          OF wf controlled nonempty builder_out])
  have counter_eq:
      "PQueryCounter verifier_query_state = PQueryCounter query_start"
    using verifier_counter good_fields by simp
  have verifier_transcript':
      "PTranscript verifier_query_state = List.concat query_chunks @ []"
    using verifier_transcript data_eq by simp

  show ?thesis
    by (rule that[OF query_out data_eq fr_eq trace_challenges_eq
          trace_roots_eq trace_final_eq alphas_eq
          composition_challenges_eq composition_roots_eq
          composition_final_eq f_fl_nonempty degree_bound verifier_query_out
          attacker_verifier_ext verifier_builder_state counter_eq
          verifier_transcript'])
      (use query_props in simp_all)
qed




lemma
  ro_absorb_checked_staged_first_root_actual_query_accepted_evidence:
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
    "f_fl \<noteq> []"
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

  from ro_absorb_checked_staged_first_root_actual_query_boundary_syncE[
      OF wf controlled nonempty builder_out verifier_out clean]
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
    and f_fl_nonempty: "f_fl \<noteq> []"
    and degree_bound: "to_nat (staged_degree data) \<le> maxDegree"
    and verifier_query_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            verifier_query_state)"
    and attacker_verifier_ext:
      "attacker_state \<le> verifier_query_state"
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
        ro_checked_staged_transcript_program_with_first_root_projection_outcome[
          OF nonempty builder_out])
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       ceil_log (to_nat (staged_degree data) + 1) \<le>
         ceil_log (maxDegree + 1)"
    using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
    by blast

  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have trace_count: "length f_fl \<le> N"
  proof -
    have clength_bound: "clength \<le> clength * scale"
      using scale_pos by simp
    have ceil_bound: "ceil_log clength \<le> N"
      by (rule ceil_log_le_power)
        (use clength_bound eval_power in simp)
    have trace_len: "length f_fl = ceil_log clength"
    proof -
      have len_eq:
          "length (map snd f_fl) =
            length (staged_trace_fri_roots data)"
        by (rule arg_cong[OF trace_roots_eq])
      show ?thesis
        using len_eq shape by simp
    qed
    show ?thesis
      using trace_len ceil_bound by linarith
  qed
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
            trace_layers_rounds composition_layers_rounds
            layer_transcripts'])
      (use trace_roots_eq composition_roots_eq data_eq in simp_all)

  have accepted:
      "\<forall>round_idx < length raws.
        ro_recorded_query_fri_accepted_evidence
          fr f_fl f_final as fl final (raws ! round_idx)
          (trace_round_layers ! round_idx)
          (composition_round_layers ! round_idx) final_state"
    using accepted_result raws_rounds by simp
  have query_start_attacker: "query_start \<le> attacker_state"
    using ro_checked_staged_query_program_with_witnesses_outcome[
      OF controlled query_bound query_out]
    by blast
  have query_start_final: "query_start \<le> final_state"
    using query_start_attacker attacker_verifier_ext accepted_result
    by (meson hash_ext_trans)
  have prefix_state_attacker: "prefix_state \<le> attacker_state"
    using
      ro_checked_staged_transcript_program_with_first_root_good_fields[
        OF wf controlled nonempty builder_out]
    by blast
  have prefix_state_final: "prefix_state \<le> final_state"
    using prefix_state_attacker attacker_verifier_ext accepted_result
    by (meson hash_ext_trans)
  show ?thesis
    by (rule that[OF fr_eq query_start_final prefix_state_final
          trace_challenges_eq trace_roots_eq trace_final_eq alphas_eq
          composition_challenges_eq composition_roots_eq
          composition_final_eq f_fl_nonempty
          degree_bound trace_layers_len composition_layers_len layer_transcripts
          raw_bound accepted])
qed


lemma
  ro_absorb_checked_staged_first_root_actual_query_joint_fri_evidence:
  fixes composition_table :: "'f list"
    and final_state :: "'f protocol_channel"
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
  obtains f_fl fl f_final final trace_round_layers
      composition_round_layers where
    "map fst f_fl = staged_trace_fri_challenges data"
    "map snd f_fl = staged_trace_fri_roots data"
    "map fst fl = staged_composition_fri_challenges data"
    "map snd fl = staged_composition_fri_roots data"
    "f_fl \<noteq> []"
    "to_nat (staged_degree data) \<le> maxDegree"
    "generic_fri_partial_evidence trace_table_low_degree
      (first_trace_fri_root_prefix_first_table prefix prefix_state)
      (clength - 1) (map snd f_fl) (map fst f_fl) f_final
      (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers"
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat (staged_degree data)))
      composition_table (to_nat (staged_degree data))
      (map snd fl) (map fst fl) final
      (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    "generic_fri_recorded_value_chain_evidence
      (map snd f_fl) (map fst f_fl) f_final
      (map (\<lambda>raw. index (to_nat raw)) raws) trace_round_layers"
    "generic_fri_recorded_value_chain_evidence
      (map snd fl) (map fst fl) final
      (map (\<lambda>raw. index (to_nat raw)) raws) composition_round_layers"
    "generic_fri_recorded_chunks_authenticated
      (map snd f_fl) (map (\<lambda>raw. index (to_nat raw)) raws)
      trace_round_layers final_state"
    "generic_fri_recorded_chunks_authenticated
      (map snd fl) (map (\<lambda>raw. index (to_nat raw)) raws)
      composition_round_layers final_state"
    "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
proof -
  from ro_absorb_checked_staged_first_root_actual_query_accepted_evidence[
      OF wf controlled nonempty builder_out verifier_out clean]
  obtain f_fl fl fr f_final as final trace_round_layers
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

  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
        ro_checked_staged_transcript_program_with_first_root_projection_outcome[
          OF nonempty builder_out])
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (to_nat (staged_degree data) + 1)"
    using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
    by blast
  have trace_count:
      "length (map snd f_fl) =
        fri_round_count_for_degree_bound (clength - 1)"
    using trace_roots_eq shape trace_fri_algebraic_round_count_eq
    unfolding trace_fri_algebraic_round_count_def
    by simp
  have composition_count:
      "length (map snd fl) =
        fri_round_count_for_degree_bound (to_nat (staged_degree data))"
    using composition_roots_eq shape
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
        (composition_table_low_degree (to_nat (staged_degree data)))
        composition_table (to_nat (staged_degree data))
        (map snd fl) (map fst fl) final
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
  have authenticated:
      "generic_fri_recorded_chunks_authenticated
         (map snd f_fl) ?query_idxs trace_round_layers final_state \<and>
       generic_fri_recorded_chunks_authenticated
         (map snd fl) ?query_idxs composition_round_layers final_state"
    by (rule ro_recorded_query_fri_accepted_evidence_all_chunks_authenticated[
          OF trace_layers_len composition_layers_len accepted])

  show ?thesis
    by (rule that[OF trace_challenges_eq trace_roots_eq
          composition_challenges_eq composition_roots_eq f_fl_nonempty
          degree_bound trace_partial composition_partial _ _ _ _ raw_bound])
      (use chains authenticated in simp_all)
qed
end
end
