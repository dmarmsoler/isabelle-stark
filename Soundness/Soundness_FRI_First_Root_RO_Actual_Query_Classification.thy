(*  Title:      Stark/Soundness_FRI_First_Root_RO_Actual_Query_Classification.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_First_Root_RO_Actual_Query_Classification
  imports Soundness_FRI_First_Root_RO_Verifier_Query_Boundary
begin


context soundness
begin

lemma ro_absorb_checked_staged_first_root_actual_query_base_agreement_or_target:
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
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        first_trace_fri_root_prefix_base_agreement_query_lists
          prefix prefix_state \<or>
      hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state"
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

  obtain fr prefix_trace_bs first_root where
    prefix_eq: "prefix = (fr, prefix_trace_bs, first_root)"
    by (cases prefix) auto
  have prefix_props:
      "prefix_trace_bs = [] \<and>
       prefix_state = prefix_final \<and>
       adversary_initial_state \<le> prefix_final \<and>
       ro_absorb_lookup_chain prefix_final
         (PState adversary_initial_state) [fr, first_root]
         (PState prefix_final) \<and>
       PQueryCounter prefix_final = PQueryCounter adversary_initial_state"
    by (rule ro_staged_first_trace_fri_root_prefix_program_chain[
          OF wf controlled nonempty])
      (use prefix_out prefix_eq in simp)
  have after_fields:
      "staged_trace_root head_data = fr \<and>
       (\<exists>roots. staged_trace_fri_roots head_data = first_root # roots)"
    by (rule
        ro_checked_staged_after_first_trace_fri_root_prefix_program_fields[
          OF nonempty])
      (use after_out prefix_eq in simp)

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

  from ro_verify_monad_actual_query_boundaryE[
      OF nonempty boundary_trace_len boundary_composition_len
        boundary_alphas_len boundary_query_idxs_len boundary_chunks_len
        boundary_chunk_shapes verifier_out]
  obtain f_fl fl verifier_query_state verifier_fr f_final alphas final where
    verifier_fr_eq: "verifier_fr = staged_trace_root data"
    and trace_roots_eq:
      "map snd f_fl = staged_trace_fri_roots data"
    and composition_roots_eq:
      "map snd fl = staged_composition_fri_roots data"
    and f_fl_nonempty: "f_fl \<noteq> []"
    and verifier_query_out:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program verifier_fr f_fl f_final
                alphas fl final)
              rounds)
            verifier_query_state)"
    and verifier_transcript:
      "PTranscript verifier_query_state =
        List.concat (staged_query_chunks data)"
    and attacker_verifier_ext:
      "attacker_state \<le> verifier_query_state"
    and verifier_counter:

      "PQueryCounter verifier_query_state = 0"
    and verifier_chain:
      "ro_absorb_lookup_chain final_state (PState verifier_query_state)
        (List.concat (staged_query_chunks data)) (PState final_state)"
    and verifier_ext: "verifier_query_state \<le> final_state"
    .

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

  obtain b rt f_fl_tail where
    f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    using f_fl_nonempty by (cases f_fl) auto

  have authenticated:
      "\<exists>trace_openings_at first_openings_at.
        verifier_query_state \<le> final_state \<and>
        length raws = rounds \<and>
        length query_states = rounds \<and>
        length query_chunks = rounds \<and>
        (\<forall>j < rounds.
          map opening_index (trace_openings_at j) =
            powers_scaled (index (to_nat (raws ! j))) \<and>
          partial_authenticated_table verifier_fr (scale * clength)
            (trace_openings_at j) final_state \<and>
          map opening_index (first_openings_at j) =
            [index (to_nat (raws ! j)),
              fri_sibling_index (scale * clength)
                (index (to_nat (raws ! j)))] \<and>
          partial_authenticated_table rt (scale * clength)
            (first_openings_at j) final_state \<and>
          opening_value (trace_openings_at j ! 0) =
            opening_value (first_openings_at j ! 0))"
    by (rule
        ro_checked_staged_query_program_with_witnesses_verifier_authenticated_openings[
          OF controlled query_bound query_out attacker_verifier_ext
            verifier_builder_state counter_eq verifier_transcript' f_fl_eq])
      (use trace_roots_eq composition_roots_eq data_eq verifier_query_out in
        simp_all)

  from authenticated obtain trace_openings_at first_openings_at where
    authenticated_ext: "verifier_query_state \<le> final_state"
    and authenticated_lengths:
      "length raws = rounds \<and>
       length query_states = rounds \<and>
       length query_chunks = rounds"
    and authenticated_evidence:
      "\<forall>j < rounds.
        map opening_index (trace_openings_at j) =
          powers_scaled (index (to_nat (raws ! j))) \<and>
        partial_authenticated_table verifier_fr (scale * clength)
          (trace_openings_at j) final_state \<and>
        map opening_index (first_openings_at j) =
          [index (to_nat (raws ! j)),
            fri_sibling_index (scale * clength)
              (index (to_nat (raws ! j)))] \<and>
        partial_authenticated_table rt (scale * clength)
          (first_openings_at j) final_state \<and>
        opening_value (trace_openings_at j ! 0) =
          opening_value (first_openings_at j ! 0)"
    by blast

  have prefix_eq': "prefix = (fr, [], first_root)"
    using prefix_eq prefix_props by simp
  have verifier_fr_prefix: "verifier_fr = fr"
    using verifier_fr_eq after_fields data_eq by simp
  have rt_prefix: "rt = first_root"
    using trace_roots_eq f_fl_eq after_fields data_eq by auto
  have prefix_final_ext: "prefix_state \<le> final_state"
    by (rule hash_ext_trans[OF conjunct1[OF good_fields] attacker_final_ext])
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume "hash_map_output_collision prefix_state"
    then have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[OF _ prefix_final_ext])
    then show False using clean by contradiction
  qed

  let ?query_idxs = "map (\<lambda>raw. index (to_nat raw)) raws"
  have query_len: "length ?query_idxs = rounds"
    using authenticated_lengths by simp
  have query_sample: "set ?query_idxs \<subseteq> query_sample_space"
    unfolding query_sample_space_def
    using index_less_query_sample_space by auto
  have conceptual_agreement_or_target:
      "?query_idxs \<in>
        trace_table_base_agreement_query_lists
          (conceptual_table prefix_state fr (scale * clength))
          (conceptual_table prefix_state first_root (scale * clength)) \<or>
       hash_map_new_output_hit
         (merkle_prefix_path_targets {fr, first_root} prefix_state)
         prefix_state final_state"
  proof (rule
      partial_authenticated_trace_first_fri_query_list_prefix_conceptual_agreement_or_target[
        OF query_len query_sample prefix_final_ext prefix_clean])
    fix i
    assume i_bound: "i < length ?query_idxs"
    have i_round: "i < rounds"
      using i_bound query_len by simp
    have i_raw: "i < length raws"
      using i_round authenticated_lengths by simp
    show
      "map opening_index (trace_openings_at i) =
          powers_scaled (?query_idxs ! i) \<and>
       partial_authenticated_table fr (scale * clength)
          (trace_openings_at i) final_state \<and>
       map opening_index (first_openings_at i) =
          [?query_idxs ! i,
            fri_sibling_index (scale * clength) (?query_idxs ! i)] \<and>
       partial_authenticated_table first_root (scale * clength)
          (first_openings_at i) final_state \<and>
       opening_value (trace_openings_at i ! 0) =
          opening_value (first_openings_at i ! 0)"
      using authenticated_evidence[rule_format, OF i_round]
        verifier_fr_prefix rt_prefix i_raw
      by simp
  qed
  have base_agreement_or_target:
      "?query_idxs \<in>
        first_trace_fri_root_prefix_base_agreement_query_lists
          prefix prefix_state \<or>
       hash_map_new_output_hit
         (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
         prefix_state final_state"
    using conceptual_agreement_or_target prefix_clean
    unfolding prefix_eq'
      first_trace_fri_root_prefix_base_agreement_query_lists_def
      first_trace_fri_root_prefix_trace_table_def
      first_trace_fri_root_prefix_first_table_def
      first_trace_fri_root_prefix_merkle_targets_def
    by simp

  show ?thesis
    using base_agreement_or_target .
qed


lemma ro_absorb_checked_staged_first_root_actual_query_classification:
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
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        first_trace_fri_root_prefix_good_agreement_query_lists
          prefix prefix_state \<or>
      hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state \<or>
      \<not> trace_table_low_degree
          (first_trace_fri_root_prefix_trace_table prefix prefix_state) \<or>
      \<not> trace_table_low_degree
          (first_trace_fri_root_prefix_first_table prefix prefix_state) \<or>
      first_trace_fri_root_prefix_trace_table prefix prefix_state =
        first_trace_fri_root_prefix_first_table prefix prefix_state"
proof -
  have base:
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        first_trace_fri_root_prefix_base_agreement_query_lists
          prefix prefix_state \<or>
      hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state final_state"
    by (rule
        ro_absorb_checked_staged_first_root_actual_query_base_agreement_or_target[
          OF wf controlled nonempty builder_out verifier_out clean])
  show ?thesis
    using base
    unfolding first_trace_fri_root_prefix_good_agreement_query_lists_def
    by auto
qed

end
end
