(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Partial_Evidence.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Partial_Evidence
  imports
    Soundness_FRI_First_Root_RO_Actual_Query_Route
    Soundness_FRI_Generic_Low_Degree
begin


context soundness
begin

lemma query_round_fri_layer_transcripts_trace_round_layer_evidence:
  assumes transcript:
    "query_round_fri_layer_transcripts (query_idxs ! round_idx)
      roots composition_roots chunk trace_layers composition_layers"
    and challenges_len: "length challenges = length roots"
    and query_len: "length round_layers = length query_idxs"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length roots"
    and round_layers_at: "round_layers ! round_idx = trace_layers"
  shows
    "fri_round_layer_evidence roots challenges query_idxs round_idx
      layer_idx round_layers"
proof -
  from transcript obtain trace_fri_chunk where
    trace:
      "fri_layers_transcript (length roots) (clength * scale)
        trace_layers trace_fri_chunk"
    unfolding query_round_fri_layer_transcripts_def by blast
  from fri_layers_transcript_nth_opening[OF trace layer_bound]
  obtain xp xp_path xn xn_path where layer_opening:
    "fri_layer_opening_chunk
      (fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
      xp xp_path xn xn_path (trace_layers ! layer_idx)"
    by blast
  have step:
    "fri_layer_step_evidence
      (roots ! layer_idx)
      (challenges ! layer_idx)
      (fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
      (fri_layer_indices (length roots) (query_idxs ! round_idx)
        (clength * scale) ! layer_idx)
      (2 ^ layer_idx)
      (fri_sibling_index
        (fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
        (fri_layer_indices (length roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx))
      xp xp_path xn xn_path
      ((fri_layer_indices (length roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx) mod
        ((fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
          div 2))
      (fri_fold_value (challenges ! layer_idx) xp xn
        (fri_fold_denominator
          ((h ^
            (fri_layer_indices (length roots) (query_idxs ! round_idx)
              (clength * scale) ! layer_idx)) * shift)
          (2 ^ layer_idx)))
      (round_layers ! round_idx ! layer_idx)"
    using layer_opening round_layers_at
    unfolding fri_layer_step_evidence_def by simp
  show ?thesis
    unfolding fri_round_layer_evidence_def
    using round_bound layer_bound challenges_len query_len step
    by blast
qed

lemma query_round_fri_layer_transcripts_trace_all_round_layer_evidence:
  assumes challenges_len: "length challenges = length roots"
    and query_len: "length round_layers = length query_idxs"
    and layers:
      "\<forall>round_idx < length query_idxs.
        query_round_fri_layer_transcripts (query_idxs ! round_idx)
          roots composition_roots (chunks ! round_idx)
          (round_layers ! round_idx) (composition_round_layers ! round_idx)"
  shows
    "fri_all_round_layer_evidence roots challenges query_idxs round_layers"
  unfolding fri_all_round_layer_evidence_def
proof (intro conjI allI impI)
  show "length challenges = length roots"
    by (rule challenges_len)
  show "length round_layers = length query_idxs"
    by (rule query_len)
  fix round_idx layer_idx
  assume round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length roots"
  show
    "fri_round_layer_evidence roots challenges query_idxs round_idx
      layer_idx round_layers"
    by (rule query_round_fri_layer_transcripts_trace_round_layer_evidence[
          OF layers[rule_format, OF round_bound] challenges_len query_len
            round_bound layer_bound])
      simp
qed


lemma query_round_fri_layer_transcripts_composition_round_layer_evidence:
  assumes transcript:
    "query_round_fri_layer_transcripts (query_idxs ! round_idx)
      trace_roots roots chunk trace_layers composition_layers"
    and challenges_len: "length challenges = length roots"
    and query_len: "length round_layers = length query_idxs"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length roots"
    and round_layers_at: "round_layers ! round_idx = composition_layers"
  shows
    "fri_round_layer_evidence roots challenges query_idxs round_idx
      layer_idx round_layers"
proof -
  from transcript obtain composition_fri_chunk where
    composition:
      "fri_layers_transcript (length roots) (clength * scale)
        composition_layers composition_fri_chunk"
    unfolding query_round_fri_layer_transcripts_def by blast
  from fri_layers_transcript_nth_opening[OF composition layer_bound]
  obtain xp xp_path xn xn_path where layer_opening:
    "fri_layer_opening_chunk
      (fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
      xp xp_path xn xn_path (composition_layers ! layer_idx)"
    by blast
  have step:
    "fri_layer_step_evidence
      (roots ! layer_idx)
      (challenges ! layer_idx)
      (fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
      (fri_layer_indices (length roots) (query_idxs ! round_idx)
        (clength * scale) ! layer_idx)
      (2 ^ layer_idx)
      (fri_sibling_index
        (fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
        (fri_layer_indices (length roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx))
      xp xp_path xn xn_path
      ((fri_layer_indices (length roots) (query_idxs ! round_idx)
          (clength * scale) ! layer_idx) mod
        ((fri_layer_lengths (length roots) (clength * scale) ! layer_idx)
          div 2))
      (fri_fold_value (challenges ! layer_idx) xp xn
        (fri_fold_denominator
          ((h ^
            (fri_layer_indices (length roots) (query_idxs ! round_idx)
              (clength * scale) ! layer_idx)) * shift)
          (2 ^ layer_idx)))
      (round_layers ! round_idx ! layer_idx)"
    using layer_opening round_layers_at
    unfolding fri_layer_step_evidence_def by simp
  show ?thesis
    unfolding fri_round_layer_evidence_def
    using round_bound layer_bound challenges_len query_len step
    by blast
qed

lemma query_round_fri_layer_transcripts_composition_all_round_layer_evidence:
  assumes challenges_len: "length challenges = length roots"
    and query_len: "length round_layers = length query_idxs"
    and layers:
      "\<forall>round_idx < length query_idxs.
        query_round_fri_layer_transcripts (query_idxs ! round_idx)
          trace_roots roots (chunks ! round_idx)
          (trace_round_layers ! round_idx) (round_layers ! round_idx)"
  shows
    "fri_all_round_layer_evidence roots challenges query_idxs round_layers"
  unfolding fri_all_round_layer_evidence_def
proof (intro conjI allI impI)
  show "length challenges = length roots"
    by (rule challenges_len)
  show "length round_layers = length query_idxs"
    by (rule query_len)
  fix round_idx layer_idx
  assume round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length roots"
  show
    "fri_round_layer_evidence roots challenges query_idxs round_idx
      layer_idx round_layers"
    by (rule
        query_round_fri_layer_transcripts_composition_round_layer_evidence[
          OF layers[rule_format, OF round_bound] challenges_len query_len
            round_bound layer_bound])
      simp
qed

lemma
  ro_checked_staged_transcript_program_with_first_root_actual_query_generic_partial_evidence_with_transcripts:
  fixes composition_table :: "'f list"
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
  obtains trace_round_layers composition_round_layers where
    "generic_fri_partial_evidence trace_table_low_degree
      (first_trace_fri_root_prefix_first_table prefix prefix_state)
      (clength - 1)
      (staged_trace_fri_roots data)
      (staged_trace_fri_challenges data)
      (staged_trace_final data)
      (map (\<lambda>raw. index (to_nat raw)) raws)
      trace_round_layers"
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat (staged_degree data)))
      composition_table (to_nat (staged_degree data))
      (staged_composition_fri_roots data)
      (staged_composition_fri_challenges data)
      (staged_composition_final data)
      (map (\<lambda>raw. index (to_nat raw)) raws)
      composition_round_layers"
    "length trace_round_layers = length raws"
    "length composition_round_layers = length raws"
    "\<forall>j < length raws.
      query_round_fri_layer_transcripts
        (map (\<lambda>raw. index (to_nat raw)) raws ! j)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (staged_query_chunks data ! j)
        (trace_round_layers ! j) (composition_round_layers ! j)"
proof -
  from ro_checked_staged_transcript_program_with_first_root_outcomeE[OF outcome]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
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
      ro_checked_staged_transcript_program_with_first_root_projection_outcome_all_rounds[
        OF outcome])
  have shape:
      "length (staged_trace_fri_roots data) = ceil_log clength \<and>
       length (staged_trace_fri_challenges data) = ceil_log clength \<and>
       length (staged_composition_fri_roots data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       length (staged_composition_fri_challenges data) =
         ceil_log (to_nat (staged_degree data) + 1) \<and>
       length (staged_query_chunks data) = rounds"
    using ro_checked_staged_transcript_program_outcome_shape[OF original_out]
    by blast
  have query_bound:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_props:
      "length raws = rounds \<and>
       length query_chunks = rounds \<and>
       (\<forall>j < rounds.
         verifier_query_round_chunk (index (to_nat (raws ! j)))
           (staged_trace_fri_roots head_data)
           (staged_composition_fri_roots head_data)
           (query_chunks ! j))"
    using ro_checked_staged_query_program_with_witnesses_outcome[
      OF controlled query_bound query_out]
    by blast
  let ?query_idxs = "map (\<lambda>raw. index (to_nat raw)) raws"
  have query_idxs_len: "length ?query_idxs = rounds"
    using query_props by simp
  have chunk_shapes:
      "\<forall>j < rounds.
        verifier_query_round_chunk (?query_idxs ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)"
    using query_props data_eq by simp
  have layer_exists:
      "\<forall>j < rounds.
        \<exists>trace_layers composition_layers.
          query_round_fri_layer_transcripts (?query_idxs ! j)
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)
            (staged_query_chunks data ! j)
            trace_layers composition_layers"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < rounds"
    from verifier_query_round_chunk_fri_layer_transcriptsE[
      OF chunk_shapes[rule_format, OF j_bound]]
    obtain trace_layers composition_layers where
      "query_round_fri_layer_transcripts (?query_idxs ! j)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (staged_query_chunks data ! j)
        trace_layers composition_layers"
      by blast
    then show
      "\<exists>trace_layers composition_layers.
        query_round_fri_layer_transcripts (?query_idxs ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)
          trace_layers composition_layers"
      by blast
  qed
  then obtain trace_layers_of composition_layers_of where layer_of:
      "\<And>j. j < rounds \<Longrightarrow>
        query_round_fri_layer_transcripts (?query_idxs ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)
          (trace_layers_of j) (composition_layers_of j)"
    by metis
  let ?trace_round_layers = "map trace_layers_of [0..<rounds]"
  let ?composition_round_layers =
    "map composition_layers_of [0..<rounds]"
  have trace_round_layers_len:
      "length ?trace_round_layers = length ?query_idxs"
    using query_idxs_len by simp
  have composition_round_layers_len:
      "length ?composition_round_layers = length ?query_idxs"
    using query_idxs_len by simp
  have layers:
      "\<forall>j < length ?query_idxs.
        query_round_fri_layer_transcripts (?query_idxs ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)
          (?trace_round_layers ! j) (?composition_round_layers ! j)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length ?query_idxs"
    then have j_round: "j < rounds"
      using query_idxs_len by simp
    show
      "query_round_fri_layer_transcripts (?query_idxs ! j)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (staged_query_chunks data ! j)
        (?trace_round_layers ! j) (?composition_round_layers ! j)"
      using layer_of[OF j_round] j_round by simp
  qed
  have all_layers:
      "fri_all_round_layer_evidence
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        ?query_idxs ?trace_round_layers"
    by (rule
      query_round_fri_layer_transcripts_trace_all_round_layer_evidence[
        OF _ trace_round_layers_len layers])
      (use shape in simp)
  have composition_all_layers:
      "fri_all_round_layer_evidence
        (staged_composition_fri_roots data)
        (staged_composition_fri_challenges data)
        ?query_idxs ?composition_round_layers"
    by (rule
      query_round_fri_layer_transcripts_composition_all_round_layer_evidence[
        OF _ composition_round_layers_len layers])
      (use shape in simp)
  have trace_count:
      "length (staged_trace_fri_roots data) =
        fri_round_count_for_degree_bound (clength - 1)"
    using shape trace_fri_algebraic_round_count_eq
    unfolding trace_fri_algebraic_round_count_def
    by simp
  have composition_count:
      "length (staged_composition_fri_roots data) =
        fri_round_count_for_degree_bound (to_nat (staged_degree data))"
    using shape
    unfolding fri_round_count_for_degree_bound_def
    by simp
  have trace_partial:
      "generic_fri_partial_evidence trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (clength - 1)
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        (staged_trace_final data)
        ?query_idxs ?trace_round_layers"
    unfolding generic_fri_partial_evidence_def
    using trace_count shape all_layers by simp
  have composition_partial:
      "generic_fri_partial_evidence
        (composition_table_low_degree (to_nat (staged_degree data)))
        composition_table (to_nat (staged_degree data))
        (staged_composition_fri_roots data)
        (staged_composition_fri_challenges data)
        (staged_composition_final data)
        ?query_idxs ?composition_round_layers"
    unfolding generic_fri_partial_evidence_def
    using composition_count shape composition_all_layers by simp
  have trace_round_layers_raw_len:
      "length ?trace_round_layers = length raws"
    using trace_round_layers_len by simp
  have composition_round_layers_raw_len:
      "length ?composition_round_layers = length raws"
    using composition_round_layers_len by simp
  have layers_raw:
      "\<forall>j < length raws.
        query_round_fri_layer_transcripts
          (map (\<lambda>raw. index (to_nat raw)) raws ! j)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          (staged_query_chunks data ! j)
          (?trace_round_layers ! j) (?composition_round_layers ! j)"
    using layers by simp
  show ?thesis
    by (rule that[OF trace_partial composition_partial
          trace_round_layers_raw_len composition_round_layers_raw_len
          layers_raw])
qed


lemma
  ro_checked_staged_transcript_program_with_first_root_actual_query_generic_partial_evidence:
  fixes composition_table :: "'f list"
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
  obtains trace_round_layers composition_round_layers where
    "generic_fri_partial_evidence trace_table_low_degree
      (first_trace_fri_root_prefix_first_table prefix prefix_state)
      (clength - 1)
      (staged_trace_fri_roots data)
      (staged_trace_fri_challenges data)
      (staged_trace_final data)
      (map (\<lambda>raw. index (to_nat raw)) raws)
      trace_round_layers"
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat (staged_degree data)))
      composition_table (to_nat (staged_degree data))
      (staged_composition_fri_roots data)
      (staged_composition_fri_challenges data)
      (staged_composition_final data)
      (map (\<lambda>raw. index (to_nat raw)) raws)
      composition_round_layers"
proof -
  from
    ro_checked_staged_transcript_program_with_first_root_actual_query_generic_partial_evidence_with_transcripts[
      OF wf controlled outcome, where composition_table=composition_table]
  obtain trace_round_layers composition_round_layers where
    trace_partial:
      "generic_fri_partial_evidence trace_table_low_degree
        (first_trace_fri_root_prefix_first_table prefix prefix_state)
        (clength - 1)
        (staged_trace_fri_roots data)
        (staged_trace_fri_challenges data)
        (staged_trace_final data)
        (map (\<lambda>raw. index (to_nat raw)) raws)
        trace_round_layers"
    and composition_partial:
      "generic_fri_partial_evidence
        (composition_table_low_degree (to_nat (staged_degree data)))
        composition_table (to_nat (staged_degree data))
        (staged_composition_fri_roots data)
        (staged_composition_fri_challenges data)
        (staged_composition_final data)
        (map (\<lambda>raw. index (to_nat raw)) raws)
        composition_round_layers"
    .
  show ?thesis
    by (rule that[OF trace_partial composition_partial])
qed


end
end
