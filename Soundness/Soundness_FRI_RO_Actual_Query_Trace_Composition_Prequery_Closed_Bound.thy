(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Trace_Composition_Prequery_Closed_Bound.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Prequery_Closed_Bound
  imports
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Adaptive_Query_Budget
    Soundness_FRI_First_Root_RO_Prequery_Closed_Bound
begin

context soundness
begin

lemma trace_composition_absorbed_query_relation_bounded_activeI:
  assumes map_bound: "card (fmdom' (HashMap attacker_state)) \<le> L"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values attacker_state"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and query_start_ext: "query_start \<le> attacker_state"
    and prefix_eq:
      "prefix =
        (staged_trace_root data, [],
          trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data))"
    and no_trace_merkle:
      "\<not> hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state attacker_state"
    and no_composition_merkle:
      "\<not> hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets
          (ro_query_head_data data) query_start)
        query_start attacker_state"
    and header_chain:
      "ro_absorb_lookup_chain attacker_state
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
    and query_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState query_start)
        (List.concat (take j (staged_query_chunks data)))
        (PState (query_states ! j))"
    and trace_len:
      "length (staged_trace_fri_roots data) = ceil_log clength"
    and alpha_len: "length (staged_alphas data) = length spec"
    and composition_len:
      "length (staged_composition_fri_roots data) =
        ceil_log (to_nat (staged_degree data) + 1)"
    and raws_len: "length raws = rounds"
    and raws_in:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_actual_query_trace_composition_good_query_lists
          prefix prefix_state (ro_query_head_data data) query_start"
    and j_bound: "j < rounds"
    and lookup:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge j (PState (query_states ! j))) =
        Some (raws ! j)"
  shows
    "hash_state_relation_active
      (trace_composition_absorbed_query_relation_bounded L)
      (HashMap attacker_state)
      (QueryIndexChallenge j (PState (query_states ! j)))
      (raws ! j)"
proof -
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision attacker_state"
      by (rule hash_map_output_collision_mono[OF collision prefix_ext])
    then show False using clean by contradiction
  qed
  have no_trace_merkle':
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets
          {staged_trace_root data, trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data)}
          prefix_state)
        prefix_state attacker_state"
    using no_trace_merkle prefix_clean
    unfolding prefix_eq first_trace_fri_root_prefix_merkle_targets_def
    by simp
  have original_targets:
      "merkle_prefix_path_targets {staged_trace_root data} prefix_state
        \<subseteq> merkle_prefix_path_targets
          {staged_trace_root data, trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data)}
          prefix_state"
    by (rule merkle_prefix_path_targets_mono) auto
  have first_targets:
      "merkle_prefix_path_targets {trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data)}
          prefix_state
        \<subseteq> merkle_prefix_path_targets
          {staged_trace_root data, trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data)}
          prefix_state"
    by (rule merkle_prefix_path_targets_mono) auto
  have no_original:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets {staged_trace_root data} prefix_state)
        prefix_state attacker_state"
    using no_trace_merkle'
      hash_map_new_output_hit_subset[OF original_targets]
    by blast
  have no_first:
      "\<not> hash_map_new_output_hit
        (merkle_prefix_path_targets
          {trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data)} prefix_state)
        prefix_state attacker_state"
    using no_trace_merkle'
      hash_map_new_output_hit_subset[OF first_targets]
    by blast
  let ?final = "channel_for_hash_map (HashMap attacker_state)"
  have final_map: "HashMap ?final = HashMap attacker_state"
    unfolding channel_for_hash_map_def by simp
  have original_final:
      "conceptual_table ?final (staged_trace_root data)
          (scale * clength) =
        conceptual_table prefix_state (staged_trace_root data)
          (scale * clength)"
  proof -
    have final_attacker:
        "conceptual_table ?final (staged_trace_root data)
            (scale * clength) =
          conceptual_table attacker_state (staged_trace_root data)
            (scale * clength)"
      by (rule conceptual_table_cong_hash_map[OF final_map])
    have attacker_prefix:
        "conceptual_table attacker_state (staged_trace_root data)
            (scale * clength) =
          conceptual_table prefix_state (staged_trace_root data)
            (scale * clength)"
      by (rule conceptual_table_prefix_stable_if_no_target[
        OF prefix_ext no_original])
    show ?thesis using final_attacker attacker_prefix by simp
  qed
  have first_final:
      "first_trace_fri_root_prefix_first_table
          (staged_trace_root data, [],
            trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data))
          ?final =
        first_trace_fri_root_prefix_first_table
          (staged_trace_root data, [],
            trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data))
          prefix_state"
  proof -
    have final_attacker:
        "conceptual_table ?final (trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data))
            (scale * clength) =
          conceptual_table attacker_state
            (trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data)) (scale * clength)"
      by (rule conceptual_table_cong_hash_map[OF final_map])
    have attacker_prefix:
        "conceptual_table attacker_state
            (trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data)) (scale * clength) =
          conceptual_table prefix_state
            (trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data)) (scale * clength)"
      by (rule conceptual_table_prefix_stable_if_no_target[
        OF prefix_ext no_first])
    show ?thesis
      unfolding first_trace_fri_root_prefix_first_table_def
      using final_attacker attacker_prefix by simp
  qed
  have composition_final:
      "ro_actual_query_composition_candidate
          (ro_trace_composition_header_data
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data))
          ?final =
        ro_actual_query_composition_candidate
          (ro_query_head_data data) query_start"
  proof (cases "staged_composition_fri_roots data = []")
    case True
    then show ?thesis
      unfolding ro_actual_query_composition_candidate_def
        ro_query_head_data_def
      by simp
  next
    case False
    have no_composition:
        "\<not> hash_map_new_output_hit
          (merkle_prefix_path_targets
            {hd (staged_composition_fri_roots data)} query_start)
          query_start attacker_state"
      using no_composition_merkle False
      unfolding ro_actual_query_composition_prefix_targets_def
        ro_query_head_data_def
      by simp
    have final_attacker:
        "conceptual_table ?final
            (hd (staged_composition_fri_roots data))
            (scale * clength) =
          conceptual_table attacker_state
            (hd (staged_composition_fri_roots data))
            (scale * clength)"
      by (rule conceptual_table_cong_hash_map[OF final_map])
    have attacker_start:
        "conceptual_table attacker_state
            (hd (staged_composition_fri_roots data))
            (scale * clength) =
          conceptual_table query_start
            (hd (staged_composition_fri_roots data))
            (scale * clength)"
      by (rule conceptual_table_prefix_stable_if_no_target[
        OF query_start_ext no_composition])
    show ?thesis
      unfolding ro_actual_query_composition_candidate_def
        ro_query_head_data_def
      using False final_attacker attacker_start
      by simp
  qed
  have query_lists_final:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_trace_composition_header_query_lists
          (HashMap attacker_state)
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
  proof -
    have query_lists_eq:
        "ro_trace_composition_header_query_lists
            (HashMap attacker_state)
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data) =
          ro_actual_query_trace_composition_good_query_lists
            prefix prefix_state (ro_query_head_data data) query_start"
      unfolding ro_trace_composition_header_query_lists_def
        ro_actual_query_trace_composition_good_query_lists_def
        ro_actual_query_trace_composition_accepted_query_lists_def
        ro_actual_query_trace_composition_accepted_indices_def
        prefix_eq
      using original_final first_final composition_final
      by (simp add: ro_query_head_data_def)
    show ?thesis using raws_in query_lists_eq by simp
  qed
  have header_chain_final:
      "ro_absorb_lookup_chain ?final
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
      (rule header_chain)
  have query_chain_final:
      "ro_absorb_lookup_chain ?final
        (PState query_start)
        (List.concat (take j (staged_query_chunks data)))
        (PState (query_states ! j))"
    by (subst ro_absorb_lookup_chain_cong_hash_map[OF final_map])
      (rule query_chain)
  have clean_final: "\<not> hash_map_output_collision ?final"
    using clean final_map
    unfolding hash_map_output_collision_def by simp
  have no_initial_final:
      "PState adversary_initial_state \<notin> hash_map_output_values ?final"
    using no_initial final_map
    unfolding hash_map_output_values_def by simp
  have relation:
      "trace_composition_absorbed_query_relation
        (HashMap attacker_state)
        (QueryIndexChallenge j (PState (query_states ! j)))
        (raws ! j)"
    unfolding trace_composition_absorbed_query_relation_def Let_def
    using clean_final no_initial_final trace_len alpha_len composition_len
      header_chain_final query_chain_final raws_len
      query_lists_final j_bound
    by blast
  show ?thesis
    unfolding hash_state_relation_active_def
      trace_composition_absorbed_query_relation_bounded_def
    using map_bound lookup relation by simp
qed

lemma ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain:
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
    and j_bound: "j < rounds"
  shows
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
        (List.concat (take j (staged_query_chunks data)))
        (PState (query_states ! j))"
proof -
  from
    ro_checked_staged_transcript_program_with_first_root_outcomeE[OF outcome]
  obtain head_data query_chunks prefix_final where
    prefix_out:
      "Some ((prefix, prefix_state), prefix_final) \<in>
        set_dist
          (execute
            (ro_staged_first_trace_fri_root_prefix_program A)
            adversary_initial_state)"
    and after_out:
      "Some (head_data, query_start) \<in>
        set_dist
          (execute
            (ro_checked_staged_after_first_trace_fri_root_prefix_program
              A prefix)
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
  obtain fr trace_bs first_root where prefix_eq:
      "prefix = (fr, trace_bs, first_root)"
    by (cases prefix) auto
  have prefix_props:
      "trace_bs = [] \<and> prefix_state = prefix_final"
    using ro_staged_first_trace_fri_root_prefix_program_chain[
      OF wf controlled nonempty prefix_out[unfolded prefix_eq]]
    by blast
  have after_fields:
      "staged_trace_root head_data = fr \<and>
        (\<exists>roots. staged_trace_fri_roots head_data = first_root # roots)"
    by (rule
      ro_checked_staged_after_first_trace_fri_root_prefix_program_fields[
        OF nonempty])
      (use after_out prefix_eq in simp)
  obtain trace_roots where
    trace_root_eq: "staged_trace_root data = fr"
    and trace_roots_eq:
      "staged_trace_fri_roots data = first_root # trace_roots"
    using after_fields data_eq by auto
  have prefix_canonical:
      "prefix =
        (staged_trace_root data, [],
          hd (staged_trace_fri_roots data))"
    using prefix_eq prefix_props trace_root_eq trace_roots_eq by simp
  have original_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (ro_checked_staged_transcript_program A)
            adversary_initial_state)"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_projection_outcome[
        OF nonempty outcome])
  have full_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state)
        (staged_proof_transcript data) (PState attacker_state)"
    using ro_checked_staged_transcript_program_absorb_lookup_chain[
      OF wf controlled original_out]
    by blast
  let ?header =
    "verifier_header_messages
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)"
  have transcript_eq:
      "staged_proof_transcript data =
        ?header @ List.concat (staged_query_chunks data)"
    unfolding staged_proof_transcript_def by simp
  from ro_absorb_lookup_chain_append_split[
      OF full_chain[unfolded transcript_eq]]
  obtain header_end where
    header_chain:
      "ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state) ?header header_end"
    and query_tail:
      "ro_absorb_lookup_chain attacker_state header_end
        (List.concat (staged_query_chunks data))
        (PState attacker_state)"
    by blast
  have query_bound:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have query_full:
      "ro_absorb_lookup_chain attacker_state
        (PState query_start)
        (List.concat (staged_query_chunks data))
        (PState attacker_state)"
    using
      ro_checked_staged_query_program_with_witnesses_absorb_lookup_chain[
        OF controlled query_bound query_out]
      data_eq
    by simp
  have header_end_eq: "header_end = PState query_start"
    by (rule ro_absorb_lookup_chain_start_functional_if_clean[
      OF clean query_tail query_full])
  have header_chain':
      "ro_absorb_lookup_chain attacker_state
        (PState adversary_initial_state) ?header (PState query_start)"
    using header_chain header_end_eq by simp
  have query_prefix:
      "ro_absorb_lookup_chain attacker_state
        (PState query_start)
        (List.concat (take j (staged_query_chunks data)))
        (PState (query_states ! j))"
    using ro_checked_staged_query_program_with_witnesses_prefix_chain[
      OF controlled query_bound query_out j_bound]
      data_eq
    by simp
  show ?thesis
    using prefix_canonical header_chain' query_prefix by blast
qed


lemma trace_composition_prequery_good_imp_budgeted_relation_transition:
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
    and prequery:
      "ro_query_head_dependent_query_start_prequery_hit
        ro_actual_query_trace_composition_good_query_lists
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
    and clean: "\<not> hash_map_output_collision attacker_state"
    and no_initial:
      "PState adversary_initial_state \<notin> hash_map_output_values attacker_state"
    and no_trace_merkle:
      "\<not> hash_map_new_output_hit
        (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
        prefix_state attacker_state"
    and no_composition_merkle:
      "\<not> hash_map_new_output_hit
        (ro_actual_query_composition_prefix_targets
          (ro_query_head_data data) query_start)
        query_start attacker_state"
  shows
    "hash_state_relation_transition
      (trace_composition_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
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
  have prequery_props:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
          ro_actual_query_trace_composition_good_query_lists
            prefix prefix_state (ro_query_head_data data) query_start \<and>
        (\<exists>j < rounds.
          fmlookup (HashMap query_start)
            (QueryIndexChallenge
              (PQueryCounter (query_states ! j))
              (PState (query_states ! j))) =
            Some (raws ! j))"
    using prequery
    unfolding ro_query_head_dependent_query_start_prequery_hit_def
    by simp
  then obtain j where
    raws_in:
      "map (\<lambda>raw. index (to_nat raw)) raws \<in>
        ro_actual_query_trace_composition_good_query_lists
          prefix prefix_state (ro_query_head_data data) query_start"
    and j_bound: "j < rounds"
    and lookup_start:
      "fmlookup (HashMap query_start)
        (QueryIndexChallenge
          (PQueryCounter (query_states ! j))
          (PState (query_states ! j))) =
        Some (raws ! j)"
    by blast
  have good_fields:
      "prefix_state \<le> attacker_state \<and> PQueryCounter query_start = 0"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_good_fields[
        OF wf controlled nonempty outcome])
  have prefix_ext: "prefix_state \<le> attacker_state"
    and query_start_counter: "PQueryCounter query_start = 0"
    using good_fields by blast+
  have query_start_ext: "query_start \<le> attacker_state"
    using outcome_props by blast
  have counter_j: "PQueryCounter (query_states ! j) = j"
    using witness_props query_start_counter j_bound by simp
  have lookup_final_raw:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge j (PState (query_states ! j))) =
        Some (raws ! j)"
  proof -
    have lifted:
        "fmlookup (HashMap attacker_state)
          (QueryIndexChallenge
            (PQueryCounter (query_states ! j))
            (PState (query_states ! j))) =
          Some (raws ! j)"
      by (rule hash_extension_lookup[OF lookup_start query_start_ext])
    show ?thesis using lifted counter_j by simp
  qed
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
          (List.concat (take j (staged_query_chunks data)))
          (PState (query_states ! j))"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_header_query_prefix_chain[
        OF wf controlled nonempty outcome clean j_bound])
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
  have trace_nonempty: "staged_trace_fri_roots data \<noteq> []"
    using shape nonempty by auto
  have prefix_selector:
      "prefix =
        (staged_trace_root data, [],
          trace_composition_header_trace_root
            (staged_trace_root data) (staged_trace_fri_roots data))"
    using conjunct1[OF chains] trace_nonempty
    by (simp add: trace_composition_header_trace_root_nonempty)
  have map_bound:
      "card (fmdom' (HashMap attacker_state)) \<le>
        ro_checked_staged_transcript_hash_query_budget_for budgets"
    by (rule
      ro_checked_staged_transcript_program_with_first_root_map_domain_bound[
        OF wf controlled nonempty outcome clean])
  have active:
      "hash_state_relation_active
        (trace_composition_absorbed_query_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets))
        (HashMap attacker_state)
        (QueryIndexChallenge j (PState (query_states ! j)))
        (raws ! j)"
    by (rule trace_composition_absorbed_query_relation_bounded_activeI[
      OF map_bound clean no_initial prefix_ext query_start_ext
        prefix_selector no_trace_merkle no_composition_merkle
        conjunct1[OF conjunct2[OF chains]]
        conjunct2[OF conjunct2[OF chains]]])
      (use shape outcome_props raws_in j_bound lookup_final_raw in auto)
  have inactive_initial:
      "\<not> hash_state_relation_active
        (trace_composition_absorbed_query_relation_bounded
          (ro_checked_staged_transcript_hash_query_budget_for budgets))
        (HashMap adversary_initial_state)
        (QueryIndexChallenge j (PState (query_states ! j)))
        (raws ! j)"
    unfolding hash_state_relation_active_def adversary_initial_state_def
    by simp
  show ?thesis
    unfolding hash_state_relation_transition_def
    using active inactive_initial by blast
qed


definition ro_checked_staged_trace_composition_clean_composition_prefix_target_hit
where
  "ro_checked_staged_trace_composition_clean_composition_prefix_target_hit
      out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some
        ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<Rightarrow>
        \<not> hash_map_output_collision attacker_state \<and>
        hash_map_new_output_hit
          (ro_actual_query_composition_prefix_targets
            (ro_query_head_data data) query_start)
          query_start attacker_state)"


definition ro_checked_staged_trace_composition_prequery_side_event
  :: "staged_budgets \<Rightarrow>
      (((('f \<times> 'f list \<times> 'f) \<times> 'f protocol_channel) \<times>
        'f staged_proof_data \<times> 'f protocol_channel \<times>
        'f list \<times> 'f protocol_channel list) \<times> 'f protocol_channel) option \<Rightarrow>
      bool"
where
  "ro_checked_staged_trace_composition_prequery_side_event budgets out \<longleftrightarrow>
    final_hash_collision_event out \<or>
    hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state out \<or>
    ro_checked_staged_first_root_prefix_merkle_target_hit out \<or>
    ro_checked_staged_trace_composition_clean_composition_prefix_target_hit
      out \<or>
    hash_state_relation_transition_event
      (trace_composition_absorbed_query_relation_bounded
        (ro_checked_staged_transcript_hash_query_budget_for budgets))
      (HashMap adversary_initial_state) out"


lemma ro_checked_staged_trace_composition_good_prequery_some_imp_side_event:
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
    and prequery:
      "ro_query_head_dependent_query_start_prequery_hit
        ro_actual_query_trace_composition_good_query_lists
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
  shows
    "ro_checked_staged_trace_composition_prequery_side_event budgets
      (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
        attacker_state)))"
proof (cases "hash_map_output_collision attacker_state")
  case True
  then show ?thesis
    unfolding ro_checked_staged_trace_composition_prequery_side_event_def
      final_hash_collision_event_def
    by simp
next
  case clean: False
  show ?thesis
  proof (cases
      "PState adversary_initial_state \<in>
        hash_map_output_values attacker_state")
    case True
    then obtain x where final_lookup:
        "fmlookup (HashMap attacker_state) x =
          Some (PState adversary_initial_state)"
      unfolding hash_map_output_values_def by blast
    have initial_lookup:
        "fmlookup (HashMap adversary_initial_state) x = None"
      unfolding adversary_initial_state_def by simp
    have initial_hit:
        "hash_map_new_output_hit {PState adversary_initial_state}
          adversary_initial_state attacker_state"
      unfolding hash_map_new_output_hit_def
      using initial_lookup final_lookup by blast
    then show ?thesis
      unfolding ro_checked_staged_trace_composition_prequery_side_event_def
        hash_new_output_hit_event_def
      by simp
  next
    case no_initial: False
    show ?thesis
    proof (cases
        "hash_map_new_output_hit
          (first_trace_fri_root_prefix_merkle_targets prefix prefix_state)
          prefix_state attacker_state")
      case True
      then show ?thesis
        unfolding
          ro_checked_staged_trace_composition_prequery_side_event_def
          ro_checked_staged_first_root_prefix_merkle_target_hit_def
        by simp
    next
      case no_trace_merkle: False
      show ?thesis
      proof (cases
          "hash_map_new_output_hit
            (ro_actual_query_composition_prefix_targets
              (ro_query_head_data data) query_start)
            query_start attacker_state")
        case True
        then show ?thesis
          unfolding
            ro_checked_staged_trace_composition_prequery_side_event_def
            ro_checked_staged_trace_composition_clean_composition_prefix_target_hit_def
          using clean by simp
      next
        case no_composition_merkle: False
        have relation:
            "hash_state_relation_transition
              (trace_composition_absorbed_query_relation_bounded
                (ro_checked_staged_transcript_hash_query_budget_for budgets))
              (HashMap adversary_initial_state)
              (HashMap attacker_state)"
          by (rule
            trace_composition_prequery_good_imp_budgeted_relation_transition[
              OF wf controlled nonempty outcome prequery clean no_initial
                no_trace_merkle no_composition_merkle])
        then show ?thesis
          unfolding
            ro_checked_staged_trace_composition_prequery_side_event_def
            hash_state_relation_transition_event_def
          by simp
      qed
    qed
  qed
qed


lemma ro_checked_staged_trace_composition_good_prequery_imp_side_event:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
    and support:
      "out \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    and prequery:
      "ro_query_head_dependent_query_start_prequery_hit
        ro_actual_query_trace_composition_good_query_lists out"
  shows
    "ro_checked_staged_trace_composition_prequery_side_event budgets out"
proof (cases out)
  case None
  then show ?thesis
    using prequery
    unfolding ro_query_head_dependent_query_start_prequery_hit_def
    by simp
next
  case (Some packed)
  obtain prefix prefix_state data query_start raws query_states
      attacker_state where packed_eq:
      "packed =
        (((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)"
    by (cases packed) (auto split: prod.splits)
  have outcome:
      "Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)) \<in>
        set_dist
          (execute
            (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
              A)
            adversary_initial_state)"
    using support unfolding Some packed_eq .
  have prequery':
      "ro_query_head_dependent_query_start_prequery_hit
        ro_actual_query_trace_composition_good_query_lists
        (Some ((((prefix, prefix_state), data, query_start, raws, query_states),
          attacker_state)))"
    using prequery unfolding Some packed_eq .
  show ?thesis
    unfolding Some packed_eq
    by (rule
      ro_checked_staged_trace_composition_good_prequery_some_imp_side_event[
        OF wf controlled nonempty outcome prequery'])
qed


lemma wp_event_bind_output_state_dependent_new_output_bound_conditional:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes none: "\<not> E None"
    and event_imp:
      "\<And>x t out. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        out \<in> set_dist (execute (k x) t) \<Longrightarrow>
        E out \<Longrightarrow> hash_new_output_hit_event (B x t) t out"
    and budget:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_target_budget (B x t) n (k x)"
    and value_bound:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        (\<exists>out \<in> set_dist (execute (k x) t). E out) \<Longrightarrow>
        hash_target_budget_value (B x t) n \<le> C"
  shows "wp_event (m \<bind> k) E s \<le> C"
proof (rule wp_event_bind_bound_by_cont[
    where Q=E and m=m and k=k and s=s and C=C])
  show "\<not> E None" by (rule none)
next
  fix x t
  assume head: "Some (x, t) \<in> set_dist (execute m s)"
  show "wp_event (k x) E t \<le> C"
  proof (cases "\<exists>out \<in> set_dist (execute (k x) t). E out")
    case False
    have
        "wp_event (k x) E t \<le> wp_event (k x) (\<lambda>out. False) t"
    proof (rule wp_event_mono_on_support)
      fix out
      assume support: "out \<in> set_dist (execute (k x) t)"
        and event: "E out"
      then show False using False by blast
    qed
    also have "... = 0" by simp
    also have "... \<le> C" by simp
    finally show ?thesis .
  next
    case True
    have
        "wp_event (k x) E t \<le>
          wp_event (k x)
            (hash_new_output_hit_event (B x t) t) t"
      by (rule wp_event_mono_on_support)
        (use head event_imp in blast)
    also have "... \<le> hash_target_budget_value (B x t) n"
      using budget[OF head] unfolding hash_target_budget_def by blast
    also have "... \<le> C"
      by (rule value_bound[OF head True])
    finally show ?thesis .
  qed
qed


lemma ro_actual_query_composition_prefix_targets_card_bound:
  "card
      (ro_actual_query_composition_prefix_targets
        (ro_query_head_data data) query_start)
    \<le> 1 + 2 * card (fmdom' (HashMap query_start))"
proof (cases "staged_composition_fri_roots data = []")
  case True
  then show ?thesis
    unfolding ro_actual_query_composition_prefix_targets_def
      ro_query_head_data_def
    by simp
next
  case False
  have
      "card
        (merkle_prefix_path_targets
          {hd (staged_composition_fri_roots data)} query_start)
      \<le> card {hd (staged_composition_fri_roots data)} +
        2 * card (fmdom' (HashMap query_start))"
    by (rule card_merkle_prefix_path_targets_le) simp
  also have "... \<le> 1 + 2 * card (fmdom' (HashMap query_start))"
    by simp
  finally show ?thesis
    using False
    unfolding ro_actual_query_composition_prefix_targets_def
      ro_query_head_data_def
    by simp
qed


definition ro_checked_staged_trace_composition_prefix_target_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_trace_composition_prefix_target_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets;
         tail =
           sum_list (query_opening_budgets budgets) + rounds +
             rounds * ro_checked_query_round_transcript_bound
     in nnreal (tail * (1 + 2 * q)) / nnreal size)"


lemma wp_ro_checked_staged_trace_composition_prefix_target_hit_bound:
  assumes nonempty: "0 < ceil_log clength"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      ro_checked_staged_trace_composition_clean_composition_prefix_target_hit
      adversary_initial_state
    \<le> ro_checked_staged_trace_composition_prefix_target_error budgets"
proof -
  let ?M = "ro_checked_staged_first_root_query_head_program A"
  let ?K =
    "\<lambda>((prefix, prefix_state), data, query_start).
      ro_checked_staged_query_program_with_witnesses A
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)
          query_start 0 rounds \<bind>
        (\<lambda>(raws, query_states, query_chunks).
          return
            (((prefix, prefix_state),
              data\<lparr>staged_query_chunks := query_chunks\<rparr>,
              query_start, raws, query_states)))"
  let ?E =
    "ro_checked_staged_trace_composition_clean_composition_prefix_target_hit"
  let ?B =
    "\<lambda>((prefix, prefix_state), data, query_start) t.
      ro_actual_query_composition_prefix_targets
        (ro_query_head_data data) query_start"
  let ?tail =
    "sum_list (query_opening_budgets budgets) + rounds +
      rounds * ro_checked_query_round_transcript_bound"
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  have decomposition:
      "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
          A =
        ?M \<bind> ?K"
    unfolding
      ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_def
    by (simp add: split_def)
  show ?thesis
    unfolding decomposition
  proof (rule
      wp_event_bind_output_state_dependent_new_output_bound_conditional[
        where B="?B" and n="?tail" and
          C="ro_checked_staged_trace_composition_prefix_target_error budgets"])
    show "\<not> ?E None"
      unfolding
        ro_checked_staged_trace_composition_clean_composition_prefix_target_hit_def
      by simp
  next
    fix x t out
    assume head:
        "Some (x, t) \<in> set_dist (execute ?M adversary_initial_state)"
      and tail_support: "out \<in> set_dist (execute (?K x) t)"
      and event: "?E out"
    obtain prefix prefix_state data query_start where x_eq:
        "x = ((prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    have state_eq: "t = query_start"
      using head
      unfolding x_eq ro_checked_staged_first_root_query_head_program_def
      by (auto elim!: set_dist_bindE split: prod.splits)
    show "hash_new_output_hit_event (?B x t) t out"
      using event tail_support
      unfolding x_eq state_eq
        ro_checked_staged_trace_composition_clean_composition_prefix_target_hit_def
        hash_new_output_hit_event_def
      by (cases out)
        (auto elim!: set_dist_bindE split: prod.splits)
  next
    fix x t
    assume head:
      "Some (x, t) \<in> set_dist (execute ?M adversary_initial_state)"
    obtain prefix prefix_state data query_start where x_eq:
        "x = ((prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    have lengths:
        "length (staged_trace_fri_roots data) = ceil_log clength \<and>
          length (staged_composition_fri_roots data) \<le>
            ceil_log (maxDegree + 1)"
      using
        ro_checked_staged_first_root_query_head_program_output_lengths[
          OF nonempty head[unfolded x_eq]]
      by blast
    have query_target:
        "hash_target_program
          (ro_actual_query_composition_prefix_targets
            (ro_query_head_data data) query_start)
          ?tail
          (ro_checked_staged_query_program_with_witnesses A
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)
            query_start 0 rounds)"
      by (rule
        hash_target_program_ro_checked_staged_query_program_with_witnesses_closed[
          OF wf controlled conjunct1[OF lengths] conjunct2[OF lengths]])
    have program_explicit:
        "hash_target_program
          (ro_actual_query_composition_prefix_targets
            (ro_query_head_data data) query_start)
          (?tail + 0)
          (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data)
              query_start 0 rounds \<bind>
            (\<lambda>(raws, query_states, query_chunks).
              return
                ((prefix, prefix_state),
                  data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                  query_start, raws, query_states)))"
      apply (rule hash_target_program_bind[OF query_target])
      by (auto simp: hash_target_program_return split: prod.splits)
    have budget_explicit:
        "hash_target_budget
          (ro_actual_query_composition_prefix_targets
            (ro_query_head_data data) query_start)
          ?tail
          (ro_checked_staged_query_program_with_witnesses A
              (staged_trace_fri_roots data)
              (staged_composition_fri_roots data)
              query_start 0 rounds \<bind>
            (\<lambda>(raws, query_states, query_chunks).
              return
                ((prefix, prefix_state),
                  data\<lparr>staged_query_chunks := query_chunks\<rparr>,
                  query_start, raws, query_states)))"
      by (rule hash_target_program_budget)
        (use program_explicit in simp)
    show "hash_target_budget (?B x t) ?tail (?K x)"
      using budget_explicit
      unfolding x_eq
      by simp
  next
    fix x t
    assume head:
        "Some (x, t) \<in> set_dist (execute ?M adversary_initial_state)"
      and witness:
        "\<exists>out \<in> set_dist (execute (?K x) t). ?E out"
    obtain prefix prefix_state data query_start where x_eq:
        "x = ((prefix, prefix_state), data, query_start)"
      by (cases x) (auto split: prod.splits)
    from witness obtain out where
      tail_support: "out \<in> set_dist (execute (?K x) t)"
      and event: "?E out"
      by blast
    from event obtain packed attacker_state where out_eq:
        "out = Some (packed, attacker_state)"
      and clean: "\<not> hash_map_output_collision attacker_state"
      unfolding
        ro_checked_staged_trace_composition_clean_composition_prefix_target_hit_def
      by (cases out) (auto split: prod.splits)
    obtain prefix' prefix_state' data' query_start' raws query_states
        where packed_eq:
        "packed =
          ((prefix', prefix_state'), data', query_start', raws, query_states)"
      by (cases packed) (auto split: prod.splits)
    have full_support:
        "Some
          (((prefix', prefix_state'), data', query_start', raws, query_states),
            attacker_state) \<in>
          set_dist
            (execute
              (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
                A)
              adversary_initial_state)"
    proof -
      have bound:
          "out \<in>
            set_dist
              (execute (?M \<bind> ?K) adversary_initial_state)"
        by (rule set_dist_bindI[OF head])
          (rule tail_support)
      show ?thesis
        using bound
        unfolding decomposition out_eq packed_eq
        by simp
    qed
    have outcome_props:
        "query_start' \<le> attacker_state"
      using
        ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_outcome[
          OF wf controlled full_support]
      by blast
    have return_fields:
        "prefix' = prefix \<and> prefix_state' = prefix_state \<and>
          query_start' = query_start \<and>
          ro_query_head_data data' = ro_query_head_data data"
      using tail_support
      unfolding x_eq out_eq packed_eq
      by (auto elim!: set_dist_bindE split: prod.splits)
    have query_start_ext: "query_start \<le> attacker_state"
      using outcome_props return_fields by simp
    have map_bound:
        "card (fmdom' (HashMap attacker_state)) \<le> ?q"
      by (rule
        ro_checked_staged_transcript_program_with_first_root_map_domain_bound[
          OF wf controlled nonempty full_support clean])
    have dom_subset:
        "fmdom' (HashMap query_start) \<subseteq>
          fmdom' (HashMap attacker_state)"
    proof
      fix key
      assume key_old: "key \<in> fmdom' (HashMap query_start)"
      then obtain v where lookup_old:
          "fmlookup (HashMap query_start) key = Some v"
        by (auto simp: fmlookup_dom'_iff)
      have extension:
          "fmlookup (HashMap query_start) key = None \<or>
            fmlookup (HashMap query_start) key =
              fmlookup (HashMap attacker_state) key"
        using query_start_ext
        unfolding less_eq_hash_ext_def less_eq_fmap_def
        by blast
      have lookup_new:
          "fmlookup (HashMap attacker_state) key = Some v"
        using extension lookup_old by auto
      show "key \<in> fmdom' (HashMap attacker_state)"
        using lookup_new by (simp add: fmlookup_dom'_iff)
    qed
    have domain_start:
        "card (fmdom' (HashMap query_start)) \<le> ?q"
    proof -
      have
          "card (fmdom' (HashMap query_start)) \<le>
            card (fmdom' (HashMap attacker_state))"
        by (rule card_mono[OF finite_fmdom' dom_subset])
      then show ?thesis using map_bound by simp
    qed
    have target_card:
        "card (?B x t) \<le> 1 + 2 * ?q"
    proof -
      have
          "card
            (ro_actual_query_composition_prefix_targets
              (ro_query_head_data data) query_start)
          \<le> 1 + 2 * card (fmdom' (HashMap query_start))"
        by (rule ro_actual_query_composition_prefix_targets_card_bound)
      also have "... \<le> 1 + 2 * ?q"
        using domain_start by simp
      finally show ?thesis
        unfolding x_eq
        by simp
    qed
    show
        "hash_target_budget_value (?B x t) ?tail \<le>
          ro_checked_staged_trace_composition_prefix_target_error budgets"
      unfolding hash_target_budget_value_def
        ro_checked_staged_trace_composition_prefix_target_error_def Let_def
      apply (rule nnreal_nat_divide_right_mono)
      using target_card
      by (rule mult_left_mono) simp
  
  qed
qed



definition ro_checked_staged_trace_composition_good_prequery_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_trace_composition_good_prequery_error budgets =
    (let q = ro_checked_staged_transcript_hash_query_budget_for budgets
     in hash_collision_budget_value 0 q +
       nnreal q / nnreal size +
       ro_checked_staged_first_root_prefix_merkle_target_error budgets +
       ro_checked_staged_trace_composition_prefix_target_error budgets +
       nnreal
         (q *
           (query_raw_preimage_card_envelope
               trace_composition_query_index_bound +
             (5 * q + 2))) /
         nnreal size)"


lemma wp_ro_checked_staged_trace_composition_good_prequery_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
        A)
      (ro_query_head_dependent_query_start_prequery_hit
        ro_actual_query_trace_composition_good_query_lists)
      adversary_initial_state
    \<le> ro_checked_staged_trace_composition_good_prequery_error budgets"
proof -
  let ?M =
    "ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A"
  let ?Prequery =
    "ro_query_head_dependent_query_start_prequery_hit
      ro_actual_query_trace_composition_good_query_lists"
  let ?Collision = "final_hash_collision_event"
  let ?Initial =
    "hash_new_output_hit_event {PState adversary_initial_state}
      adversary_initial_state"
  let ?TraceTarget =
    "ro_checked_staged_first_root_prefix_merkle_target_hit"
  let ?CompositionTarget =
    "ro_checked_staged_trace_composition_clean_composition_prefix_target_hit"
  let ?q = "ro_checked_staged_transcript_hash_query_budget_for budgets"
  let ?Relation =
    "hash_state_relation_transition_event
      (trace_composition_absorbed_query_relation_bounded ?q)
      (HashMap adversary_initial_state)"
  have event_le:
      "wp_event ?M ?Prequery adversary_initial_state \<le>
        wp_event ?M
          (ro_checked_staged_trace_composition_prequery_side_event budgets)
          adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in> set_dist (execute ?M adversary_initial_state)"
      and prequery: "?Prequery out"
    show
        "ro_checked_staged_trace_composition_prequery_side_event budgets out"
      by (rule
        ro_checked_staged_trace_composition_good_prequery_imp_side_event[
          OF wf controlled nonempty support prequery])
  qed
  have union4:
      "wp_event ?M
          (ro_checked_staged_trace_composition_prequery_side_event budgets)
          adversary_initial_state
        \<le> wp_event ?M ?Collision adversary_initial_state +
          wp_event ?M ?Initial adversary_initial_state +
          wp_event ?M ?TraceTarget adversary_initial_state +
          wp_event ?M
            (\<lambda>out. ?CompositionTarget out \<or> ?Relation out)
            adversary_initial_state"
    unfolding ro_checked_staged_trace_composition_prequery_side_event_def
    by (rule wp_event_union_bound4)
  have union2:
      "wp_event ?M
          (\<lambda>out. ?CompositionTarget out \<or> ?Relation out)
          adversary_initial_state
        \<le> wp_event ?M ?CompositionTarget adversary_initial_state +
          wp_event ?M ?Relation adversary_initial_state"
    by (rule wp_event_union_bound)
  have union:
      "wp_event ?M
          (ro_checked_staged_trace_composition_prequery_side_event budgets)
          adversary_initial_state
        \<le> wp_event ?M ?Collision adversary_initial_state +
          wp_event ?M ?Initial adversary_initial_state +
          wp_event ?M ?TraceTarget adversary_initial_state +
          wp_event ?M ?CompositionTarget adversary_initial_state +
          wp_event ?M ?Relation adversary_initial_state"
    apply (rule order_trans[OF union4])
    using union2
    by (simp add: add_mono add.assoc)
  have collision:
      "wp_event ?M ?Collision adversary_initial_state \<le>
        hash_collision_budget_value 0 ?q"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_collision_bound[
        OF wf controlled nonempty])
  have initial:
      "wp_event ?M ?Initial adversary_initial_state \<le>
        nnreal ?q / nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_initial_target_bound[
        OF wf controlled nonempty])
  have trace_target:
      "wp_event ?M ?TraceTarget adversary_initial_state \<le>
        ro_checked_staged_first_root_prefix_merkle_target_error budgets"
    by (rule
      wp_ro_checked_staged_first_root_prefix_merkle_target_hit_bound[
        OF nonempty wf controlled])
  have composition_target:
      "wp_event ?M ?CompositionTarget adversary_initial_state \<le>
        ro_checked_staged_trace_composition_prefix_target_error budgets"
    by (rule
      wp_ro_checked_staged_trace_composition_prefix_target_hit_bound[
        OF nonempty wf controlled])
  have relation:
      "wp_event ?M ?Relation adversary_initial_state \<le>
        nnreal
          (?q *
            (query_raw_preimage_card_envelope
                trace_composition_query_index_bound +
              (5 * ?q + 2))) /
          nnreal size"
    by (rule
      wp_ro_checked_staged_transcript_program_with_first_root_and_query_witnesses_trace_composition_bounded_relation[
        OF wf controlled nonempty])
  have closed:
      "wp_event ?M
          (ro_checked_staged_trace_composition_prequery_side_event budgets)
          adversary_initial_state
        \<le> ro_checked_staged_trace_composition_good_prequery_error budgets"
    apply (rule order_trans[OF union])
    unfolding
      ro_checked_staged_trace_composition_good_prequery_error_def Let_def
    apply (intro add_mono)
        apply (rule collision)
       apply (rule initial)
      apply (rule trace_target)
     apply (rule composition_target)
    apply (rule relation)
    done
  show ?thesis
    by (rule order_trans[OF event_le closed])
qed


definition ro_checked_staged_trace_composition_good_actual_query_error
  :: "staged_budgets \<Rightarrow> prob"
where
  "ro_checked_staged_trace_composition_good_actual_query_error budgets =
    nnreal (trace_composition_query_index_bound ^ rounds) *
      (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds +
    ro_checked_staged_trace_composition_good_prequery_error budgets +
    hash_relation_budget_value
      (rounds *
        (query_raw_preimage_card_envelope
          trace_composition_query_index_bound))
      (sum_list (query_opening_budgets budgets) + rounds +
        rounds * ro_checked_query_round_transcript_bound)"


lemma wp_ro_checked_staged_trace_composition_good_actual_query_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and nonempty: "0 < ceil_log clength"
  shows
    "wp_event
      (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
      (ro_query_head_dependent_actual_query_index_list_hit
        ro_actual_query_trace_composition_good_query_lists)
      adversary_initial_state
    \<le> ro_checked_staged_trace_composition_good_actual_query_error budgets"
proof -
  have split:
      "wp_event
        (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses A)
        (ro_query_head_dependent_actual_query_index_list_hit
          ro_actual_query_trace_composition_good_query_lists)
        adversary_initial_state
      \<le>
        nnreal (trace_composition_query_index_bound ^ rounds) *
          (nnreal (query_raw_preimage_card_envelope 1) / nnreal size) ^ rounds +
        wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_query_head_dependent_query_start_prequery_hit
            ro_actual_query_trace_composition_good_query_lists)
          adversary_initial_state +
        hash_relation_budget_value
          (rounds *
            (query_raw_preimage_card_envelope
              trace_composition_query_index_bound))
          (sum_list (query_opening_budgets budgets) + rounds +
            rounds * ro_checked_query_round_transcript_bound)"
    by (rule
      wp_ro_actual_query_trace_composition_good_actual_query_split_bound[
        OF wf controlled nonempty])
  have prequery:
      "wp_event
          (ro_checked_staged_transcript_program_with_first_root_and_query_witnesses
            A)
          (ro_query_head_dependent_query_start_prequery_hit
            ro_actual_query_trace_composition_good_query_lists)
          adversary_initial_state
        \<le> ro_checked_staged_trace_composition_good_prequery_error budgets"
    by (rule
      wp_ro_checked_staged_trace_composition_good_prequery_bound[
        OF wf controlled nonempty])
  show ?thesis
    by (rule order_trans[OF split])
      (use prequery in
        \<open>simp add:
          ro_checked_staged_trace_composition_good_actual_query_error_def
          add_mono\<close>)
qed


end
end
