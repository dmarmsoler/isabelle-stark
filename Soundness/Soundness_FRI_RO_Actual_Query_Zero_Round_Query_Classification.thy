(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Zero_Round_Query_Classification.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Zero_Round_Query_Classification
  imports
    Soundness_FRI_RO_Actual_Query_Zero_Round_Prefix
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Parameter_Bound
begin

text \<open>
  Prefix-fixed classification for the trace-FRI zero-round branch.  The
  initial trace root has already been absorbed through the domain-separated
  random oracle before the remaining header and all query indices.  Therefore
  its prefix conceptual table is fixed without reconstructing a complete table
  from sampled openings.
\<close>

context soundness
begin

definition ro_actual_query_zero_round_trace_table
where
  "ro_actual_query_zero_round_trace_table data prefix_state =
    conceptual_table prefix_state (staged_trace_root data)
      (scale * clength)"

definition ro_actual_query_zero_round_trace_indices
where
  "ro_actual_query_zero_round_trace_indices data prefix_state =
    fri_final_value_agreement_set
      (ro_actual_query_zero_round_trace_table data prefix_state)
      (staged_trace_final data)"

definition ro_actual_query_zero_round_trace_query_lists
where
  "ro_actual_query_zero_round_trace_query_lists data prefix_state =
    query_index_lists_over
      (ro_actual_query_zero_round_trace_indices data prefix_state)"

definition ro_actual_query_zero_round_trace_merkle_targets
where
  "ro_actual_query_zero_round_trace_merkle_targets data prefix_state =
    merkle_prefix_path_targets {staged_trace_root data} prefix_state"

lemma
  partial_authenticated_trace_final_value_prefix_conceptual_agreement_or_target:
  fixes prefix_state final_state :: "'f protocol_channel"
  assumes ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and idx_sample: "idx \<in> query_sample_space"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and trace_table:
      "partial_authenticated_table fr (scale * clength)
        trace_openings final_state"
    and final_value:
      "opening_value (trace_openings ! 0) = final"
  shows
    "idx \<in>
       fri_final_value_agreement_set
         (conceptual_table prefix_state fr (scale * clength)) final \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {fr} prefix_state)
       prefix_state final_state"
proof (cases
    "hash_map_new_output_hit
      (merkle_prefix_path_targets {fr} prefix_state)
      prefix_state final_state")
  case True
  then show ?thesis by simp
next
  case False
  have agrees:
      "table_agrees_with_authenticated_openings
        (conceptual_table prefix_state fr (scale * clength))
        (scale * clength) trace_openings"
    using
      partial_authenticated_table_agrees_with_prefix_conceptual_table_or_prefix_target_hit[
        OF ext clean trace_table]
      False
    by blast
  have trace_nonempty: "trace_openings \<noteq> []"
  proof
    assume empty: "trace_openings = []"
    have "powers_scaled idx = []"
      using trace_indices empty by simp
    then show False
      using powers_pos unfolding powers_scaled_def by simp
  qed
  have head_index:
      "opening_index (trace_openings ! 0) = idx"
  proof -
    have
      "opening_index (trace_openings ! 0) =
        hd (map opening_index trace_openings)"
      using trace_nonempty by (cases trace_openings) simp_all
    also have "... = hd (powers_scaled idx)"
      using trace_indices by simp
    also have "... = idx"
      by (rule powers_scaled_hd)
    finally show ?thesis .
  qed
  have head_in: "trace_openings ! 0 \<in> set trace_openings"
    using trace_nonempty by (cases trace_openings) simp_all
  have table_value:
      "conceptual_table prefix_state fr (scale * clength) ! idx =
        opening_value (trace_openings ! 0)"
    using agrees head_in head_index
    unfolding table_agrees_with_authenticated_openings_def
    by blast
  have idx_bound:
      "idx <
        length (conceptual_table prefix_state fr (scale * clength))"
    using agrees head_in head_index
    unfolding table_agrees_with_authenticated_openings_def
    by auto
  show ?thesis
    unfolding fri_final_value_agreement_set_def
    using idx_sample idx_bound table_value final_value False by simp
qed

lemma
  partial_authenticated_trace_final_value_query_list_prefix_conceptual_agreement_or_target:
  fixes prefix_state final_state :: "'f protocol_channel"
  assumes query_len: "length query_idxs = rounds"
    and query_sample: "set query_idxs \<subseteq> query_sample_space"
    and ext: "prefix_state \<le> final_state"
    and clean: "\<not> hash_map_output_collision prefix_state"
    and evidence:
      "\<And>i. i < length query_idxs \<Longrightarrow>
        map opening_index (trace_openings_at i) =
          powers_scaled (query_idxs ! i) \<and>
        partial_authenticated_table fr (scale * clength)
          (trace_openings_at i) final_state \<and>
        opening_value (trace_openings_at i ! 0) = final"
  shows
    "query_idxs \<in>
       query_index_lists_over
         (fri_final_value_agreement_set
           (conceptual_table prefix_state fr (scale * clength)) final) \<or>
     hash_map_new_output_hit
       (merkle_prefix_path_targets {fr} prefix_state)
       prefix_state final_state"
proof (cases
    "hash_map_new_output_hit
      (merkle_prefix_path_targets {fr} prefix_state)
      prefix_state final_state")
  case True
  then show ?thesis by simp
next
  case False
  have subset:
      "set query_idxs \<subseteq>
        fri_final_value_agreement_set
          (conceptual_table prefix_state fr (scale * clength)) final"
  proof
    fix idx
    assume idx_in: "idx \<in> set query_idxs"
    then obtain i where i_bound: "i < length query_idxs"
      and idx_eq: "query_idxs ! i = idx"
      by (metis in_set_conv_nth)
    have ev:
        "map opening_index (trace_openings_at i) =
            powers_scaled (query_idxs ! i) \<and>
         partial_authenticated_table fr (scale * clength)
            (trace_openings_at i) final_state \<and>
         opening_value (trace_openings_at i ! 0) = final"
      by (rule evidence[OF i_bound])
    have idx_sample: "query_idxs ! i \<in> query_sample_space"
      using query_sample nth_mem[OF i_bound] by blast
    have
      "query_idxs ! i \<in>
         fri_final_value_agreement_set
           (conceptual_table prefix_state fr (scale * clength)) final \<or>
       hash_map_new_output_hit
         (merkle_prefix_path_targets {fr} prefix_state)
         prefix_state final_state"
      by (rule
          partial_authenticated_trace_final_value_prefix_conceptual_agreement_or_target[
            where trace_openings="trace_openings_at i",
            OF ext clean idx_sample])
        (use ev in simp_all)
    then show "idx \<in>
        fri_final_value_agreement_set
          (conceptual_table prefix_state fr (scale * clength)) final"
      using False idx_eq by blast
  qed
  have
      "query_idxs \<in>
        query_index_lists_over
          (fri_final_value_agreement_set
            (conceptual_table prefix_state fr (scale * clength)) final)"
    unfolding query_index_lists_over_def
    using query_len subset by simp
  then show ?thesis by simp
qed

lemma
  ro_absorb_checked_staged_zero_round_actual_query_agreement_or_target:
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
    "map (\<lambda>raw. index (to_nat raw)) raws \<in>
       ro_actual_query_zero_round_trace_query_lists data prefix_state \<or>
     hash_map_new_output_hit
       (ro_actual_query_zero_round_trace_merkle_targets data prefix_state)
       prefix_state final_state"
proof -
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
    and f_fl_zero: "f_fl = []"
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
    and query_counter: "PQueryCounter query_start = 0"
    and verifier_transcript:
      "PTranscript verifier_query_state = List.concat query_chunks @ []"
    and raws_rounds: "length raws = rounds"
    and query_chunks_rounds: "length query_chunks = rounds"
    and raw_bound:
      "\<forall>raw \<in> set raws. index (to_nat raw) < clength * scale"
    .

  have query_bound:
      "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have authenticated:
      "\<exists>trace_openings_at.
        verifier_query_state \<le> final_state \<and>
        length raws = rounds \<and>
        length query_states = rounds \<and>
        length query_chunks = rounds \<and>
        (\<forall>j < rounds.
          map opening_index (trace_openings_at j) =
            powers_scaled (index (to_nat (raws ! j))) \<and>
          partial_authenticated_table fr (scale * clength)
            (trace_openings_at j) final_state \<and>
          opening_value (trace_openings_at j ! 0) = f_final)"
    by (rule
        ro_checked_staged_query_program_with_witnesses_verifier_authenticated_trace_openings_zero[
          OF controlled query_bound query_out attacker_verifier_ext
            verifier_builder_state counter_eq verifier_transcript f_fl_zero])
      (use trace_roots_eq composition_roots_eq data_eq verifier_query_out in
        simp_all)
  then obtain trace_openings_at where
    verifier_final_ext: "verifier_query_state \<le> final_state"
    and authenticated_lengths:
      "length raws = rounds \<and>
       length query_states = rounds \<and>
       length query_chunks = rounds"
    and authenticated_evidence:
      "\<forall>j < rounds.
        map opening_index (trace_openings_at j) =
          powers_scaled (index (to_nat (raws ! j))) \<and>
        partial_authenticated_table fr (scale * clength)
          (trace_openings_at j) final_state \<and>
        opening_value (trace_openings_at j ! 0) = f_final"
    by blast

  have prefix_final_ext: "prefix_state \<le> final_state"
    using prefix_query_ext query_attacker_ext attacker_verifier_ext
      verifier_final_ext
    by (meson hash_ext_trans)
  have prefix_clean: "\<not> hash_map_output_collision prefix_state"
  proof
    assume collision: "hash_map_output_collision prefix_state"
    have "hash_map_output_collision final_state"
      by (rule hash_map_output_collision_mono[
            OF collision prefix_final_ext])
    then show False
      using clean by contradiction
  qed

  let ?query_idxs = "map (\<lambda>raw. index (to_nat raw)) raws"
  have query_len: "length ?query_idxs = rounds"
    using authenticated_lengths by simp
  have query_sample: "set ?query_idxs \<subseteq> query_sample_space"
    unfolding query_sample_space_def
    using index_less_query_sample_space by auto
  have conceptual_or_target:
      "?query_idxs \<in>
         query_index_lists_over
           (fri_final_value_agreement_set
             (conceptual_table prefix_state fr (scale * clength))
             f_final) \<or>
       hash_map_new_output_hit
         (merkle_prefix_path_targets {fr} prefix_state)
         prefix_state final_state"
  proof (rule
      partial_authenticated_trace_final_value_query_list_prefix_conceptual_agreement_or_target[
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
       opening_value (trace_openings_at i ! 0) = f_final"
      using authenticated_evidence[rule_format, OF i_round] i_raw
      by simp
  qed
  show ?thesis
    using conceptual_or_target fr_eq trace_final_eq
    unfolding ro_actual_query_zero_round_trace_query_lists_def
      ro_actual_query_zero_round_trace_indices_def
      ro_actual_query_zero_round_trace_table_def
      ro_actual_query_zero_round_trace_merkle_targets_def
    by simp
qed

definition ro_actual_query_zero_round_bad_query_lists
where
  "ro_actual_query_zero_round_bad_query_lists
      prefix prefix_state data query_start =
    (if
      \<not> trace_table_low_degree
          (ro_actual_query_zero_round_trace_table data prefix_state)
     then ro_actual_query_zero_round_trace_query_lists data prefix_state
     else {})"

lemma ceil_log_clength_zero_imp_clength_one:
  assumes zero: "ceil_log clength = 0"
  shows "clength = 1"
proof -
  have "clength \<le> 1"
    using zero unfolding ceil_log_def
    by (cases "clength \<le> 1") simp_all
  then show ?thesis
    using clength_pos by simp
qed

lemma ceil_log_clength_zero_imp_powers_one:
  assumes zero: "ceil_log clength = 0"
  shows "powers = 1"
  using powers_pos powers_le_clength
    ceil_log_clength_zero_imp_clength_one[OF zero]
  by simp

lemma zero_round_trace_table_len_query_sample_space:
  assumes zero: "ceil_log clength = 0"
  shows
    "length (ro_actual_query_zero_round_trace_table data prefix_state) =
      query_sample_space_size"
  unfolding ro_actual_query_zero_round_trace_table_def
    query_sample_space_size_def
  using ceil_log_clength_zero_imp_clength_one[OF zero]
    ceil_log_clength_zero_imp_powers_one[OF zero]
  by simp

lemma zero_round_trace_table_final_consistent_imp_low_degree:
  assumes zero: "ceil_log clength = 0"
    and final:
      "fri_final_constant_consistent
        (ro_actual_query_zero_round_trace_table data prefix_state)
        (staged_trace_final data)"
  shows
    "trace_table_low_degree
      (ro_actual_query_zero_round_trace_table data prefix_state)"
proof -
  let ?table =
    "ro_actual_query_zero_round_trace_table data prefix_state"
  have clength_one: "clength = 1"
    by (rule ceil_log_clength_zero_imp_clength_one[OF zero])
  have table_len: "length ?table = length eval_domain"
    unfolding ro_actual_query_zero_round_trace_table_def
    using eval_domain_length by (simp add: mult.commute)
  have table_eq:
      "?table =
        map (poly [:staged_trace_final data:]) eval_domain"
  proof (rule nth_equalityI)
    show
      "length ?table =
        length (map (poly [:staged_trace_final data:]) eval_domain)"
      using table_len by simp
  next
    fix i
    assume i_bound: "i < length ?table"
    have "?table ! i = staged_trace_final data"
      by (rule fri_final_constant_consistent_nth[OF final i_bound])
    then show
      "?table ! i =
        map (poly [:staged_trace_final data:]) eval_domain ! i"
      using i_bound table_len by simp
  qed
  show ?thesis
    unfolding trace_table_low_degree_def
    by (intro exI[of _ "[:staged_trace_final data:]"] conjI)
      (use clength_one table_eq in simp_all)
qed

lemma zero_round_trace_indices_card_lt_if_not_low_degree:
  assumes zero: "ceil_log clength = 0"
    and not_low:
      "\<not> trace_table_low_degree
        (ro_actual_query_zero_round_trace_table data prefix_state)"
  shows
    "card (ro_actual_query_zero_round_trace_indices data prefix_state) <
      query_sample_space_size"
proof -
  have not_final:
      "\<not> fri_final_constant_consistent
        (ro_actual_query_zero_round_trace_table data prefix_state)
        (staged_trace_final data)"
    using zero_round_trace_table_final_consistent_imp_low_degree[
      OF zero] not_low
    by blast
  show ?thesis
    unfolding ro_actual_query_zero_round_trace_indices_def
    by (rule
        fri_final_value_agreement_set_card_lt_if_not_constant_whole_sample[
          OF zero_round_trace_table_len_query_sample_space[OF zero]
            not_final])
qed

lemma ro_actual_query_zero_round_trace_indices_subset:
  "ro_actual_query_zero_round_trace_indices data prefix_state
    \<subseteq> query_sample_space"
  unfolding ro_actual_query_zero_round_trace_indices_def
  by (rule fri_final_value_agreement_set_subset)

lemma ro_actual_query_zero_round_bad_query_lists_subset:
  "ro_actual_query_zero_round_bad_query_lists
      prefix prefix_state data query_start
    \<subseteq> fri_query_index_list_space"
  unfolding ro_actual_query_zero_round_bad_query_lists_def
    ro_actual_query_zero_round_trace_query_lists_def
  using query_index_lists_over_subset_fri_query_index_list_space[
    OF ro_actual_query_zero_round_trace_indices_subset]
  by auto

lemma ro_actual_query_zero_round_bad_query_lists_card_bound:
  assumes zero: "ceil_log clength = 0"
  shows
    "card
      (ro_actual_query_zero_round_bad_query_lists
        prefix prefix_state data query_start)
      \<le> (query_sample_space_size - 1) ^ rounds"
proof (cases
    "trace_table_low_degree
      (ro_actual_query_zero_round_trace_table data prefix_state)")
  case True
  then show ?thesis
    unfolding ro_actual_query_zero_round_bad_query_lists_def by simp
next
  case False
  have finite:
      "finite (ro_actual_query_zero_round_trace_indices data prefix_state)"
    unfolding ro_actual_query_zero_round_trace_indices_def by simp
  have card_lists:
      "card (ro_actual_query_zero_round_trace_query_lists data prefix_state) =
        card (ro_actual_query_zero_round_trace_indices data prefix_state) ^
          rounds"
    unfolding ro_actual_query_zero_round_trace_query_lists_def
    by (rule card_query_index_lists_over[OF finite])
  have card_indices:
      "card (ro_actual_query_zero_round_trace_indices data prefix_state)
        \<le> query_sample_space_size - 1"
    using zero_round_trace_indices_card_lt_if_not_low_degree[
      OF zero False]
    by simp
  have power:
      "card (ro_actual_query_zero_round_trace_indices data prefix_state) ^
          rounds
        \<le> (query_sample_space_size - 1) ^ rounds"
    by (rule power_mono[OF card_indices]) simp
  show ?thesis
    unfolding ro_actual_query_zero_round_bad_query_lists_def
    using False card_lists power by simp
qed

lemma
  ro_actual_query_zero_round_bad_query_lists_relation_fiber_bound:
  assumes zero: "ceil_log clength = 0"
  shows
    "query_index_raw_list_relation_fiber_bound
      (ro_actual_query_zero_round_bad_query_lists
        prefix prefix_state data query_start)
      \<le> rounds *
        query_raw_preimage_card_envelope
          (query_sample_space_size - 1)"
proof (cases
    "trace_table_low_degree
      (ro_actual_query_zero_round_trace_table data prefix_state)")
  case True
  then show ?thesis
    unfolding ro_actual_query_zero_round_bad_query_lists_def
      query_index_raw_list_relation_fiber_bound_def
      query_index_raw_list_position_values_def
      query_index_raw_list_preimage_def
    by simp
next
  case False
  let ?indices =
    "ro_actual_query_zero_round_trace_indices data prefix_state"
  have base:
      "query_index_raw_list_relation_fiber_bound
        (query_index_lists_over ?indices)
        \<le> rounds * query_raw_preimage_card_envelope (card ?indices)"
    by (rule
        query_index_raw_list_relation_fiber_bound_query_index_lists_over[
          OF ro_actual_query_zero_round_trace_indices_subset])
  have card_indices:
      "card ?indices \<le> query_sample_space_size - 1"
    using zero_round_trace_indices_card_lt_if_not_low_degree[
      OF zero False]
    by simp
  have envelope:
      "query_raw_preimage_card_envelope (card ?indices) \<le>
        query_raw_preimage_card_envelope (query_sample_space_size - 1)"
    by (rule query_raw_preimage_card_envelope_mono[OF card_indices])
  have product:
      "rounds * query_raw_preimage_card_envelope (card ?indices)
        \<le> rounds *
          query_raw_preimage_card_envelope (query_sample_space_size - 1)"
    using envelope by simp
  show ?thesis
    unfolding ro_actual_query_zero_round_bad_query_lists_def
      ro_actual_query_zero_round_trace_query_lists_def
    using False order_trans[OF base product] by simp
qed

lemma ro_actual_query_zero_round_bad_query_lists_position_card_bound:
  assumes zero: "ceil_log clength = 0"
    and i_bound: "i < rounds"
  shows
    "card
      (query_index_raw_list_position_values
        (ro_actual_query_zero_round_bad_query_lists
          prefix prefix_state data query_start)
        i)
      \<le> query_raw_preimage_card_envelope
          (query_sample_space_size - 1)"
proof (cases
    "trace_table_low_degree
      (ro_actual_query_zero_round_trace_table data prefix_state)")
  case True
  then show ?thesis
    unfolding ro_actual_query_zero_round_bad_query_lists_def
      query_index_raw_list_position_values_def
      query_index_raw_list_preimage_def
    by simp
next
  case False
  let ?indices =
    "ro_actual_query_zero_round_trace_indices data prefix_state"
  let ?Q =
    "ro_actual_query_zero_round_bad_query_lists
      prefix prefix_state data query_start"
  have Q_eq: "?Q = query_index_lists_over ?indices"
    unfolding ro_actual_query_zero_round_bad_query_lists_def
      ro_actual_query_zero_round_trace_query_lists_def
    using False by simp
  have subset:
    "query_index_raw_list_position_values ?Q i
      \<subseteq> query_index_raw_preimage ?indices"
    unfolding Q_eq
    by (rule
      query_index_raw_list_position_values_query_index_lists_over_subset[
        OF i_bound])
  have card_le:
    "card (query_index_raw_list_position_values ?Q i)
      \<le> card (query_index_raw_preimage ?indices)"
    by (rule card_mono[OF _ subset]) simp
  have raw_card:
    "card (query_index_raw_preimage ?indices) \<le>
      query_raw_preimage_card_envelope (card ?indices)"
    by (rule card_query_index_raw_preimage_le_query_envelope)
      (rule ro_actual_query_zero_round_trace_indices_subset)
  have indices_bound:
    "card ?indices \<le> query_sample_space_size - 1"
    using zero_round_trace_indices_card_lt_if_not_low_degree[
      OF zero False]
    by simp
  have envelope:
    "query_raw_preimage_card_envelope (card ?indices) \<le>
      query_raw_preimage_card_envelope (query_sample_space_size - 1)"
    by (rule query_raw_preimage_card_envelope_mono[OF indices_bound])
  show ?thesis
    by (rule order_trans[OF card_le])
      (rule order_trans[OF raw_card envelope])
qed


end
end
