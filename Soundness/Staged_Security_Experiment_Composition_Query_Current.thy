(*  Title:      Stark/Staged_Security_Experiment_Composition_Query_Current.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Composition_Query_Current
  imports Staged_Security_Experiment_Composition_Query_Classification
begin

text \<open>
  Current-execution projection for the composition query branch.

  The broader header-supported query witnesses are existential over possible
  verifier executions.  This layer only reasons about openings authenticated in
  the actual sampled verifier final state, so the sampled query lookup is
  available and the event projects to the existing data-state partial-opening
  query event.
\<close>

context soundness
begin

lemma checked_staged_security_experiment_with_query_prefix_data_state_raw_final_lookup:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and outcome:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
  shows
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
proof -
  have head:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    and cont:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive_with_verifier A i
            ((prefix, prefix_state), raw))
          raw_state)"
    using outcome
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
    by (auto elim!: set_dist_bindE)
  have recv:
    "Some (raw, raw_state) \<in>
      set_dist (execute receive_query_index_challenge prefix_state)"
    by (rule checked_staged_query_prefix_receive_with_state_receive_support
        [OF head])
  have raw_lookup:
    "fmlookup (HashMap raw_state)
      (QueryIndexChallenge (PQueryCounter prefix_state) (PState prefix_state)) =
      Some raw"
    using receive_query_index_challenge_outcome[OF recv] by blast
  have data_out:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive A i
            ((prefix, prefix_state), raw))
          raw_state)"
    by (rule
        checked_staged_after_query_prefix_receive_with_verifier_outcome(1)
        [OF cont])
  have verifier_out:
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    by (rule
        checked_staged_after_query_prefix_receive_with_verifier_outcome(2)
        [OF cont])
  have raw_ext_attacker: "raw_state \<le> attacker_state"
    by (rule checked_staged_after_query_prefix_receive_extends
        [OF wf controlled i_bound data_out])
  have attacker_ext_verifier:
    "attacker_state \<le>
      verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)"
  proof -
    have "attacker_state \<le> attacker_state"
      unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    then show ?thesis
      by (rule hash_extends_verifier_state_from_adversary_right)
  qed
  have verifier_ext_final:
    "verifier_state_from_adversary attacker_state
        (staged_proof_transcript data) \<le>
      final_state"
    by (rule verify_monad_hash_extends[OF verifier_out])
  have raw_ext_final: "raw_state \<le> final_state"
    by (rule hash_ext_trans[OF raw_ext_attacker])
      (rule hash_ext_trans[OF attacker_ext_verifier verifier_ext_final])
  have prefix_support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i)
          adversary_initial_state)"
    by (rule checked_staged_query_prefix_receive_with_state_prefix_support
        [OF head])
  have prefix_alignment:
    "PQueryCounter prefix_state = i \<and>
     PState prefix_state =
       state_after_query_chunks
        (staged_query_prefix_start_hash prefix)
        (sqp_query_chunks prefix) i \<and>
     length (sqp_query_chunks prefix) = i"
    by (rule checked_staged_query_prefix_with_state_alignment
        [OF wf controlled i_bound prefix_support])
  from cont obtain chunk chunk_state assert_state record_state suffix_chunks
    where data_eq:
      "data =
        \<lparr>staged_trace_root = sqp_trace_root prefix,
         staged_trace_fri_roots = sqp_trace_fri_roots prefix,
         staged_trace_fri_challenges = sqp_trace_fri_challenges prefix,
         staged_trace_final = sqp_trace_final prefix,
         staged_alphas = sqp_alphas prefix,
         staged_degree = sqp_degree prefix,
         staged_composition_fri_roots = sqp_composition_fri_roots prefix,
         staged_composition_fri_challenges =
           sqp_composition_fri_challenges prefix,
         staged_composition_final = sqp_composition_final prefix,
         staged_query_chunks = sqp_query_chunks prefix @ chunk # suffix_chunks\<rparr>"
    unfolding checked_staged_after_query_prefix_receive_with_verifier_def
      checked_staged_after_query_prefix_receive_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have start_hash_eq:
    "staged_query_start_hash data = staged_query_prefix_start_hash prefix"
    unfolding data_eq staged_query_start_hash_def
      staged_query_prefix_start_hash_def
      staged_composition_fri_start_hash_def
      staged_trace_fri_start_hash_def
    by simp
  have chunks_state_eq:
    "state_after_query_chunks
        (staged_query_start_hash data) (staged_query_chunks data) i =
      state_after_query_chunks
        (staged_query_prefix_start_hash prefix) (sqp_query_chunks prefix) i"
  proof -
    have len_prefix: "length (sqp_query_chunks prefix) = i"
      using prefix_alignment by simp
    have
      "state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i =
        state_after_query_chunks
          (staged_query_prefix_start_hash prefix)
          (sqp_query_chunks prefix @ chunk # suffix_chunks) i"
      using start_hash_eq unfolding data_eq by simp
    also have "... =
        state_after_query_chunks
          (staged_query_prefix_start_hash prefix) (sqp_query_chunks prefix) i"
      by (rule state_after_query_chunks_append_prefix[OF len_prefix])
    finally show ?thesis .
  qed
  have fields:
    "PQueryCounter prefix_state = i"
    "PState prefix_state =
      state_after_query_chunks
        (staged_query_start_hash data) (staged_query_chunks data) i"
    using prefix_alignment chunks_state_eq by simp_all
  have raw_lookup':
    "fmlookup (HashMap raw_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    using raw_lookup fields by simp
  show ?thesis
    by (rule hash_extension_lookup[OF raw_lookup' raw_ext_final])
qed

definition checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
where
  "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i out \<longleftrightarrow>
    (\<exists>trace_openings composition_openings.
      checked_staged_security_with_query_prefix_authenticated_opening_hit
        trace_openings composition_openings i out)"

definition checked_staged_security_with_query_prefix_current_query_partial_opening_hit
where
  "checked_staged_security_with_query_prefix_current_query_partial_opening_hit
      out \<longleftrightarrow>
    (\<exists>i < rounds.
      checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i out)"

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_atI:
  assumes
    "checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_openings composition_openings i out"
  shows
    "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i out"
  using assms
  unfolding
    checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_def
  by blast

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hitI:
  assumes "i < rounds"
    and
      "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i out"
  shows
    "checked_staged_security_with_query_prefix_current_query_partial_opening_hit
      out"
  using assms
  unfolding
      checked_staged_security_with_query_prefix_current_query_partial_opening_hit_def
    by blast

definition staged_query_prefix_prefix_authenticated_opening_target
  :: "'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "staged_query_prefix_prefix_authenticated_opening_target prefix prefix_state =
    {idx \<in> query_sample_space.
      \<exists>(trace_openings :: 'f authenticated_opening list)
        (composition_openings :: 'f authenticated_opening list).
        sqp_composition_fri_roots prefix \<noteq> [] \<and>
        partial_authenticated_table (sqp_trace_root prefix)
          (scale * clength) trace_openings prefix_state \<and>
        partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
          (scale * clength) composition_openings prefix_state \<and>
        partial_query_openings_consistent trace_openings composition_openings
          (sqp_alphas prefix) idx}"

definition staged_query_prefix_prefix_authenticated_trace_indices
  :: "'f staged_query_prefix_data \<Rightarrow> 'f protocol_channel \<Rightarrow> nat set"
where
  "staged_query_prefix_prefix_authenticated_trace_indices prefix prefix_state =
    {idx \<in> query_sample_space.
      \<exists>opn :: 'f authenticated_opening.
        authenticated_opening_in prefix_state opn \<and>
        opening_root opn = sqp_trace_root prefix \<and>
        opening_length opn = scale * clength \<and>
        opening_index opn = idx}"

lemma staged_query_prefix_prefix_authenticated_opening_target_subset:
  "staged_query_prefix_prefix_authenticated_opening_target prefix prefix_state
    \<subseteq> query_sample_space"
  unfolding staged_query_prefix_prefix_authenticated_opening_target_def
  by blast

lemma staged_query_prefix_prefix_authenticated_opening_target_eq_query_sample_space_if_all_indices_witnessed:
  assumes witnessed:
      "\<And>idx. idx \<in> query_sample_space \<Longrightarrow>
        \<exists>trace_openings composition_openings.
          sqp_composition_fri_roots prefix \<noteq> [] \<and>
          partial_authenticated_table (sqp_trace_root prefix)
            (scale * clength) trace_openings prefix_state \<and>
          partial_authenticated_table
            (hd (sqp_composition_fri_roots prefix))
            (scale * clength) composition_openings prefix_state \<and>
          partial_query_openings_consistent trace_openings
            composition_openings (sqp_alphas prefix) idx"
  shows
    "staged_query_prefix_prefix_authenticated_opening_target prefix
      prefix_state = query_sample_space"
proof
  show
    "staged_query_prefix_prefix_authenticated_opening_target prefix
      prefix_state \<subseteq> query_sample_space"
    by (rule staged_query_prefix_prefix_authenticated_opening_target_subset)
next
  show
    "query_sample_space \<subseteq>
      staged_query_prefix_prefix_authenticated_opening_target prefix
        prefix_state"
  proof
    fix idx
    assume idx_sample: "idx \<in> query_sample_space"
    then obtain trace_openings composition_openings where
      "sqp_composition_fri_roots prefix \<noteq> []"
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) trace_openings prefix_state"
      "partial_authenticated_table
        (hd (sqp_composition_fri_roots prefix))
        (scale * clength) composition_openings prefix_state"
      "partial_query_openings_consistent trace_openings composition_openings
        (sqp_alphas prefix) idx"
      using witnessed by blast
    then show
      "idx \<in>
        staged_query_prefix_prefix_authenticated_opening_target prefix
          prefix_state"
      unfolding staged_query_prefix_prefix_authenticated_opening_target_def
      using idx_sample by blast
  qed
qed

lemma staged_query_prefix_prefix_authenticated_opening_target_subset_trace_indices:
  "staged_query_prefix_prefix_authenticated_opening_target prefix prefix_state
    \<subseteq>
   staged_query_prefix_prefix_authenticated_trace_indices prefix prefix_state"
proof
  fix idx
  assume idx_in:
    "idx \<in>
      staged_query_prefix_prefix_authenticated_opening_target prefix
        prefix_state"
  then obtain trace_openings composition_openings where
    idx_sample: "idx \<in> query_sample_space"
    and trace_table:
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) trace_openings prefix_state"
    and consistent:
      "partial_query_openings_consistent trace_openings
        composition_openings (sqp_alphas prefix) idx"
    unfolding staged_query_prefix_prefix_authenticated_opening_target_def
    by blast
  have trace_indices:
    "map opening_index trace_openings = powers_scaled idx"
    using consistent unfolding partial_query_openings_consistent_def
    by simp
  have trace_nonempty: "trace_openings \<noteq> []"
  proof -
    have "powers_scaled idx \<noteq> []"
      unfolding powers_scaled_def using powers_pos by simp
    then show ?thesis
      using trace_indices by auto
  qed
  have hd_idx: "opening_index (hd trace_openings) = idx"
  proof -
    have "hd (map opening_index trace_openings) = hd (powers_scaled idx)"
      using trace_indices by simp
    then have "opening_index (hd trace_openings) = hd (powers_scaled idx)"
      using trace_nonempty by (simp add: hd_map)
    then show ?thesis
      using powers_scaled_hd by simp
  qed
  have hd_in: "hd trace_openings \<in> set trace_openings"
    using trace_nonempty by simp
  have auth:
    "authenticated_opening_in prefix_state (hd trace_openings)"
    using trace_table hd_in unfolding partial_authenticated_table_def
    by blast
  have root:
    "opening_root (hd trace_openings) = sqp_trace_root prefix"
    using trace_table hd_in unfolding partial_authenticated_table_def
    by blast
  have len:
    "opening_length (hd trace_openings) = scale * clength"
    using trace_table hd_in unfolding partial_authenticated_table_def
    by blast
  show
    "idx \<in>
      staged_query_prefix_prefix_authenticated_trace_indices prefix
        prefix_state"
    unfolding staged_query_prefix_prefix_authenticated_trace_indices_def
    by (intro CollectI conjI exI[of _ "hd trace_openings"])
      (use idx_sample auth root len hd_idx in simp_all)
qed

lemma staged_query_prefix_prefix_authenticated_trace_indices_subset:
  "staged_query_prefix_prefix_authenticated_trace_indices prefix prefix_state
    \<subseteq> query_sample_space"
  unfolding staged_query_prefix_prefix_authenticated_trace_indices_def
  by blast

lemma staged_query_prefix_prefix_authenticated_trace_indices_eq_query_sample_space_if_all_indices_witnessed:
  assumes witnessed:
    "\<And>idx. idx \<in> query_sample_space \<Longrightarrow>
      \<exists>opn :: 'f authenticated_opening.
        authenticated_opening_in prefix_state opn \<and>
        opening_root opn = sqp_trace_root prefix \<and>
        opening_length opn = scale * clength \<and>
        opening_index opn = idx"
  shows
    "staged_query_prefix_prefix_authenticated_trace_indices prefix
      prefix_state = query_sample_space"
proof
  show
    "staged_query_prefix_prefix_authenticated_trace_indices prefix
      prefix_state \<subseteq> query_sample_space"
    by (rule staged_query_prefix_prefix_authenticated_trace_indices_subset)
next
  show
    "query_sample_space \<subseteq>
      staged_query_prefix_prefix_authenticated_trace_indices prefix
        prefix_state"
    unfolding staged_query_prefix_prefix_authenticated_trace_indices_def
    using witnessed by blast
qed

lemma finite_staged_query_prefix_prefix_authenticated_trace_indices[simp]:
  "finite
    (staged_query_prefix_prefix_authenticated_trace_indices prefix
      prefix_state)"
  by (rule finite_subset
      [OF staged_query_prefix_prefix_authenticated_trace_indices_subset
        finite_query_sample_space])

lemma staged_query_prefix_prefix_authenticated_opening_target_fraction_bound_if_trace_indices:
  assumes trace_frac:
      "nnreal
        (card
          (staged_query_prefix_prefix_authenticated_trace_indices prefix
            prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
  shows
    "nnreal
      (card
        (staged_query_prefix_prefix_authenticated_opening_target prefix
          prefix_state)) /
      nnreal (card query_sample_space) \<le> query_error_bound"
proof -
  have card_le:
    "card
      (staged_query_prefix_prefix_authenticated_opening_target prefix
        prefix_state) \<le>
     card
      (staged_query_prefix_prefix_authenticated_trace_indices prefix
        prefix_state)"
    by (rule card_mono)
      (simp,
        rule staged_query_prefix_prefix_authenticated_opening_target_subset_trace_indices)
  have
    "nnreal
      (card
        (staged_query_prefix_prefix_authenticated_opening_target prefix
          prefix_state)) /
      nnreal (card query_sample_space) \<le>
     nnreal
      (card
        (staged_query_prefix_prefix_authenticated_trace_indices prefix
          prefix_state)) /
      nnreal (card query_sample_space)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> query_error_bound"
    by (rule trace_frac)
  finally show ?thesis .
qed

lemma checked_staged_query_prefix_prefix_authenticated_target_hit_bound_from_trace_indices:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_frac:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        nnreal
          (card
            (staged_query_prefix_prefix_authenticated_trace_indices prefix
              prefix_state)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
  shows
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  have hit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state \<le>
     wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state + query_error_bound"
  proof (rule
      checked_staged_query_prefix_dynamic_index_hit_bound_by_prehit_and_query_error
      [OF raw_bound])
    fix prefix prefix_state
    assume support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
    have subset:
      "staged_query_prefix_prefix_authenticated_opening_target prefix
          prefix_state \<subseteq> query_sample_space"
      by (rule staged_query_prefix_prefix_authenticated_opening_target_subset)
    have frac:
      "nnreal
        (card
          (staged_query_prefix_prefix_authenticated_opening_target prefix
            prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      by (rule
          staged_query_prefix_prefix_authenticated_opening_target_fraction_bound_if_trace_indices)
        (rule trace_frac[OF support])
    show
      "staged_query_prefix_prefix_authenticated_opening_target prefix
          prefix_state \<subseteq> query_sample_space \<and>
       nnreal
        (card
          (staged_query_prefix_prefix_authenticated_opening_target prefix
            prefix_state)) /
        nnreal (card query_sample_space) \<le> query_error_bound"
      using subset frac by blast
  qed
  have prehit_bound:
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_prehit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1)"
  proof (rule
      checked_staged_query_prefix_dynamic_index_prehit_bound_from_relation_program)
    show "HashMap adversary_initial_state = fmempty"
      by (simp add: adversary_initial_state_def)
    show "hash_relation_program
        (checked_staged_query_prefix_dynamic_index_prehit_relation A i
          adversary_initial_state
          staged_query_prefix_prefix_authenticated_opening_target)
        size (staged_query_search_queries budgets i + 1)
        (checked_staged_query_prefix_receive_with_state A i)"
      by (rule hash_relation_program_checked_staged_query_prefix_receive_with_state
          [OF wf controlled])
        (use i_bound in simp_all,
          rule checked_staged_query_prefix_dynamic_index_prehit_relation_fiber_bound_size)
  qed
  show ?thesis
    by (rule order_trans[OF hit_bound])
      (intro add_mono prehit_bound order_refl)
qed

definition checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
where
  "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
      i out \<longleftrightarrow>
    (\<exists>(trace_openings :: 'f authenticated_opening list)
        (composition_openings :: 'f authenticated_opening list).
      checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i out)"

definition checked_staged_security_with_query_prefix_current_path_output_hit_at
where
  "checked_staged_security_with_query_prefix_current_path_output_hit_at
      (i::nat) out \<longleftrightarrow>
    (\<exists>(trace_openings :: 'f authenticated_opening list)
        (composition_openings :: 'f authenticated_opening list).
      checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings out)"

lemma checked_staged_security_with_query_prefix_current_path_output_hit_at_imp_lower:
  assumes hit:
    "checked_staged_security_with_query_prefix_current_path_output_hit_at
      i out"
  shows
    "\<exists>(trace_openings :: 'f authenticated_opening list)
        (composition_openings :: 'f authenticated_opening list).
      checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings out"
  using hit
  unfolding
    checked_staged_security_with_query_prefix_current_path_output_hit_at_def
  by assumption

lemma checked_staged_security_with_query_prefix_current_path_output_hit_atE:
  assumes hit:
    "checked_staged_security_with_query_prefix_current_path_output_hit_at
      i out"
  obtains prefix prefix_state raw raw_state data attacker_state result
      final_state rt len idx val pth where
    "out = Some (((((prefix, prefix_state), raw), raw_state),
      ((data, attacker_state), result)), final_state)"
    "hash_map_new_output_hit
      (merkle_path_target_roots final_state rt len idx val pth)
      prefix_state final_state"
    "finite (merkle_path_target_roots final_state rt len idx val pth)"
    "card (merkle_path_target_roots final_state rt len idx val pth) \<le>
      Suc (length pth)"
proof -
  from hit have lower_ex:
    "\<exists>(trace_openings :: 'f authenticated_opening list)
        (composition_openings :: 'f authenticated_opening list).
      checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings out"
    unfolding
      checked_staged_security_with_query_prefix_current_path_output_hit_at_def
    by assumption
  then show ?thesis
  proof
    fix trace_openings
    assume composition_ex:
      "\<exists>composition_openings.
        checked_staged_security_with_query_prefix_opening_path_output_hit
          trace_openings composition_openings out"
    then show ?thesis
    proof
      fix composition_openings
      assume lower:
        "checked_staged_security_with_query_prefix_opening_path_output_hit
          trace_openings composition_openings out"
      then show ?thesis
      proof (rule checked_staged_security_with_query_prefix_opening_path_output_hitE)
        fix prefix prefix_state raw raw_state data attacker_state result
          final_state opn
        assume out_eq:
          "out = Some (((((prefix, prefix_state), raw), raw_state),
            ((data, attacker_state), result)), final_state)"
        assume new_output:
          "hash_map_new_output_hit
            (merkle_path_target_roots final_state
              (opening_root opn)
              (opening_length opn)
              (opening_index opn)
              (opening_value opn)
              (opening_path opn))
            prefix_state final_state"
        assume finite_roots:
          "finite
            (merkle_path_target_roots final_state
              (opening_root opn)
              (opening_length opn)
              (opening_index opn)
              (opening_value opn)
              (opening_path opn))"
        assume card_roots:
          "card
            (merkle_path_target_roots final_state
              (opening_root opn)
              (opening_length opn)
              (opening_index opn)
              (opening_value opn)
              (opening_path opn)) \<le>
            Suc (length (opening_path opn))"
        show thesis
          by (rule that
              [of prefix prefix_state raw raw_state data attacker_state result
                final_state "opening_root opn" "opening_length opn"
                "opening_index opn" "opening_value opn" "opening_path opn"])
            (rule out_eq, rule new_output, rule finite_roots, rule card_roots)
      qed
    qed
  qed
qed

lemma checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_imp_dynamic_target:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i out"
  shows
    "checked_staged_security_with_query_prefix_dynamic_index_hit
      staged_query_prefix_prefix_authenticated_opening_target out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_def
      checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_def
    by simp
next
  case (Some packed)
  then obtain prefix prefix_state raw raw_state data attacker_state result
      final_state where out_eq:
    "out =
      Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state)"
    by (cases packed, auto split: prod.splits)
  have support_out:
    "Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          adversary_initial_state)"
    using support out_eq by simp
  have head:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    and cont:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive_with_verifier A i
            ((prefix, prefix_state), raw))
          raw_state)"
    using support_out
    unfolding checked_staged_security_experiment_with_query_prefix_data_state_def
    by (auto elim!: set_dist_bindE)
  have prefix_support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i)
          adversary_initial_state)"
    by (rule checked_staged_query_prefix_receive_with_state_prefix_support
        [OF head])
  have prefix_alignment:
    "PQueryCounter prefix_state = i \<and>
     PState prefix_state =
       state_after_query_chunks
        (staged_query_prefix_start_hash prefix)
        (sqp_query_chunks prefix) i \<and>
     length (sqp_query_chunks prefix) = i"
    by (rule checked_staged_query_prefix_with_state_alignment
        [OF wf controlled i_bound prefix_support])
  from cont obtain chunk chunk_state assert_state record_state suffix_chunks
    where data_eq:
      "data =
        \<lparr>staged_trace_root = sqp_trace_root prefix,
         staged_trace_fri_roots = sqp_trace_fri_roots prefix,
         staged_trace_fri_challenges = sqp_trace_fri_challenges prefix,
         staged_trace_final = sqp_trace_final prefix,
         staged_alphas = sqp_alphas prefix,
         staged_degree = sqp_degree prefix,
         staged_composition_fri_roots = sqp_composition_fri_roots prefix,
         staged_composition_fri_challenges =
           sqp_composition_fri_challenges prefix,
         staged_composition_final = sqp_composition_final prefix,
         staged_query_chunks = sqp_query_chunks prefix @ chunk # suffix_chunks\<rparr>"
    unfolding checked_staged_after_query_prefix_receive_with_verifier_def
      checked_staged_after_query_prefix_receive_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  from hit obtain trace_openings composition_openings where prefix_hit:
    "checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
      trace_openings composition_openings i out"
    unfolding
      checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_def
    by blast
  have idx_in:
    "index (to_nat raw) \<in>
      staged_query_prefix_prefix_authenticated_opening_target prefix prefix_state"
    using prefix_hit index_less_query_sample_space
    unfolding out_eq
      checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit_def
      staged_query_prefix_prefix_authenticated_opening_target_def
      query_sample_space_def
      data_eq
    by auto
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_query_prefix_dynamic_index_hit_def
      checked_staged_query_prefix_dynamic_index_hit_def
    using idx_in by simp
qed

lemma checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_le_dynamic_target:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state"
  by (rule wp_event_mono_on_support)
    (rule
      checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_imp_dynamic_target
        [OF wf controlled i_bound])

lemma checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_dynamic_target:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and prefix_bound:
      "wp_event (checked_staged_query_prefix_receive_with_state A i)
        (checked_staged_query_prefix_dynamic_index_hit
          staged_query_prefix_prefix_authenticated_opening_target)
        adversary_initial_state \<le> B"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
      adversary_initial_state \<le> B"
proof -
  have lifted:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state \<le> B"
    by (rule checked_staged_security_with_query_prefix_dynamic_index_hit_bound
        [OF prefix_bound])
  show ?thesis
    by (rule order_trans[
        OF checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_le_dynamic_target
          lifted])
      (use wf controlled i_bound in simp_all)
qed

lemma checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_trace_indices:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and trace_frac:
      "\<And>prefix prefix_state.
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        nnreal
          (card
            (staged_query_prefix_prefix_authenticated_trace_indices prefix
              prefix_state)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
proof (rule
    checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_dynamic_target
      [OF wf controlled i_bound])
  show
    "wp_event (checked_staged_query_prefix_receive_with_state A i)
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_prefix_authenticated_opening_target)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_query_prefix_prefix_authenticated_target_hit_bound_from_trace_indices
        [OF wf controlled i_bound trace_frac])
qed

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_imp_prefix_or_path_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i out"
  shows
    "checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
        i out \<or>
     checked_staged_security_with_query_prefix_current_path_output_hit_at
        i out"
proof -
  from hit obtain trace_openings composition_openings where current:
    "checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_openings composition_openings i out"
    unfolding
      checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_def
    by blast
  have split:
    "checked_staged_security_with_query_prefix_prefix_authenticated_opening_hit
        trace_openings composition_openings i out \<or>
     checked_staged_security_with_query_prefix_opening_path_output_hit
        trace_openings composition_openings out"
    by (rule
        checked_staged_security_with_query_prefix_authenticated_opening_hit_imp_prefix_or_path_output_hit_on_support
        [OF wf controlled i_bound support current])
  then show ?thesis
    unfolding
      checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_def
      checked_staged_security_with_query_prefix_current_path_output_hit_at_def
    by blast
qed

lemma checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_prefix_and_path:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
        adversary_initial_state \<le> P"
    and path_bound:
      "wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_path_output_hit_at i)
        adversary_initial_state \<le> Q"
  shows
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le> P + Q"
proof -
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out.
        checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
          i out \<or>
        checked_staged_security_with_query_prefix_current_path_output_hit_at
          i out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_imp_prefix_or_path_on_support
        [OF wf controlled i_bound])
  have union_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (\<lambda>out.
        checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at
          i out \<or>
        checked_staged_security_with_query_prefix_current_path_output_hit_at
          i out)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_path_output_hit_at i)
      adversary_initial_state"
    by (rule wp_event_union_bound)
  have sum_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
      adversary_initial_state +
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_path_output_hit_at i)
      adversary_initial_state \<le> P + Q"
    by (intro add_mono prefix_bound path_bound)
  show ?thesis
    by (rule order_trans[OF event_le])
      (rule order_trans[OF union_bound sum_bound])
qed

definition staged_security_with_data_state_current_query_partial_opening_hit_at
  :: "nat \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "staged_security_with_data_state_current_query_partial_opening_hit_at i out
    \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), result), final_state) \<Rightarrow>
          (let s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in
            (\<exists>raw trace_openings composition_openings rest.
              i < rounds \<and>
              fmlookup (HashMap final_state)
                (QueryIndexChallenge i
                  (state_after_query_chunks
                    (staged_query_start_hash data)
                    (staged_query_chunks data) i)) =
                Some raw \<and>
              staged_composition_fri_roots data \<noteq> [] \<and>
              Some (result, final_state) \<in>
                set_dist (execute verify_monad s) \<and>
              partial_authenticated_table (staged_trace_root data)
                (scale * clength) trace_openings final_state \<and>
              partial_authenticated_table
                (hd (staged_composition_fri_roots data))
                (scale * clength) composition_openings final_state \<and>
              verifier_header_transcript s
                (staged_trace_root data)
                (staged_trace_fri_roots data)
                (staged_trace_final data)
                (staged_alphas data)
                (staged_degree data)
                (staged_composition_fri_roots data)
                (staged_composition_final data)
                rest \<and>
              partial_query_openings_consistent trace_openings
                composition_openings (staged_alphas data)
                (index (to_nat raw)))))"

definition staged_security_with_data_state_current_query_partial_opening_hit
  :: "((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
where
  "staged_security_with_data_state_current_query_partial_opening_hit out
    \<longleftrightarrow>
      (\<exists>i < rounds.
        staged_security_with_data_state_current_query_partial_opening_hit_at
          i out)"

lemma staged_security_with_data_state_current_query_partial_opening_hit_at_aligned_transcript_classification_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    and no_bad:
      "\<not> partial_merkle_inconsistency_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state))"
    and hit:
      "staged_security_with_data_state_current_query_partial_opening_hit_at i
        (Some (((data, attacker_state), result), final_state))"
  shows
    "trace_fri_bad_with_partial_candidates
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state)) \<or>
     composition_fri_bad_with_partial_candidates
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state)) \<or>
     query_bad_with_partial_candidates
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (Some (result, final_state)) \<or>
     (\<exists>trace_table composition_table trace_openings_i composition_openings_i.
      partial_trace_table_candidate trace_table
        (trace_openings[i := trace_openings_i]) \<and>
      partial_composition_table_candidate composition_table
        (composition_openings[i := composition_openings_i]) \<and>
      trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as)"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support]
  obtain builder where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    by blast
  have staged_header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as
      query_idxs"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_shape
        [OF partial])
  from checked_staged_security_with_data_state_accepted_shape_query_chunks
      [OF wf controlled support shape]
  obtain raw_idxs where as_eq: "as = staged_alphas data"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<forall>j<rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
        Some (raw_idxs ! j)"
    by blast
  from partial have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned)
  have aligned0:
    "accepted_with_partial_initial_openings_aligned ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
        [OF aligned])
  from accepted_with_partial_initial_openings_aligned_shapes[OF aligned0]
  obtain rest where header:
    "verifier_header_transcript ?s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    by blast
  have header_eq:
    "fr = staged_trace_root data \<and>
     f_fri_roots = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     composition_fri_roots = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     rest = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  from hit obtain raw trace_openings_i composition_openings_i rest' where
    i_bound: "i < rounds"
    and final_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some raw"
    and trace_auth:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings_i final_state"
    and comp_auth:
      "partial_authenticated_table
        (hd (staged_composition_fri_roots data)) (scale * clength)
        composition_openings_i final_state"
    and consistent_raw:
      "partial_query_openings_consistent trace_openings_i
        composition_openings_i (staged_alphas data) (index (to_nat raw))"
    unfolding staged_security_with_data_state_current_query_partial_opening_hit_at_def
      Let_def
    by auto
  have raw_eq: "raw = raw_idxs ! i"
    using final_lookup lookup i_bound by simp
  have idx_eq: "index (to_nat raw) = query_idxs ! i"
    using raw_eq query_idxs_eq len_raw i_bound by simp
  have consistent:
    "partial_query_openings_consistent trace_openings_i
      composition_openings_i as (query_idxs ! i)"
    using consistent_raw idx_eq header_eq by simp
  have trace_auth':
    "partial_authenticated_table fr (scale * clength) trace_openings_i
      final_state"
    using trace_auth header_eq by simp
  have comp_auth':
    "partial_authenticated_table (hd composition_fri_roots)
      (scale * clength) composition_openings_i final_state"
    using comp_auth header_eq by simp
  have classified:
    "trace_fri_bad_with_partial_candidates ?s
      (Some (result, final_state)) \<or>
     composition_fri_bad_with_partial_candidates ?s
      (Some (result, final_state)) \<or>
     query_bad_with_partial_candidates ?s (Some (result, final_state)) \<or>
     (\<exists>trace_table composition_table.
      partial_trace_table_candidate trace_table
        (trace_openings[i := trace_openings_i]) \<and>
      partial_composition_table_candidate composition_table
        (composition_openings[i := composition_openings_i]) \<and>
      trace_table_low_degree trace_table \<and>
      composition_table_low_degree maxDegree composition_table \<and>
      all_queries_consistent trace_table composition_table as)"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_update_round_candidate_classification
        [OF partial no_bad i_bound consistent trace_auth' comp_auth'])
  then show ?thesis
    by blast
qed

lemma staged_security_with_data_state_current_query_partial_opening_hit_at_imp_query_prefix_current_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "Some (((((prefix, prefix_state), raw), raw_state),
          ((data, attacker_state), result)), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_query_prefix_data_state A i)
            adversary_initial_state)"
    and hit:
      "staged_security_with_data_state_current_query_partial_opening_hit_at i
        (Some (((data, attacker_state), result), final_state))"
  shows
    "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
      i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have hit':
    "\<exists>raw' trace_openings composition_openings rest.
      i < rounds \<and>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some raw' \<and>
      staged_composition_fri_roots data \<noteq> [] \<and>
      Some (result, final_state) \<in> set_dist (execute verify_monad ?s) \<and>
      partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state \<and>
      partial_authenticated_table
        (hd (staged_composition_fri_roots data)) (scale * clength)
        composition_openings final_state \<and>
      verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        rest \<and>
      partial_query_openings_consistent trace_openings
        composition_openings (staged_alphas data) (index (to_nat raw'))"
    using hit
    unfolding staged_security_with_data_state_current_query_partial_opening_hit_at_def
      Let_def
    by simp
  from hit'
  obtain raw' trace_openings composition_openings rest where
    final_lookup':
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some raw'"
    and comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
    and trace_auth:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and comp_auth:
      "partial_authenticated_table
        (hd (staged_composition_fri_roots data)) (scale * clength)
        composition_openings final_state"
    and consistent':
      "partial_query_openings_consistent trace_openings
        composition_openings (staged_alphas data) (index (to_nat raw'))"
    by blast
  have final_lookup:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_raw_final_lookup
        [OF wf controlled i_bound support])
  have raw_eq: "raw' = raw"
    using final_lookup' final_lookup by simp
  have current:
    "checked_staged_security_with_query_prefix_authenticated_opening_hit
      trace_openings composition_openings i
      (Some (((((prefix, prefix_state), raw), raw_state),
        ((data, attacker_state), result)), final_state))"
    unfolding checked_staged_security_with_query_prefix_authenticated_opening_hit_def
    using comp_nonempty trace_auth comp_auth consistent' raw_eq by simp
  show ?thesis
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_atI
        [OF current])
qed

lemma checked_staged_security_with_data_state_current_query_partial_opening_hit_at_le_query_prefix_current:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state"
proof -
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow>
        staged_security_with_data_state_current_query_partial_opening_hit_at
          i None
    | Some (packed, t) \<Rightarrow>
        staged_security_with_data_state_current_query_partial_opening_hit_at
          i (Some (snd packed, t))"
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_current_query_partial_opening_hit_at i)
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      ?projected
      adversary_initial_state"
    by (rule
        checked_staged_security_experiment_with_query_prefix_data_state_projection_event
        [OF i_bound])
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      ?projected
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_query_prefix_data_state A i)
              adversary_initial_state)"
      and hit: "?projected out"
    show
      "checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at
        i out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          staged_security_with_data_state_current_query_partial_opening_hit_at_def
        by simp
    next
      case (Some packed)
      then obtain prefix prefix_state raw raw_state data attacker_state result
          final_state where out_eq:
          "out =
            Some (((((prefix, prefix_state), raw), raw_state),
              ((data, attacker_state), result)), final_state)"
        by (cases packed) (auto split: prod.splits)
      show ?thesis
        unfolding out_eq
        by (rule
            staged_security_with_data_state_current_query_partial_opening_hit_at_imp_query_prefix_current_on_support
            [OF wf controlled i_bound])
          (use support hit out_eq in simp_all)
    qed
  qed
  show ?thesis
    unfolding projection
    by (rule event_le)
qed

lemma checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_query_prefix_rounds:
  assumes round_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_query_prefix_data_state A i)
        (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le> C i"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
proof -
  have round_le:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event
        (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le> C i"
  proof -
    fix i
    assume i_bound: "i < rounds"
    show
      "wp_event
        (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_current_query_partial_opening_hit_at i)
        adversary_initial_state \<le> C i"
      by (rule order_trans
          [OF
            checked_staged_security_with_data_state_current_query_partial_opening_hit_at_le_query_prefix_current
            round_bound[OF i_bound]])
        (use wf controlled i_bound in simp_all)
  qed
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out. \<exists>i \<in> {..<rounds}.
        staged_security_with_data_state_current_query_partial_opening_hit_at
          i out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_current_query_partial_opening_hit_def)
  also have "... \<le> (\<Sum>i<rounds. C i)"
    by (rule wp_event_finite_UN_bound)
      (simp_all add: round_le)
  finally show ?thesis .
qed

lemma staged_security_with_data_state_current_query_partial_opening_hit_at_imp_partial_opening_hit_at:
  assumes hit:
    "staged_security_with_data_state_current_query_partial_opening_hit_at i
      out"
  shows
    "staged_security_with_data_state_query_partial_opening_hit_at i out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding
      staged_security_with_data_state_current_query_partial_opening_hit_at_def
      staged_security_with_data_state_query_partial_opening_hit_at_def
    by simp
next
  case (Some packed)
  then obtain data attacker_state result final_state where out_eq:
    "out = Some (((data, attacker_state), result), final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have hit':
    "\<exists>raw trace_openings composition_openings rest.
      i < rounds \<and>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some raw \<and>
      staged_composition_fri_roots data \<noteq> [] \<and>
      Some (result, final_state) \<in> set_dist (execute verify_monad ?s) \<and>
      partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state \<and>
      partial_authenticated_table
        (hd (staged_composition_fri_roots data)) (scale * clength)
        composition_openings final_state \<and>
      verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        rest \<and>
      partial_query_openings_consistent trace_openings
        composition_openings (staged_alphas data) (index (to_nat raw))"
    using hit
    unfolding out_eq
      staged_security_with_data_state_current_query_partial_opening_hit_at_def
      Let_def
    by simp
  from hit'
  obtain raw trace_openings composition_openings rest where
    i_bound: "i < rounds"
    and lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data)
            (staged_query_chunks data) i)) =
      Some raw"
    and comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and trace_auth:
      "partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings final_state"
    and comp_auth:
      "partial_authenticated_table
        (hd (staged_composition_fri_roots data)) (scale * clength)
        composition_openings final_state"
    and header:
      "verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        rest"
    and consistent:
      "partial_query_openings_consistent trace_openings
        composition_openings (staged_alphas data) (index (to_nat raw))"
    by blast
  have idx_sample: "index (to_nat raw) \<in> query_sample_space"
    using consistent
    unfolding partial_query_openings_consistent_def by simp
  have witness:
    "(trace_openings, composition_openings) \<in>
      query_header_supported_partial_opening_witnesses ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
    unfolding query_header_supported_partial_opening_witnesses_def
    using comp_nonempty verifier trace_auth comp_auth header
    by blast
  have success:
    "index (to_nat raw) \<in>
      query_header_supported_partial_opening_success_indices_at ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i"
    unfolding query_header_supported_partial_opening_success_indices_at_def
    by (intro CollectI conjI exI[of _ trace_openings]
        exI[of _ composition_openings])
      (use idx_sample witness consistent in simp_all)
  show ?thesis
    unfolding out_eq staged_security_with_data_state_query_partial_opening_hit_at_def
      Let_def
    using i_bound lookup success by simp
qed

lemma staged_security_with_data_state_current_query_partial_opening_hit_imp_partial_opening_hit:
  assumes hit:
    "staged_security_with_data_state_current_query_partial_opening_hit out"
  shows "staged_security_with_data_state_query_partial_opening_hit out"
proof -
  from hit obtain i where i_bound: "i < rounds"
    and round_hit:
      "staged_security_with_data_state_current_query_partial_opening_hit_at
        i out"
    unfolding staged_security_with_data_state_current_query_partial_opening_hit_def
    by blast
  have
    "staged_security_with_data_state_query_partial_opening_hit_at i out"
    by (rule
        staged_security_with_data_state_current_query_partial_opening_hit_at_imp_partial_opening_hit_at
        [OF round_hit])
  then show ?thesis
    by (rule staged_security_with_data_state_query_partial_opening_hitI
        [OF i_bound])
qed

lemma staged_security_with_data_state_current_query_partial_opening_hitI:
  assumes "i < rounds"
    and
      "staged_security_with_data_state_current_query_partial_opening_hit_at
        i out"
  shows
    "staged_security_with_data_state_current_query_partial_opening_hit out"
  using assms
  unfolding staged_security_with_data_state_current_query_partial_opening_hit_def
  by blast

lemma checked_staged_security_with_data_state_aligned_transcript_query_bad_imp_current_partial_opening_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates
        (Some (((data, attacker_state), result), final_state))"
  shows
    "staged_security_with_data_state_current_query_partial_opening_hit
      (Some (((data, attacker_state), result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support]
  obtain builder where builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  have staged_header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  from bad obtain fr f_fri_roots f_final as dg composition_fri_roots
      final query_idxs trace_openings composition_openings trace_table
      composition_table where partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent ?s
        (Some (result, final_state)) fr f_fri_roots f_final as dg
        composition_fri_roots final query_idxs trace_openings
        composition_openings"
    unfolding staged_security_with_data_state_verifier_event_def
      query_bad_with_aligned_transcript_partial_candidates_def
    by simp blast
  have aligned:
    "accepted_with_partial_initial_openings_aligned_consistent ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        [OF partial])
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state)) as
      query_idxs"
    by (rule
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_shape
        [OF partial])
  from checked_staged_security_with_data_state_accepted_shape_query_chunks
      [OF wf controlled support shape]
  obtain raw_idxs where
    as_eq: "as = staged_alphas data"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<forall>i<rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs ! i)"
    by blast
  have aligned0:
    "accepted_with_partial_initial_openings_aligned ?s
      (Some (result, final_state)) fr f_fri_roots f_final as dg
      composition_fri_roots final query_idxs trace_openings
      composition_openings"
    by (rule
        accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
        [OF aligned])
  from accepted_with_partial_initial_openings_aligned_shapes[OF aligned0]
  obtain rest where header:
    "verifier_header_transcript ?s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
    by blast
  have comp_nonempty: "composition_fri_roots \<noteq> []"
    using accepted_with_partial_initial_openings_aligned_shapes(1)
      [OF aligned0] .
  have trace_partial:
    "accepted_with_partial_trace_openings ?s
      (Some (result, final_state)) fr query_idxs trace_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(3)
      [OF aligned0] .
  have comp_partial:
    "accepted_with_partial_composition_openings ?s
      (Some (result, final_state)) (hd composition_fri_roots) query_idxs
      composition_openings"
    using accepted_with_partial_initial_openings_aligned_shapes(4)
      [OF aligned0] .
  have header_eq:
    "fr = staged_trace_root data \<and>
     f_fri_roots = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     composition_fri_roots = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     rest = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF header staged_header]
    by simp
  let ?i = 0
  have i_bound: "?i < rounds"
    using rounds_positive by simp
  have round_consistent:
    "partial_query_round_consistent trace_openings composition_openings as
      ?i (query_idxs ! ?i)"
    using aligned i_bound
    unfolding accepted_with_partial_initial_openings_aligned_consistent_def
    by simp
  have opening_consistent:
    "partial_query_openings_consistent (trace_openings ! ?i)
      (composition_openings ! ?i) as (query_idxs ! ?i)"
    using round_consistent
    unfolding partial_query_round_consistent_def
      partial_query_openings_consistent_def
    by simp
  have trace_table:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! ?i) final_state"
    using trace_partial i_bound
    unfolding accepted_with_partial_trace_openings_def by blast
  have comp_table:
    "partial_authenticated_table (hd composition_fri_roots)
      (scale * clength) (composition_openings ! ?i) final_state"
    using comp_partial i_bound
    unfolding accepted_with_partial_composition_openings_def by blast
  have raw_idx:
    "index (to_nat (raw_idxs ! ?i)) = query_idxs ! ?i"
    using query_idxs_eq len_raw i_bound by simp
  have lookup_i:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge ?i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) ?i)) =
      Some (raw_idxs ! ?i)"
    using lookup i_bound by simp
  have exists_hit:
    "\<exists>raw trace_openings' composition_openings' rest'.
      ?i < rounds \<and>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge ?i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) ?i)) =
        Some raw \<and>
      staged_composition_fri_roots data \<noteq> [] \<and>
      Some (result, final_state) \<in> set_dist (execute verify_monad ?s) \<and>
      partial_authenticated_table (staged_trace_root data)
        (scale * clength) trace_openings' final_state \<and>
      partial_authenticated_table (hd (staged_composition_fri_roots data))
        (scale * clength) composition_openings' final_state \<and>
      verifier_header_transcript ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        rest' \<and>
      partial_query_openings_consistent trace_openings'
        composition_openings' (staged_alphas data) (index (to_nat raw))"
    apply (rule exI[where x = "raw_idxs ! ?i"])
    apply (rule exI[where x = "trace_openings ! ?i"])
    apply (rule exI[where x = "composition_openings ! ?i"])
    apply (rule exI[where x = "List.concat (staged_query_chunks data)"])
    using i_bound lookup_i comp_nonempty verifier trace_table comp_table
      opening_consistent raw_idx header_eq staged_header
    by simp
  have hit_at:
    "staged_security_with_data_state_current_query_partial_opening_hit_at ?i
      (Some (((data, attacker_state), result), final_state))"
    unfolding
      staged_security_with_data_state_current_query_partial_opening_hit_at_def
      Let_def
    using exists_hit by simp
  show ?thesis
    by (rule staged_security_with_data_state_current_query_partial_opening_hitI
        [OF i_bound hit_at])
qed

lemma checked_staged_security_with_data_state_aligned_transcript_query_bad_bound_from_current_partial_opening_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates)
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state"
proof (rule wp_event_mono_on_support)
  fix out
  assume support:
    "out \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        query_bad_with_aligned_transcript_partial_candidates out"
  show "staged_security_with_data_state_current_query_partial_opening_hit out"
  proof (cases out)
    case None
    then show ?thesis
      using bad
      unfolding staged_security_with_data_state_verifier_event_def
        query_bad_with_aligned_transcript_partial_candidates_def
      by simp
  next
    case (Some packed)
    then obtain data attacker_state result final_state where out_eq:
      "out = Some (((data, attacker_state), result), final_state)"
      by (cases packed, auto split: prod.splits)
    show ?thesis
      unfolding out_eq
      by (rule
          checked_staged_security_with_data_state_aligned_transcript_query_bad_imp_current_partial_opening_hit_on_support
          [OF wf controlled])
        (use support bad out_eq in simp_all)
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_data_state_current_partial_opening_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
  shows
    "staged_security_with_data_state_current_query_partial_opening_hit
      (Some (((data, attacker_state), result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  have header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_current_openingsE
        [OF wf controlled support hit])
    fix s trace_table composition_table query_idxs f i raw trace_openings
        composition_openings trace_openingss composition_openingss
    assume s_def:
        "s = verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      and i_bound: "i < rounds"
      and final_lookup:
        "fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some raw"
      and idx_eq: "index (to_nat raw) = query_idxs ! i"
      and comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
      and trace_auth:
        "partial_authenticated_table (staged_trace_root data)
          (scale * clength) trace_openings final_state"
      and comp_auth:
        "partial_authenticated_table
          (hd (staged_composition_fri_roots data)) (scale * clength)
          composition_openings final_state"
      and consistent:
        "partial_query_openings_consistent trace_openings
          composition_openings (staged_alphas data) (query_idxs ! i)"
    have consistent_raw:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
      using consistent idx_eq by simp
    have round_hit:
      "staged_security_with_data_state_current_query_partial_opening_hit_at i
        (Some (((data, attacker_state), result), final_state))"
      unfolding
        staged_security_with_data_state_current_query_partial_opening_hit_at_def
        Let_def
      apply simp
      by (intro exI[of _ raw] exI[of _ trace_openings]
          exI[of _ composition_openings]
          exI[of _ "List.concat (staged_query_chunks data)"] conjI)
        (use i_bound final_lookup comp_nonempty verifier trace_auth
          comp_auth header consistent_raw in simp_all)
    show
      "staged_security_with_data_state_current_query_partial_opening_hit
        (Some (((data, attacker_state), result), final_state))"
      by (rule
          staged_security_with_data_state_current_query_partial_opening_hitI
          [OF i_bound round_hit])
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_data_state_current_partial_opening_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (packed, t) \<Rightarrow>
        staged_security_with_data_state_current_query_partial_opening_hit
          (Some (?project packed, t))"
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?projected adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
                A)
              adversary_initial_state)"
      and hit:
        "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
          out"
    show "?projected out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
          checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
          checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        by simp
    next
      case (Some packed)
      then obtain alpha_prefix alpha_prefix_state data attacker_state result
          final_state where out_eq:
          "out =
            Some (((((alpha_prefix, alpha_prefix_state), data),
              attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      have partial_hit:
        "staged_security_with_data_state_current_query_partial_opening_hit
          (Some (((data, attacker_state), result), final_state))"
        by (rule
            checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_data_state_current_partial_opening_hit_on_support
            [OF wf controlled])
          (use support hit out_eq in simp_all)
      show ?thesis
        unfolding out_eq
        using partial_hit by simp
    qed
  qed
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?projected adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state"
  proof -
    have
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_current_query_partial_opening_hit
        adversary_initial_state =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
          \<bind> (\<lambda>x. return (?project x)))
        staged_security_with_data_state_current_query_partial_opening_hit
        adversary_initial_state"
      using
        checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
        [of A]
      by simp
    also have "... =
      wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        ?projected adversary_initial_state"
      by (subst wp_event_bind_return_map)
        (simp add:
          staged_security_with_data_state_current_query_partial_opening_hit_def
          staged_security_with_data_state_current_query_partial_opening_hit_at_def)
    finally show ?thesis
      by simp
  qed
  show ?thesis
    by (rule order_trans[OF event_le])
      (simp add: projection)
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_data_state_current_partial_opening_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and partial_bound:
      "wp_event
        (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_current_query_partial_opening_hit
        adversary_initial_state \<le> (Q::prob)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> Q"
  by (rule order.trans
      [OF
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_data_state_current_partial_opening_hit
        partial_bound])
    (use wf controlled in simp_all)

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_prefix_current_rounds:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
          adversary_initial_state \<le> C i"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
proof -
  have current_bound:
    "wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_current_query_partial_opening_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_current_query_partial_opening_hit_bound_from_query_prefix_rounds
        [OF round_bound wf controlled])
  show ?thesis
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_data_state_current_partial_opening_hit
        [OF wf controlled current_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_prefix_target_and_path:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event (checked_staged_query_prefix_receive_with_state A i)
          (checked_staged_query_prefix_dynamic_index_hit
            staged_query_prefix_prefix_authenticated_opening_target)
          adversary_initial_state \<le> P i"
    and path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_path_output_hit_at i)
          adversary_initial_state \<le> Q i"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. P i + Q i)"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_prefix_current_rounds
    [OF wf controlled])
  fix i
  assume i_bound: "i < rounds"
  have prefix_hit_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
      adversary_initial_state \<le> P i"
    by (rule
        checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_dynamic_target
        [OF wf controlled i_bound prefix_bound[OF i_bound]])
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le> P i + Q i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_prefix_and_path
        [OF wf controlled i_bound prefix_hit_bound path_bound[OF i_bound]])
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_trace_indices_and_path:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_frac:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        nnreal
          (card
            (staged_query_prefix_prefix_authenticated_trace_indices prefix
              prefix_state)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
    and path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_path_output_hit_at i)
          adversary_initial_state \<le> Q i"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound + Q i)"
proof (rule
    checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_query_prefix_current_rounds
    [OF wf controlled])
  fix i
  assume i_bound: "i < rounds"
  have prefix_hit_bound:
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) + query_error_bound"
    by (rule
        checked_staged_security_with_query_prefix_current_prefix_authenticated_hit_at_bound_from_trace_indices
        [OF wf controlled i_bound])
      (use trace_frac[OF i_bound] in blast)
  show
    "wp_event
      (checked_staged_security_experiment_with_query_prefix_data_state A i)
      (checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + Q i"
    by (rule
        checked_staged_security_with_query_prefix_current_query_partial_opening_hit_at_bound_from_prefix_and_path
        [OF wf controlled i_bound prefix_hit_bound path_bound[OF i_bound]])
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_trace_indices_path_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and trace_frac:
      "\<And>i prefix prefix_state.
        i < rounds \<Longrightarrow>
        Some ((prefix, prefix_state), prefix_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_with_state A i)
              adversary_initial_state) \<Longrightarrow>
        nnreal
          (card
            (staged_query_prefix_prefix_authenticated_trace_indices prefix
              prefix_state)) /
          nnreal (card query_sample_space) \<le> query_error_bound"
    and path_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event
          (checked_staged_security_experiment_with_query_prefix_data_state A i)
          (checked_staged_security_with_query_prefix_current_path_output_hit_at i)
          adversary_initial_state \<le> Q i"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound + Q i) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  let ?Q =
    "(\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound + Q i)"
  have query_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> ?Q"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_trace_indices_and_path
        [OF wf controlled trace_frac path_bound])
  have without_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit
      adversary_initial_state \<le> 0"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_without_query_hit_bound
        [OF wf controlled])
  have drift_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift
      adversary_initial_state \<le> ?Q + 0"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_bound_from_query_and_without_query
        [OF query_bound without_bound])
  have comp_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      (?Q + 0) +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_composition_bad_bound_from_composition_candidate_drift_and_budgets
        [OF wf controlled drift_bound])
  then show ?thesis
    by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_data_state_partial_opening_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state) \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
        (Some (((((alpha_prefix, alpha_prefix_state), data), attacker_state),
          result), final_state))"
  shows
    "staged_security_with_data_state_query_partial_opening_hit
      (Some (((data, attacker_state), result), final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have data_support:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_support_imp_data_state_support
        [OF support])
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF data_support]
  obtain builder verifier where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast
  have header:
    "verifier_header_transcript ?s
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule checked_staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  show ?thesis
  proof (rule
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_current_openingsE
        [OF wf controlled support hit])
    fix s trace_table composition_table query_idxs f i raw trace_openings
        composition_openings trace_openingss composition_openingss
    assume s_def:
        "s = verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      and i_bound: "i < rounds"
      and final_lookup:
        "fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some raw"
      and idx_eq: "index (to_nat raw) = query_idxs ! i"
      and comp_nonempty: "staged_composition_fri_roots data \<noteq> []"
      and trace_auth:
        "partial_authenticated_table (staged_trace_root data)
          (scale * clength) trace_openings final_state"
      and comp_auth:
        "partial_authenticated_table
          (hd (staged_composition_fri_roots data)) (scale * clength)
          composition_openings final_state"
      and consistent:
        "partial_query_openings_consistent trace_openings
          composition_openings (staged_alphas data) (query_idxs ! i)"
    have consistent_raw:
      "partial_query_openings_consistent trace_openings composition_openings
        (staged_alphas data) (index (to_nat raw))"
      using consistent idx_eq by simp
    have idx_sample: "index (to_nat raw) \<in> query_sample_space"
      using consistent_raw
      unfolding partial_query_openings_consistent_def by simp
    have witness:
      "(trace_openings, composition_openings) \<in>
        query_header_supported_partial_opening_witnesses ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
      unfolding query_header_supported_partial_opening_witnesses_def
      using comp_nonempty verifier trace_auth comp_auth header
      by auto
    have success:
      "index (to_nat raw) \<in>
        query_header_supported_partial_opening_success_indices_at ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)
          i"
      unfolding query_header_supported_partial_opening_success_indices_at_def
      by (intro CollectI conjI exI[of _ trace_openings]
          exI[of _ composition_openings])
        (use idx_sample witness consistent_raw in simp_all)
    have round_hit:
      "staged_security_with_data_state_query_partial_opening_hit_at i
        (Some (((data, attacker_state), result), final_state))"
      unfolding staged_security_with_data_state_query_partial_opening_hit_at_def
        Let_def
      using i_bound final_lookup success by simp
    show
      "staged_security_with_data_state_query_partial_opening_hit
        (Some (((data, attacker_state), result), final_state))"
      by (rule staged_security_with_data_state_query_partial_opening_hitI
          [OF i_bound round_hit])
  qed
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_data_state_partial_opening_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state"
proof -
  let ?project =
    "\<lambda>x. ((snd (fst (fst x)), snd (fst x)), snd x)"
  let ?projected =
    "\<lambda>out. case out of
      None \<Rightarrow> False
    | Some (packed, t) \<Rightarrow>
        staged_security_with_data_state_query_partial_opening_hit
          (Some (?project packed, t))"
  have event_le:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le>
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?projected adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
        "out \<in>
          set_dist
            (execute
              (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
                A)
              adversary_initial_state)"
      and hit:
        "checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
          out"
    show "?projected out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_def
          checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_def
          checked_staged_security_with_actual_alpha_prefix_verifier_event_def
        by simp
    next
      case (Some packed)
      then obtain alpha_prefix alpha_prefix_state data attacker_state result
          final_state where out_eq:
          "out =
            Some (((((alpha_prefix, alpha_prefix_state), data),
              attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      have partial_hit:
        "staged_security_with_data_state_query_partial_opening_hit
          (Some (((data, attacker_state), result), final_state))"
        by (rule
            checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_imp_data_state_partial_opening_hit_on_support
            [OF wf controlled])
          (use support hit out_eq in simp_all)
      show ?thesis
        unfolding out_eq
        using partial_hit by simp
    qed
  qed
  have projection:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      ?projected adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_opening_hit
      adversary_initial_state"
  proof -
    have
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_opening_hit
        adversary_initial_state =
       wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A
          \<bind> (\<lambda>x. return (?project x)))
        staged_security_with_data_state_query_partial_opening_hit
        adversary_initial_state"
      using
        checked_staged_security_experiment_with_actual_alpha_prefix_data_state_projection
        [of A]
      by simp
    also have "... =
      wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
        ?projected adversary_initial_state"
      by (subst wp_event_bind_return_map)
        (simp add: staged_security_with_data_state_query_partial_opening_hit_def
          staged_security_with_data_state_query_partial_opening_hit_at_def)
    finally show ?thesis
      by simp
  qed
  show ?thesis
    by (rule order_trans[OF event_le])
      (simp add: projection)
qed

lemma checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_bound_from_data_state_partial_opening_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and partial_bound:
      "wp_event
        (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_opening_hit
        adversary_initial_state \<le> (Q::prob)"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit
      adversary_initial_state \<le> Q"
  by (rule order.trans
      [OF
        checked_staged_security_with_actual_alpha_prefix_composition_candidate_drift_query_hit_le_data_state_partial_opening_hit
        partial_bound])
    (use wf controlled in simp_all)

end

end
