(*  Title:      Stark/Staged_Security_Experiment_Checked.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Staged_Security_Experiment_Checked
  imports Staged_Security_Experiment_Checked_Prefix
begin

text \<open>Final checked staged query-bad and collision bounds.\<close>

context soundness
begin

lemma query_bad_imp_query_rounds_sampling_success_hit:
  assumes bad: "query_bad s out"
  shows
    "\<exists>trace_table composition_table as.
      query_rounds_any_index_set_hit s
        (query_sampling_success_space trace_table composition_table as)
        rounds out"
proof -
  have round_hit:
    "query_index_round_set_hit s query_sampling_success_space out"
    by (rule query_bad_imp_query_index_round_set_hit[OF bad])
  then obtain i where hit_at:
    "query_index_round_set_hit_at s query_sampling_success_space i out"
    unfolding query_index_round_set_hit_def by blast
  show ?thesis
    by (rule query_index_round_set_hit_at_imp_query_rounds_any_index_set_hit
        [OF hit_at])
qed

lemma query_bad_imp_query_header_sampling_success_hit:
  assumes outcome: "out \<in> set_dist (execute verify_monad s)"
    and bad: "query_bad s out"
  shows
    "query_header_rounds_any_index_set_hit s
      (query_header_supported_union_good_sets s query_sampling_success_space)
      out"
proof -
  have round_hit:
    "query_index_round_set_hit s query_sampling_success_space out"
    by (rule query_bad_imp_query_index_round_set_hit[OF bad])
  show ?thesis
    by (rule query_index_round_set_hit_imp_query_header_supported_rounds_hit
        [OF outcome round_hit])
qed

lemma staged_security_with_data_query_bad_imp_sampling_hit:
  assumes bad: "staged_security_with_data_query_bad_hit out"
  shows "staged_security_with_data_query_sampling_hit out"
proof (cases out)
  case None
  then show ?thesis
    using bad unfolding staged_security_with_data_query_bad_hit_def by simp
next
  case (Some result)
  then obtain data verifier_result final_state where out_eq:
    "out = Some ((data, verifier_result), final_state)"
    by (cases result, auto split: prod.splits)
  from bad[unfolded out_eq staged_security_with_data_query_bad_hit_def]
  obtain s where query_bad:
    "query_bad s (Some (verifier_result, final_state))"
    by auto
  from query_bad_imp_query_rounds_sampling_success_hit[OF query_bad]
  obtain trace_table composition_table as where hit:
    "query_rounds_any_index_set_hit s
      (query_sampling_success_space trace_table composition_table as)
      rounds (Some (verifier_result, final_state))"
    by blast
  have witness:
    "\<exists>s trace_table composition_table as.
      query_rounds_any_index_set_hit s
        (query_sampling_success_space trace_table composition_table as)
        rounds (Some (verifier_result, final_state))"
    by (intro exI[of _ s] exI[of _ trace_table]
        exI[of _ composition_table] exI[of _ as])
      (rule hit)
  show ?thesis
    unfolding out_eq staged_security_with_data_query_sampling_hit_def
    using witness by simp
qed

lemma staged_security_with_data_query_bad_imp_header_sampling_hit:
  assumes bad: "staged_security_with_data_query_bad_hit out"
  shows "staged_security_with_data_query_header_sampling_hit out"
proof (cases out)
  case None
  then show ?thesis
    using bad unfolding staged_security_with_data_query_bad_hit_def by simp
next
  case (Some result)
  then obtain data verifier_result final_state where out_eq:
    "out = Some ((data, verifier_result), final_state)"
    by (cases result, auto split: prod.splits)
  from bad[unfolded out_eq staged_security_with_data_query_bad_hit_def]
  obtain s where outcome:
      "Some (verifier_result, final_state) \<in>
        set_dist (execute verify_monad s)"
    and query_bad:
      "query_bad s (Some (verifier_result, final_state))"
    by auto
  have hit:
    "query_header_rounds_any_index_set_hit s
      (query_header_supported_union_good_sets s query_sampling_success_space)
      (Some (verifier_result, final_state))"
    by (rule query_bad_imp_query_header_sampling_success_hit
        [OF outcome query_bad])
  then show ?thesis
    unfolding out_eq staged_security_with_data_query_header_sampling_hit_def
    by auto
qed

lemma staged_security_with_data_state_query_bad_imp_header_sampling_hit:
  assumes bad: "staged_security_with_data_state_query_bad_hit out"
  shows "staged_security_with_data_state_query_header_sampling_hit out"
proof (cases out)
  case None
  then show ?thesis
    using bad
    unfolding staged_security_with_data_state_query_bad_hit_def by simp
next
  case (Some result)
  then obtain data attacker_state verifier_result final_state where out_eq:
    "out = Some (((data, attacker_state), verifier_result), final_state)"
    by (cases result, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from bad[unfolded out_eq staged_security_with_data_state_query_bad_hit_def]
  have outcome:
      "Some (verifier_result, final_state) \<in>
        set_dist (execute verify_monad ?s)"
    and query_bad:
      "query_bad ?s (Some (verifier_result, final_state))"
    by (simp_all add: Let_def)
  have hit:
    "query_header_rounds_any_index_set_hit ?s
      (query_header_supported_union_good_sets ?s query_sampling_success_space)
      (Some (verifier_result, final_state))"
    by (rule query_bad_imp_query_header_sampling_success_hit
        [OF outcome query_bad])
  then show ?thesis
    unfolding out_eq
      staged_security_with_data_state_query_header_sampling_hit_def
    by simp
qed

lemma checked_staged_security_with_data_state_query_bad_imp_header_key_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad: "staged_security_with_data_state_query_bad_hit out"
  shows "staged_security_with_data_state_query_header_key_hit out"
proof (cases out)
  case None
  then show ?thesis
    using bad unfolding staged_security_with_data_state_query_bad_hit_def
    by simp
next
  case (Some result_pack)
  then obtain data attacker_state result final_state where out_eq:
    "out = Some (((data, attacker_state), result), final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have support_some:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    using support unfolding out_eq .
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support_some]
  have builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast+
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
  from bad[unfolded out_eq
      staged_security_with_data_state_query_bad_hit_def Let_def]
  have query_bad: "query_bad ?s (Some (result, final_state))"
    by simp
  from query_bad_imp_query_index_round_set_hit[OF query_bad]
  obtain i trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and i_bound: "i < rounds"
    and query_hit:
      "query_idxs ! i \<in>
        query_sampling_success_space trace_table composition_table as"
    unfolding query_index_round_set_hit_def
      query_index_round_set_hit_at_def
    by blast
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state))
      as query_idxs"
    using bound
    unfolding accepted_with_bound_tables_def accepted_with_tables_def
    by simp
  from checked_staged_security_with_data_state_accepted_shape_query_keys
      [OF wf controlled support_some shape]
  obtain raw_idxs where
    as_eq: "as = staged_alphas data"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup:
      "\<And>j. j < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
        Some (raw_idxs ! j)"
    and idx_bound:
      "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by blast
  have idx_sample:
    "query_idxs ! i \<in> query_sample_space"
  proof -
    have len_query: "length query_idxs = rounds"
      using query_idxs_eq len_raw by simp
    have "query_idxs ! i \<in> set query_idxs"
      by (rule nth_mem) (use i_bound len_query in simp)
    then show ?thesis
      by (rule accepted_with_bound_tables_query_sample_space[OF bound])
  qed
  have candidate:
    "(trace_table, composition_table) \<in>
      query_header_supported_table_candidates ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
  proof -
    have bound_staged:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table (staged_alphas data) query_idxs"
      using bound as_eq by simp
    have witness:
      "\<exists>out query_idxs rest.
        out \<in> set_dist (execute verify_monad ?s) \<and>
        accepted_with_bound_tables ?s out trace_table composition_table
          (staged_alphas data) query_idxs \<and>
        verifier_header_transcript ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) rest"
      by (intro exI[where x="Some (result, final_state)"]
          exI[where x=query_idxs]
          exI[where x="List.concat (staged_query_chunks data)"] conjI)
        (use verifier bound_staged staged_header in simp_all)
    show ?thesis
      using witness
      unfolding query_header_supported_table_candidates_def by simp
  qed
  have raw_hit:
    "index (to_nat (raw_idxs ! i)) \<in>
      query_header_supported_union_good_sets ?s
        query_sampling_success_space
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)"
  proof -
    have raw_idx_eq: "index (to_nat (raw_idxs ! i)) = query_idxs ! i"
      using query_idxs_eq len_raw i_bound by simp
    show ?thesis
      unfolding query_header_supported_union_good_sets_def raw_idx_eq
      using idx_sample candidate query_hit as_eq by blast
  qed
  have lookup_i:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    by (rule lookup[OF i_bound])
  show ?thesis
    unfolding out_eq staged_security_with_data_state_query_header_key_hit_def
      Let_def
    using i_bound lookup_i raw_hit by auto
qed

lemma staged_security_with_data_state_query_bad_bound_from_header_sampling_hit:
  assumes header_bound:
    "wp_event (staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_header_sampling_hit
      adversary_initial_state \<le> C"
  shows
    "wp_event (staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le> C"
proof -
  have "wp_event (staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
    wp_event (staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_header_sampling_hit
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule staged_security_with_data_state_query_bad_imp_header_sampling_hit)
  also have "... \<le> C"
    by (rule header_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_query_bad_bound_from_header_key_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and header_key_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_header_key_hit
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le> C"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_header_key_hit
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and bad: "staged_security_with_data_state_query_bad_hit out"
    show "staged_security_with_data_state_query_header_key_hit out"
      by (rule
          checked_staged_security_with_data_state_query_bad_imp_header_key_hit_on_support
          [OF wf controlled support bad])
  qed
  also have "... \<le> C"
    by (rule header_key_bound)
  finally show ?thesis .
qed

lemma
  checked_staged_security_with_data_state_header_key_hit_bound_from_index_set:
  assumes cover:
    "\<And>data attacker_state.
      query_header_supported_union_good_sets
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        query_sampling_success_space
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data) \<subseteq> B"
    and index_bound:
      "wp_event (checked_staged_security_experiment_with_data A)
        (staged_security_with_data_query_index_set_hit B)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_header_key_hit
      adversary_initial_state \<le> C"
proof -
  let ?projected =
    "\<lambda>out. case out of None \<Rightarrow>
        staged_security_with_data_query_index_set_hit B None
      | Some (((data, _), result), t) \<Rightarrow>
        staged_security_with_data_query_index_set_hit B
          (Some ((data, result), t))"
  have event_le:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_header_key_hit
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?projected adversary_initial_state"
  proof (rule wp_event_mono)
    fix out
    assume hit:
      "staged_security_with_data_state_query_header_key_hit out"
    show "?projected out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding staged_security_with_data_state_query_header_key_hit_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      let ?B =
        "query_header_supported_union_good_sets ?s
          query_sampling_success_space
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
      from hit[unfolded out_eq
          staged_security_with_data_state_query_header_key_hit_def Let_def]
      obtain i raw where i_bound: "i < rounds"
        and lookup:
          "fmlookup (HashMap final_state)
            (QueryIndexChallenge i
              (state_after_query_chunks
                (staged_query_start_hash data)
                (staged_query_chunks data) i)) =
            Some raw"
        and raw_hit: "index (to_nat raw) \<in> ?B"
        by auto
      have raw_in_B: "index (to_nat raw) \<in> B"
      proof -
        have "?B \<subseteq> B"
          by (rule cover)
        then show ?thesis
          using raw_hit by blast
      qed
      show ?thesis
        unfolding out_eq staged_security_with_data_query_index_set_hit_def
        using i_bound lookup raw_in_B by auto
    qed
  qed
  also have
    "wp_event (checked_staged_security_experiment_with_data_state A)
      ?projected adversary_initial_state =
     wp_event (checked_staged_security_experiment_with_data A)
      (staged_security_with_data_query_index_set_hit B)
      adversary_initial_state"
    using checked_staged_security_experiment_with_data_event_from_data_state
      [of A "staged_security_with_data_query_index_set_hit B"]
    by simp
  also have "... \<le> C"
    by (rule index_bound)
  finally show ?thesis .
qed

lemma
  checked_staged_security_with_data_state_header_key_hit_bound_from_index_set_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
      "\<And>data attacker_state.
        query_header_supported_union_good_sets
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          query_sampling_success_space
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<subseteq> B"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_header_key_hit
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule
      checked_staged_security_with_data_state_header_key_hit_bound_from_index_set
      [OF cover])
    (rule checked_staged_security_with_data_query_index_set_hit_bound
      [OF wf controlled])

lemma
  checked_staged_security_with_data_state_query_bad_bound_from_index_set_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
      "\<And>data attacker_state.
        query_header_supported_union_good_sets
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          query_sampling_success_space
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<subseteq> B"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule checked_staged_security_with_data_state_query_bad_bound_from_header_key_hit
      [OF wf controlled])
    (rule
      checked_staged_security_with_data_state_header_key_hit_bound_from_index_set_controlled
      [OF wf controlled cover])

lemma
  checked_staged_security_with_data_state_query_bad_bound_from_fixed_query_error_cover:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
      "\<And>data attacker_state.
        query_header_supported_union_good_sets
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          query_sampling_success_space
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<subseteq> B"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and envelope:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
proof -
  have target:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule
        checked_staged_security_with_data_state_query_bad_bound_from_index_set_controlled
        [OF wf controlled cover])
  also have "... \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
    by (rule staged_phase_query_index_target_error_query_bound
        [OF raw_bound subset envelope])
  finally show ?thesis .
qed

lemma
  checked_staged_security_with_data_state_query_bad_verifier_event_bound_from_index_set_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
      "\<And>data attacker_state.
        query_header_supported_union_good_sets
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          query_sampling_success_space
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<subseteq> B"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule
      checked_staged_security_with_data_state_query_bad_verifier_event_bound)
    (rule
      checked_staged_security_with_data_state_query_bad_bound_from_index_set_controlled
      [OF wf controlled cover])

lemma
  checked_staged_security_with_data_state_query_bad_verifier_event_bound_from_fixed_query_error_cover:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
      "\<And>data attacker_state.
        query_header_supported_union_good_sets
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          query_sampling_success_space
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<subseteq> B"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and envelope:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
  by (rule
      checked_staged_security_with_data_state_query_bad_verifier_event_bound)
    (rule
      checked_staged_security_with_data_state_query_bad_bound_from_fixed_query_error_cover
      [OF wf controlled cover raw_bound subset envelope])

lemma staged_security_with_data_query_bad_bound_from_sampling_hit:
  assumes sampling_bound:
    "wp_event (staged_security_experiment_with_data A)
      staged_security_with_data_query_sampling_hit
      adversary_initial_state \<le> C"
  shows
    "wp_event (staged_security_experiment_with_data A)
      staged_security_with_data_query_bad_hit
      adversary_initial_state \<le> C"
proof -
  have "wp_event (staged_security_experiment_with_data A)
      staged_security_with_data_query_bad_hit
      adversary_initial_state \<le>
    wp_event (staged_security_experiment_with_data A)
      staged_security_with_data_query_sampling_hit
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule staged_security_with_data_query_bad_imp_sampling_hit)
  also have "... \<le> C"
    by (rule sampling_bound)
  finally show ?thesis .
qed

lemma staged_security_with_data_query_bad_bound_from_header_sampling_hit:
  assumes header_bound:
    "wp_event (staged_security_experiment_with_data A)
      staged_security_with_data_query_header_sampling_hit
      adversary_initial_state \<le> C"
  shows
    "wp_event (staged_security_experiment_with_data A)
      staged_security_with_data_query_bad_hit
      adversary_initial_state \<le> C"
proof -
  have "wp_event (staged_security_experiment_with_data A)
      staged_security_with_data_query_bad_hit
      adversary_initial_state \<le>
    wp_event (staged_security_experiment_with_data A)
      staged_security_with_data_query_header_sampling_hit
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule staged_security_with_data_query_bad_imp_header_sampling_hit)
  also have "... \<le> C"
    by (rule header_bound)
  finally show ?thesis .
qed

lemma staged_transcript_program_outcome_trace_challenge_lookup:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (staged_transcript_program A)
            adversary_initial_state)"
    and i_bound: "i < ceil_log clength"
  shows
    "fmlookup (HashMap attacker_state)
      (TraceFriChallenge i
        (foldl concat (staged_trace_fri_start_hash data)
          (take (Suc i) (staged_trace_fri_roots data)))) =
      Some (staged_trace_fri_challenges data ! i)"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5
      as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 s12 query_chunks where
    root_out:
      "Some (fr, s1) \<in>
        set_dist (execute (trace_root_stage A) adversary_initial_state)"
    and record_root:
      "Some ((), s2) \<in> set_dist (execute (record_staged_message fr) s1)"
    and trace_out:
      "Some ((trace_roots, trace_bs), s3) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and final_out:
      "Some (trace_final, s4) \<in>
        set_dist (execute (trace_final_stage A trace_bs) s3)"
    and record_final:
      "Some ((), s5) \<in>
        set_dist (execute (record_staged_message trace_final) s4)"
    and alpha_out:
      "Some (as, s6) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s5)"
    and degree_out:
      "Some (dg, s7) \<in> set_dist (execute (degree_stage A as) s6)"
    and record_degree:
      "Some ((), s8) \<in> set_dist (execute (record_staged_message dg) s7)"
    and assert_out:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1))) s8)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s10) \<in>
        set_dist
          (execute
            (staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s9)"
    and composition_final_out:
      "Some (composition_final, s11) \<in>
        set_dist
          (execute (composition_final_stage A dg composition_bs) s10)"
    and record_composition_final:
      "Some ((), s12) \<in>
        set_dist (execute (record_staged_message composition_final) s11)"
    and query_out:
      "Some (query_chunks, attacker_state) \<in>
        set_dist (execute (staged_query_program A 0 rounds) s12)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
    unfolding staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have root_controlled:
    "controlled_ro_program (trace_root_budget budgets)
      (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def by simp
  have trace_final_controlled:
    "controlled_ro_program (trace_final_budget budgets)
      (trace_final_stage A trace_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have degree_controlled:
    "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_final_controlled:
    "controlled_ro_program (composition_final_budget budgets)
      (composition_final_stage A dg composition_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have root_fields:
    "PState s1 = 0 \<and>
     PTraceFriCounter s1 = 0"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp
  have s2_eq:
    "s2 = s1\<lparr>
      PState := concat (PState s1) fr,
      PTranscript := PTranscript s1 @ [fr]\<rparr>"
    by (rule record_staged_message_outcome[OF record_root])
  have trace_bound:
    "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have trace_alignment:
    "length trace_roots = ceil_log clength \<and>
     length trace_bs = length ([] :: 'f list) + ceil_log clength \<and>
     PTranscript s3 = PTranscript s2 @ trace_roots \<and>
     PState s3 = foldl concat (PState s2) trace_roots \<and>
     s2 \<le> s3 \<and>
     PTraceFriCounter s3 = PTraceFriCounter s2 + ceil_log clength \<and>
     PCompositionFriCounter s3 = PCompositionFriCounter s2 \<and>
     PAlphaCounter s3 = PAlphaCounter s2 \<and>
     PQueryCounter s3 = PQueryCounter s2 \<and>
     (\<forall>j < ceil_log clength.
        fmlookup (HashMap s3)
          (TraceFriChallenge (PTraceFriCounter s2 + j)
            (foldl concat (PState s2) (take (Suc j) trace_roots))) =
        Some (trace_bs ! (length ([] :: 'f list) + j)))"
    by (rule staged_trace_fri_program_alignment
        [OF controlled trace_bound trace_out])
  let ?key =
    "TraceFriChallenge i
      (foldl concat (concat 0 fr) (take (Suc i) trace_roots))"
  have lookup_s3: "fmlookup (HashMap s3) ?key = Some (trace_bs ! i)"
    using trace_alignment i_bound root_fields
    unfolding s2_eq by simp
  have ext_s3_s4: "s3 \<le> s4"
    using controlled_ro_program_extension[OF trace_final_controlled]
      final_out
    unfolding hash_extension_preserving_def by blast
  have s5_eq:
    "s5 = s4\<lparr>
      PState := concat (PState s4) trace_final,
      PTranscript := PTranscript s4 @ [trace_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_final])
  have ext_s4_s5: "s4 \<le> s5"
    unfolding s5_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have ext_s5_s6: "s5 \<le> s6"
    by (rule hash_target_program_outcome_extension
        [OF hash_target_program_staged_alpha_program alpha_out])
  have ext_s6_s7: "s6 \<le> s7"
    using controlled_ro_program_extension[OF degree_controlled] degree_out
    unfolding hash_extension_preserving_def by blast
  have s8_eq:
    "s8 = s7\<lparr>
      PState := concat (PState s7) dg,
      PTranscript := PTranscript s7 @ [dg]\<rparr>"
    by (rule record_staged_message_outcome[OF record_degree])
  have ext_s7_s8: "s7 \<le> s8"
    unfolding s8_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have s9_eq: "s9 = s8"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have ext_s8_s9: "s8 \<le> s9"
    unfolding s9_eq by (simp add: hash_ext_refl)
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_bound:
    "0 + ceil_log (to_nat dg + 1) \<le>
      length (composition_fri_budgets budgets)"
    using wf round_bound unfolding staged_budget_wellformed_def by simp
  have ext_s9_s10: "s9 \<le> s10"
    using staged_composition_fri_program_alignment
        [OF controlled composition_bound composition_out]
    by simp
  have ext_s10_s11: "s10 \<le> s11"
    using controlled_ro_program_extension[OF composition_final_controlled]
      composition_final_out
    unfolding hash_extension_preserving_def by blast
  have s12_eq:
    "s12 = s11\<lparr>
      PState := concat (PState s11) composition_final,
      PTranscript := PTranscript s11 @ [composition_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_composition_final])
  have ext_s11_s12: "s11 \<le> s12"
    unfolding s12_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have query_bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have ext_s12_attacker: "s12 \<le> attacker_state"
    by (rule hash_target_program_outcome_extension
        [OF hash_target_program_staged_query_program[OF controlled query_bound]
          query_out])
  have ext_s3_s5: "s3 \<le> s5"
    by (rule hash_ext_trans[OF ext_s3_s4 ext_s4_s5])
  have ext_s3_s6: "s3 \<le> s6"
    by (rule hash_ext_trans[OF ext_s3_s5 ext_s5_s6])
  have ext_s3_s7: "s3 \<le> s7"
    by (rule hash_ext_trans[OF ext_s3_s6 ext_s6_s7])
  have ext_s3_s8: "s3 \<le> s8"
    by (rule hash_ext_trans[OF ext_s3_s7 ext_s7_s8])
  have ext_s3_s9: "s3 \<le> s9"
    by (rule hash_ext_trans[OF ext_s3_s8 ext_s8_s9])
  have ext_s3_s10: "s3 \<le> s10"
    by (rule hash_ext_trans[OF ext_s3_s9 ext_s9_s10])
  have ext_s3_s11: "s3 \<le> s11"
    by (rule hash_ext_trans[OF ext_s3_s10 ext_s10_s11])
  have ext_s3_s12: "s3 \<le> s12"
    by (rule hash_ext_trans[OF ext_s3_s11 ext_s11_s12])
  have ext_s3_attacker: "s3 \<le> attacker_state"
    by (rule hash_ext_trans[OF ext_s3_s12 ext_s12_attacker])
  have lookup_attacker:
    "fmlookup (HashMap attacker_state) ?key = Some (trace_bs ! i)"
    by (rule hash_extension_lookup[OF lookup_s3 ext_s3_attacker])
  show ?thesis
    unfolding data_eq staged_trace_fri_start_hash_def
    using lookup_attacker by simp
qed

lemma staged_transcript_program_outcome_composition_challenge_lookup:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (staged_transcript_program A)
            adversary_initial_state)"
    and i_bound:
      "i < ceil_log (to_nat (staged_degree data) + 1)"
  shows
    "fmlookup (HashMap attacker_state)
      (CompositionFriChallenge i
        (foldl concat (staged_composition_fri_start_hash data)
          (take (Suc i) (staged_composition_fri_roots data)))) =
      Some (staged_composition_fri_challenges data ! i)"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5
      as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 s12 query_chunks where
    root_out:
      "Some (fr, s1) \<in>
        set_dist (execute (trace_root_stage A) adversary_initial_state)"
    and record_root:
      "Some ((), s2) \<in> set_dist (execute (record_staged_message fr) s1)"
    and trace_out:
      "Some ((trace_roots, trace_bs), s3) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    and final_out:
      "Some (trace_final, s4) \<in>
        set_dist (execute (trace_final_stage A trace_bs) s3)"
    and record_final:
      "Some ((), s5) \<in>
        set_dist (execute (record_staged_message trace_final) s4)"
    and alpha_out:
      "Some (as, s6) \<in>
        set_dist (execute (staged_alpha_program (length spec)) s5)"
    and degree_out:
      "Some (dg, s7) \<in> set_dist (execute (degree_stage A as) s6)"
    and record_degree:
      "Some ((), s8) \<in> set_dist (execute (record_staged_message dg) s7)"
    and assert_out:
      "Some ((), s9) \<in>
        set_dist
          (execute
            (assert
              (ceil_log (to_nat dg + 1) \<le>
                ceil_log (maxDegree + 1))) s8)"
    and composition_out:
      "Some ((composition_roots, composition_bs), s10) \<in>
        set_dist
          (execute
            (staged_composition_fri_program A dg 0
              (ceil_log (to_nat dg + 1)) []) s9)"
    and composition_final_out:
      "Some (composition_final, s11) \<in>
        set_dist
          (execute (composition_final_stage A dg composition_bs) s10)"
    and record_composition_final:
      "Some ((), s12) \<in>
        set_dist (execute (record_staged_message composition_final) s11)"
    and query_out:
      "Some (query_chunks, attacker_state) \<in>
        set_dist (execute (staged_query_program A 0 rounds) s12)"
    and data_eq:
      "data =
        \<lparr>staged_trace_root = fr,
         staged_trace_fri_roots = trace_roots,
         staged_trace_fri_challenges = trace_bs,
         staged_trace_final = trace_final,
         staged_alphas = as,
         staged_degree = dg,
         staged_composition_fri_roots = composition_roots,
         staged_composition_fri_challenges = composition_bs,
         staged_composition_final = composition_final,
         staged_query_chunks = query_chunks\<rparr>"
    unfolding staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have root_controlled:
    "controlled_ro_program (trace_root_budget budgets)
      (trace_root_stage A)"
    using controlled unfolding staged_adversary_controlled_def by simp
  have trace_final_controlled:
    "controlled_ro_program (trace_final_budget budgets)
      (trace_final_stage A trace_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have degree_controlled:
    "controlled_ro_program (degree_budget budgets) (degree_stage A as)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have composition_final_controlled:
    "controlled_ro_program (composition_final_budget budgets)
      (composition_final_stage A dg composition_bs)"
    using controlled unfolding staged_adversary_controlled_def by blast
  have root_fields:
    "PState s1 = 0 \<and>
     PCompositionFriCounter s1 = 0"
    using controlled_stage_outcome_fields[OF root_controlled root_out]
    by simp
  have s2_eq:
    "s2 = s1\<lparr>
      PState := concat (PState s1) fr,
      PTranscript := PTranscript s1 @ [fr]\<rparr>"
    by (rule record_staged_message_outcome[OF record_root])
  have s2_fields:
    "PState s2 = concat 0 fr \<and>
     PCompositionFriCounter s2 = 0"
    unfolding s2_eq using root_fields by simp
  have trace_bound:
    "0 + ceil_log clength \<le> length (trace_fri_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have trace_alignment:
    "length trace_roots = ceil_log clength \<and>
     length trace_bs = length ([] :: 'f list) + ceil_log clength \<and>
     PTranscript s3 = PTranscript s2 @ trace_roots \<and>
     PState s3 = foldl concat (PState s2) trace_roots \<and>
     s2 \<le> s3 \<and>
     PTraceFriCounter s3 = PTraceFriCounter s2 + ceil_log clength \<and>
     PCompositionFriCounter s3 = PCompositionFriCounter s2 \<and>
     PAlphaCounter s3 = PAlphaCounter s2 \<and>
     PQueryCounter s3 = PQueryCounter s2 \<and>
     (\<forall>j < ceil_log clength.
        fmlookup (HashMap s3)
          (TraceFriChallenge (PTraceFriCounter s2 + j)
            (foldl concat (PState s2) (take (Suc j) trace_roots))) =
        Some (trace_bs ! (length ([] :: 'f list) + j)))"
    by (rule staged_trace_fri_program_alignment
        [OF controlled trace_bound trace_out])
  have final_fields:
    "PState s4 = PState s3 \<and>
     PCompositionFriCounter s4 = PCompositionFriCounter s3"
    using controlled_stage_outcome_fields
        [OF trace_final_controlled final_out]
    by simp
  have s5_eq:
    "s5 = s4\<lparr>
      PState := concat (PState s4) trace_final,
      PTranscript := PTranscript s4 @ [trace_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_final])
  have s5_fields:
    "PState s5 =
      concat (foldl concat (concat 0 fr) trace_roots) trace_final \<and>
     PCompositionFriCounter s5 = 0"
    unfolding s5_eq
    using s2_fields trace_alignment final_fields by simp
  have alpha_alignment:
    "length as = length spec \<and>
     PTranscript s6 = PTranscript s5 @ as \<and>
     PState s6 = foldl concat (PState s5) as \<and>
     PTraceFriCounter s6 = PTraceFriCounter s5 \<and>
     PCompositionFriCounter s6 = PCompositionFriCounter s5 \<and>
     PAlphaCounter s6 = PAlphaCounter s5 + length spec \<and>
     PQueryCounter s6 = PQueryCounter s5"
    by (rule staged_alpha_program_alignment[OF alpha_out])
  have degree_fields:
    "PState s7 = PState s6 \<and>
     PCompositionFriCounter s7 = PCompositionFriCounter s6"
    using controlled_stage_outcome_fields[OF degree_controlled degree_out]
    by simp
  have s8_eq:
    "s8 = s7\<lparr>
      PState := concat (PState s7) dg,
      PTranscript := PTranscript s7 @ [dg]\<rparr>"
    by (rule record_staged_message_outcome[OF record_degree])
  have s9_eq: "s9 = s8"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have start_fields:
    "PState s9 =
      concat
        (foldl concat
          (concat
            (foldl concat (concat 0 fr) trace_roots)
            trace_final)
          as)
        dg \<and>
     PCompositionFriCounter s9 = 0"
    unfolding s9_eq s8_eq
    using s5_fields alpha_alignment degree_fields
    by simp
  have round_bound:
    "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    using assert_out unfolding assert_def
    by (cases
        "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)")
      (auto simp: throw_no_outcome)
  have composition_bound:
    "0 + ceil_log (to_nat dg + 1) \<le>
      length (composition_fri_budgets budgets)"
    using wf round_bound unfolding staged_budget_wellformed_def by simp
  have composition_alignment:
    "length composition_roots = ceil_log (to_nat dg + 1) \<and>
     length composition_bs =
       length ([] :: 'f list) + ceil_log (to_nat dg + 1) \<and>
     PTranscript s10 = PTranscript s9 @ composition_roots \<and>
     PState s10 = foldl concat (PState s9) composition_roots \<and>
     s9 \<le> s10 \<and>
     PTraceFriCounter s10 = PTraceFriCounter s9 \<and>
     PCompositionFriCounter s10 =
       PCompositionFriCounter s9 + ceil_log (to_nat dg + 1) \<and>
     PAlphaCounter s10 = PAlphaCounter s9 \<and>
     PQueryCounter s10 = PQueryCounter s9 \<and>
     (\<forall>j < ceil_log (to_nat dg + 1).
        fmlookup (HashMap s10)
          (CompositionFriChallenge (PCompositionFriCounter s9 + j)
            (foldl concat (PState s9) (take (Suc j) composition_roots))) =
        Some (composition_bs ! (length ([] :: 'f list) + j)))"
    by (rule staged_composition_fri_program_alignment
        [OF controlled composition_bound composition_out])
  let ?key =
    "CompositionFriChallenge i
      (foldl concat
        (concat
          (foldl concat
            (concat
              (foldl concat (concat 0 fr) trace_roots)
              trace_final)
            as)
          dg)
        (take (Suc i) composition_roots))"
  have i_bound': "i < ceil_log (to_nat dg + 1)"
    using i_bound unfolding data_eq by simp
  have lookup_s10:
    "fmlookup (HashMap s10) ?key = Some (composition_bs ! i)"
    using composition_alignment i_bound' start_fields by simp
  have ext_s10_s11: "s10 \<le> s11"
    using controlled_ro_program_extension[OF composition_final_controlled]
      composition_final_out
    unfolding hash_extension_preserving_def by blast
  have s12_eq:
    "s12 = s11\<lparr>
      PState := concat (PState s11) composition_final,
      PTranscript := PTranscript s11 @ [composition_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_composition_final])
  have ext_s11_s12: "s11 \<le> s12"
    unfolding s12_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have query_bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  have ext_s12_attacker: "s12 \<le> attacker_state"
    by (rule hash_target_program_outcome_extension
        [OF hash_target_program_staged_query_program[OF controlled query_bound]
          query_out])
  have ext_s10_s12: "s10 \<le> s12"
    by (rule hash_ext_trans[OF ext_s10_s11 ext_s11_s12])
  have ext_s10_attacker: "s10 \<le> attacker_state"
    by (rule hash_ext_trans[OF ext_s10_s12 ext_s12_attacker])
  have lookup_attacker:
    "fmlookup (HashMap attacker_state) ?key = Some (composition_bs ! i)"
    by (rule hash_extension_lookup[OF lookup_s10 ext_s10_attacker])
  show ?thesis
    unfolding data_eq staged_composition_fri_start_hash_def
      staged_trace_fri_start_hash_def
    using lookup_attacker by simp
qed

lemma staged_transcript_program_outcome_header_transcript:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (staged_transcript_program A)
            adversary_initial_state)"
  shows
    "verifier_header_transcript
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
proof -
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
    by (rule staged_transcript_program_outcome_shape
        [OF wf controlled outcome])
  show ?thesis
    by (rule staged_proof_transcript_verifier_header_transcript)
      (use shape in simp_all)
qed

lemma staged_security_experiment_outcomeE:
  assumes
    "Some (result, final_state) \<in>
      set_dist (execute (staged_security_experiment A) initial_state)"
  obtains data attacker_state where
    "Some (data, attacker_state) \<in>
      set_dist (execute (staged_transcript_program A) initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
  using assms unfolding staged_security_experiment_def
  by (auto elim!: set_dist_bindE intro: that)

lemma accepted_staged_security_experimentE:
  assumes outcome:
    "out \<in> set_dist
      (execute (staged_security_experiment A) adversary_initial_state)"
    and accepted: "\<not> Option.is_none out"
  obtains result final_state data attacker_state where
    "out = Some (result, final_state)"
    "Some (data, attacker_state) \<in>
      set_dist (execute (staged_transcript_program A) adversary_initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
proof -
  from accepted obtain result final_state where
    out: "out = Some (result, final_state)"
    by (cases out) auto
  from staged_security_experiment_outcomeE[OF outcome[unfolded out]]
  obtain data attacker_state where
    builder:
      "Some (data, attacker_state) \<in>
        set_dist (execute (staged_transcript_program A)
          adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    by blast
  show ?thesis by (rule that[OF out builder verifier])
qed

lemma accepted_staged_security_experiment_headerE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "out \<in> set_dist
        (execute (staged_security_experiment A) adversary_initial_state)"
    and accepted: "\<not> Option.is_none out"
  obtains result final_state data attacker_state where
    "out = Some (result, final_state)"
    "Some (data, attacker_state) \<in>
      set_dist (execute (staged_transcript_program A)
        adversary_initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    "verifier_header_transcript
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
proof -
  from accepted_staged_security_experimentE[OF outcome accepted]
  obtain result final_state data attacker_state where
    out_eq: "out = Some (result, final_state)"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist (execute (staged_transcript_program A)
          adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    by blast
  have header:
    "verifier_header_transcript
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      (staged_trace_root data)
      (staged_trace_fri_roots data)
      (staged_trace_final data)
      (staged_alphas data)
      (staged_degree data)
      (staged_composition_fri_roots data)
      (staged_composition_final data)
      (List.concat (staged_query_chunks data))"
    by (rule staged_transcript_program_outcome_header_transcript
        [OF wf controlled builder])
  show ?thesis
    by (rule that[OF out_eq builder verifier header])
qed

lemma accepted_staged_security_experiment_transcript_shapeE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "out \<in> set_dist
        (execute (staged_security_experiment A) adversary_initial_state)"
    and accepted: "\<not> Option.is_none out"
  obtains result final_state data attacker_state query_idxs where
    "out = Some (result, final_state)"
    "Some (data, attacker_state) \<in>
      set_dist (execute (staged_transcript_program A)
        adversary_initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    "accepted_transcript_shape
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      out
      (staged_alphas data)
      query_idxs"
proof -
  from accepted_staged_security_experiment_headerE
      [OF wf controlled outcome accepted]
  obtain result final_state data attacker_state where
    out_eq: "out = Some (result, final_state)"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist (execute (staged_transcript_program A)
          adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and staged_header:
      "verifier_header_transcript
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        (List.concat (staged_query_chunks data))"
    by blast
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from verify_monad_accepted_transcript_shape[OF verifier]
  obtain as query_idxs where shape:
    "accepted_transcript_shape ?s (Some (result, final_state))
      as query_idxs"
    by blast
  from shape obtain result' final_state' fr f_fri_roots f_final dg
      composition_fri_roots final rest where
    shape_out: "Some (result, final_state) = Some (result', final_state')"
    and shape_header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    by (elim accepted_transcript_shape_header_query_extraction)
  have as_eq: "as = staged_alphas data"
    using verifier_header_transcript_unique[OF staged_header shape_header]
    by simp
  have shape_staged:
    "accepted_transcript_shape ?s out (staged_alphas data) query_idxs"
    using shape unfolding out_eq as_eq .
  show ?thesis
    by (rule that[OF out_eq builder verifier shape_staged])
qed

lemma accepted_staged_security_experiment_query_chunksE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "out \<in> set_dist
        (execute (staged_security_experiment A) adversary_initial_state)"
    and accepted: "\<not> Option.is_none out"
  obtains result final_state data attacker_state raw_idxs query_idxs
      query_chunks trailing
  where
    "out = Some (result, final_state)"
    "Some (data, attacker_state) \<in>
      set_dist (execute (staged_transcript_program A)
        adversary_initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    "length raw_idxs = rounds"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "length query_chunks = rounds"
    "List.concat query_chunks @ trailing =
      List.concat (staged_query_chunks data)"
    "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (query_idxs ! i)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (query_chunks ! i)"
    "\<And>i. i < rounds \<Longrightarrow>
      length (query_chunks ! i) =
        verifier_query_round_transcript_length (query_idxs ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)"
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) query_chunks i)) =
        Some (raw_idxs ! i)"
    "\<forall>idx \<in> set query_idxs. idx < clength * scale"
proof -
  from accepted_staged_security_experiment_headerE
      [OF wf controlled outcome accepted]
  obtain result final_state data attacker_state where
    out_eq: "out = Some (result, final_state)"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist (execute (staged_transcript_program A)
          adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and staged_header:
      "verifier_header_transcript
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        (List.concat (staged_query_chunks data))"
    by blast
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from verify_monad_accepted_transcript_shape[OF verifier]
  obtain as accepted_query_idxs where shape:
    "accepted_transcript_shape ?s (Some (result, final_state))
      as accepted_query_idxs"
    by blast
  from accepted_transcript_shape_query_chunksE[OF shape]
  obtain result' final_state' fr f_fri_roots f_final dg
      composition_fri_roots final rest raw_idxs query_chunks trailing
    where shape_out:
      "Some (result, final_state) = Some (result', final_state')"
    and header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "accepted_query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and concat_chunks: "List.concat query_chunks @ trailing = rest"
    and chunk_shape:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (accepted_query_idxs ! i)
          f_fri_roots composition_fri_roots (query_chunks ! i)"
    and lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter ?s + i)
            (state_after_query_chunks
              (verifier_header_state ?s fr f_fri_roots f_final as dg
                composition_fri_roots final)
              query_chunks i)) =
          Some (raw_idxs ! i)"
    and idx_bound:
      "\<forall>idx \<in> set accepted_query_idxs. idx < clength * scale"
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
    using verifier_header_transcript_unique[OF staged_header header]
    by simp
  have final_state_eq: "final_state' = final_state"
    using shape_out by simp
  have header_state_eq:
    "verifier_header_state ?s fr f_fri_roots f_final as dg
      composition_fri_roots final =
      staged_query_start_hash data"
    using header_eq
    unfolding verifier_header_state_def verifier_header_messages_def
      staged_query_start_hash_def staged_composition_fri_start_hash_def
      staged_trace_fri_start_hash_def
    by simp
  have lookup':
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) query_chunks i)) =
        Some (raw_idxs ! i)"
    using lookup final_state_eq header_state_eq by simp
  have chunk_shape':
    "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (accepted_query_idxs ! i)
        (staged_trace_fri_roots data)
        (staged_composition_fri_roots data)
        (query_chunks ! i)"
    using chunk_shape header_eq by simp
  have chunk_len:
    "\<And>i. i < rounds \<Longrightarrow>
      length (query_chunks ! i) =
        verifier_query_round_transcript_length (accepted_query_idxs ! i)
          (staged_trace_fri_roots data)
          (staged_composition_fri_roots data)"
    by (rule verifier_query_round_chunk_length[OF chunk_shape'])
  show ?thesis
    by (rule that[OF out_eq builder verifier len_raw query_idxs_eq
          len_chunks])
      (use concat_chunks header_eq chunk_shape' chunk_len lookup' idx_bound
        in simp_all)
qed

lemma staged_transcript_shape_alpha_badD:
  assumes shape:
      "accepted_transcript_shape s out staged_as staged_query_idxs"
    and bad: "alpha_bad_set_hit s B out"
  shows "\<exists>trace_table. staged_as \<in> B trace_table"
proof -
  from bad obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables s out trace_table composition_table
        as query_idxs"
    and as_bad: "as \<in> B trace_table"
    unfolding alpha_bad_set_hit_def by blast
  have shape_bad: "accepted_transcript_shape s out as query_idxs"
    using bound unfolding accepted_with_bound_tables_def
      accepted_with_tables_def by simp
  have "as = staged_as"
    by (rule accepted_transcript_shape_alphas_unique[OF shape shape_bad])
  then show ?thesis
    using as_bad by blast
qed

lemma staged_security_with_data_alpha_bad_set_hit_imp_alpha_list_hit:
  assumes envelope: "\<And>trace_table. bad_sets trace_table \<subseteq> B"
    and hit: "staged_security_with_data_alpha_bad_set_hit bad_sets out"
  shows "staged_security_with_data_alpha_list_hit B out"
  using assms
  unfolding staged_security_with_data_alpha_bad_set_hit_def
    staged_security_with_data_alpha_list_hit_def
  by (auto split: option.splits prod.splits)

lemma staged_security_with_data_alpha_list_bound_from_transcript:
  assumes transcript_bound:
    "wp_event (staged_transcript_program A)
      (staged_transcript_alpha_list_hit B) adversary_initial_state \<le> C"
  shows
    "wp_event (staged_security_experiment_with_data A)
      (staged_security_with_data_alpha_list_hit B)
      adversary_initial_state \<le> C"
  unfolding staged_security_experiment_with_data_def
proof (rule wp_event_bind_bound_by_head_event[OF transcript_bound])
  show "staged_security_with_data_alpha_list_hit B None \<Longrightarrow>
    staged_transcript_alpha_list_hit B None"
    unfolding staged_security_with_data_alpha_list_hit_def
      staged_transcript_alpha_list_hit_def
    by simp
next
  fix data attacker_state out
  assume cont:
    "out \<in>
      set_dist
        (execute
          (get \<bind>
            (\<lambda>s. put
              (verifier_state_from_adversary s
                (staged_proof_transcript data)) \<bind>
              (\<lambda>_. verify_monad \<bind>
                (\<lambda>result. return (data, result)))))
          attacker_state)"
    and hit: "staged_security_with_data_alpha_list_hit B out"
  have data_bad: "staged_alphas data \<in> B"
  proof (cases out)
    case None
    then show ?thesis
      using hit unfolding staged_security_with_data_alpha_list_hit_def
      by simp
  next
    case (Some result)
    then obtain data' result' final_state where out_eq:
      "out = Some ((data', result'), final_state)"
      by (cases result, auto split: prod.splits)
    from cont[unfolded out_eq]
    obtain s3 where
      ret:
        "Some ((data', result'), final_state) \<in>
          set_dist (execute (return (data, result')) s3)"
      by (auto elim!: set_dist_bindE)
    have data'_eq: "data' = data"
      using ret by simp
    show ?thesis
      using hit unfolding out_eq data'_eq
        staged_security_with_data_alpha_list_hit_def
      by simp
  qed
  show "staged_transcript_alpha_list_hit B
      (Some (data, attacker_state))"
    using data_bad unfolding staged_transcript_alpha_list_hit_def by simp
qed

lemma staged_security_with_data_alpha_bad_set_bound_from_alpha_list:
  assumes envelope: "\<And>trace_table. bad_sets trace_table \<subseteq> B"
    and list_bound:
      "wp_event (staged_security_experiment_with_data A)
        (staged_security_with_data_alpha_list_hit B)
        adversary_initial_state \<le> C"
  shows
    "wp_event (staged_security_experiment_with_data A)
      (staged_security_with_data_alpha_bad_set_hit bad_sets)
      adversary_initial_state \<le> C"
proof -
  have "wp_event (staged_security_experiment_with_data A)
      (staged_security_with_data_alpha_bad_set_hit bad_sets)
      adversary_initial_state \<le>
    wp_event (staged_security_experiment_with_data A)
      (staged_security_with_data_alpha_list_hit B)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule staged_security_with_data_alpha_bad_set_hit_imp_alpha_list_hit
        [OF envelope])
  also have "... \<le> C"
    by (rule list_bound)
  finally show ?thesis .
qed

definition checked_staged_security_with_data_state_alpha_list_hit
  :: "'f list set \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_data_state_alpha_list_hit B out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, _), _), _) \<Rightarrow> staged_alphas data \<in> B)"

definition checked_staged_security_with_data_state_alpha_bad_set_hit
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_data_state_alpha_bad_set_hit bad_sets out
      \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, _), _), _) \<Rightarrow>
          (\<exists>trace_table. staged_alphas data \<in> bad_sets trace_table))"

definition checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
  :: "('f list \<Rightarrow> 'f list set) \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
      bad_sets out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), _), _) \<Rightarrow>
          (let s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in staged_alphas data \<in>
            alpha_header_supported_union_bad_sets s bad_sets
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)))"

lemma checked_staged_security_with_data_state_alpha_bad_set_hit_imp_alpha_list_hit:
  assumes envelope: "\<And>trace_table. bad_sets trace_table \<subseteq> B"
    and hit:
      "checked_staged_security_with_data_state_alpha_bad_set_hit bad_sets out"
  shows "checked_staged_security_with_data_state_alpha_list_hit B out"
  using assms
  unfolding checked_staged_security_with_data_state_alpha_bad_set_hit_def
    checked_staged_security_with_data_state_alpha_list_hit_def
  by (auto split: option.splits prod.splits)

lemma checked_staged_security_with_data_state_alpha_list_bound_from_transcript:
  assumes transcript_bound:
    "wp_event (checked_staged_transcript_program A)
      (staged_transcript_alpha_list_hit B) adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_list_hit B)
      adversary_initial_state \<le> C"
  unfolding checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_head_event[OF transcript_bound])
  show
    "checked_staged_security_with_data_state_alpha_list_hit B None \<Longrightarrow>
      staged_transcript_alpha_list_hit B None"
    unfolding checked_staged_security_with_data_state_alpha_list_hit_def
      staged_transcript_alpha_list_hit_def
    by simp
next
  fix data attacker_state out
  assume cont:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>s. put
                (verifier_state_from_adversary s
                  (staged_proof_transcript data)) \<bind>
                (\<lambda>_. verify_monad \<bind>
                  (\<lambda>result. return ((data, s), result)))))
            attacker_state)"
    and hit: "checked_staged_security_with_data_state_alpha_list_hit B out"
  have data_bad: "staged_alphas data \<in> B"
  proof (cases out)
    case None
    then show ?thesis
      using hit
      unfolding checked_staged_security_with_data_state_alpha_list_hit_def
      by simp
  next
    case (Some result_pack)
    then obtain data' attacker_state' result final_state where out_eq:
      "out = Some (((data', attacker_state'), result), final_state)"
      by (cases result_pack, auto split: prod.splits)
    from cont[unfolded out_eq]
    obtain saved_state state_after_get where
      ret:
        "Some (((data', attacker_state'), result), final_state) \<in>
          set_dist (execute (return ((data, saved_state), result))
            final_state)"
      by (auto elim!: set_dist_bindE)
    have data'_eq: "data' = data"
      using ret by simp
    show ?thesis
      using hit
      unfolding out_eq data'_eq
        checked_staged_security_with_data_state_alpha_list_hit_def
      by simp
  qed
  show "staged_transcript_alpha_list_hit B
      (Some (data, attacker_state))"
    using data_bad unfolding staged_transcript_alpha_list_hit_def by simp
qed

lemma checked_staged_security_with_data_state_alpha_bad_set_bound_from_alpha_list:
  assumes envelope: "\<And>trace_table. bad_sets trace_table \<subseteq> B"
    and list_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_list_hit B)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_bad_set_hit bad_sets)
      adversary_initial_state \<le> C"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_bad_set_hit bad_sets)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_list_hit B)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        checked_staged_security_with_data_state_alpha_bad_set_hit_imp_alpha_list_hit
        [OF envelope])
  also have "... \<le> C"
    by (rule list_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_composition_randomization_bad_imp_alpha_header_supported_bad_set_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        composition_randomization_bad out"
  shows
    "checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
      composition_trace_bad_alpha_space out"
proof (cases out)
  case None
  then show ?thesis
    using bad
    unfolding staged_security_with_data_state_verifier_event_def
    by simp
next
  case (Some result_pack)
  then obtain data attacker_state result final_state where out_eq:
    "out = Some (((data, attacker_state), result), final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have support_some:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    using support unfolding out_eq .
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support_some]
  have builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast+
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
  from bad[unfolded out_eq
      staged_security_with_data_state_verifier_event_def]
  have random_bad:
    "composition_randomization_bad ?s (Some (result, final_state))"
    by simp
  have alpha_hit:
    "alpha_bad_set_hit ?s composition_trace_bad_alpha_space
      (Some (result, final_state))"
    by (rule composition_randomization_bad_imp_alpha_bad_set_hit
        [OF random_bad])
  from alpha_hit obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and as_bad: "as \<in> composition_trace_bad_alpha_space trace_table"
    unfolding alpha_bad_set_hit_def by blast
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state))
      as query_idxs"
    using bound
    unfolding accepted_with_bound_tables_def accepted_with_tables_def
    by simp
  from shape obtain result' final_state' fr f_fri_roots f_final dg
      composition_fri_roots final rest where
    header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    by (elim accepted_transcript_shape_header_query_extraction)
  have as_eq: "as = staged_alphas data"
    using verifier_header_transcript_unique[OF staged_header header]
    by simp
  have bound_staged:
    "accepted_with_bound_tables ?s (Some (result, final_state))
      trace_table composition_table (staged_alphas data) query_idxs"
    using bound as_eq by simp
  have staged_bad:
    "staged_alphas data \<in> composition_trace_bad_alpha_space trace_table"
    using as_bad as_eq by simp
  have candidate:
    "trace_table \<in>
      alpha_header_supported_trace_table_candidates ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)"
    unfolding alpha_header_supported_trace_table_candidates_def
    using verifier bound_staged staged_header by blast
  have union_bad:
    "staged_alphas data \<in>
      alpha_header_supported_union_bad_sets ?s
        composition_trace_bad_alpha_space
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)"
    unfolding alpha_header_supported_union_bad_sets_def
    using candidate staged_bad
      composition_trace_bad_alpha_space_subset_alpha_space[of trace_table]
    by auto
  show ?thesis
    using union_bad
    unfolding out_eq
      checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit_def
    by simp
qed

lemma checked_staged_security_with_data_state_composition_randomization_bad_bound_from_alpha_header_supported_bad_set:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and alpha_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad)
      adversary_initial_state \<le> C"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_data_state_composition_randomization_bad_imp_alpha_header_supported_bad_set_hit_on_support
        [OF wf controlled])
  also have "... \<le> C"
    by (rule alpha_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_composition_randomization_bad_imp_alpha_bad_set_hit_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad:
      "staged_security_with_data_state_verifier_event
        composition_randomization_bad out"
  shows
    "checked_staged_security_with_data_state_alpha_bad_set_hit
      composition_trace_bad_alpha_space out"
proof (cases out)
  case None
  then show ?thesis
    using bad
    unfolding staged_security_with_data_state_verifier_event_def
    by simp
next
  case (Some result_pack)
  then obtain data attacker_state result final_state where out_eq:
    "out = Some (((data, attacker_state), result), final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have support_some:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
    using support unfolding out_eq .
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support_some]
  have builder:
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
  from bad[unfolded out_eq
      staged_security_with_data_state_verifier_event_def]
  have random_bad:
    "composition_randomization_bad ?s (Some (result, final_state))"
    by simp
  have alpha_hit:
    "alpha_bad_set_hit ?s composition_trace_bad_alpha_space
      (Some (result, final_state))"
    by (rule composition_randomization_bad_imp_alpha_bad_set_hit
        [OF random_bad])
  from alpha_hit obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and as_bad: "as \<in> composition_trace_bad_alpha_space trace_table"
    unfolding alpha_bad_set_hit_def by blast
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state))
      as query_idxs"
    using bound
    unfolding accepted_with_bound_tables_def accepted_with_tables_def
    by simp
  from shape obtain result' final_state' fr f_fri_roots f_final dg
      composition_fri_roots final rest where
    header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    by (elim accepted_transcript_shape_header_query_extraction)
  have as_eq: "as = staged_alphas data"
    using verifier_header_transcript_unique[OF staged_header header]
    by simp
  have staged_bad:
    "staged_alphas data \<in> composition_trace_bad_alpha_space trace_table"
    using as_bad as_eq by simp
  show ?thesis
    using staged_bad
    unfolding out_eq
      checked_staged_security_with_data_state_alpha_bad_set_hit_def
    by auto
qed

lemma checked_staged_security_with_data_state_composition_randomization_bad_bound_from_alpha_bad_set:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and alpha_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad)
      adversary_initial_state \<le> C"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (checked_staged_security_with_data_state_alpha_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_data_state_composition_randomization_bad_imp_alpha_bad_set_hit_on_support
        [OF wf controlled])
  also have "... \<le> C"
    by (rule alpha_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_composition_degree_bad_bound:
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_degree_bad)
      adversary_initial_state \<le> 0"
proof -
  have event_eq:
    "staged_security_with_data_state_verifier_event composition_degree_bad =
      (\<lambda>out :: ((('f staged_proof_data \<times> 'f protocol_channel) \<times>
          unit list) \<times> 'f protocol_channel) option. False)"
    by (rule ext)
      (auto simp: staged_security_with_data_state_verifier_event_def
        composition_degree_bad_false[OF spec_degree_wellformed_from_spec_query_margin]
        split: option.splits prod.splits)
  show ?thesis
    unfolding event_eq wp_event_def wp_def dist_expect_def by simp
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_alpha_bad_set:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and alpha_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> composition_error_bound"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le> composition_error_bound"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?degree =
    "staged_security_with_data_state_verifier_event composition_degree_bad"
  let ?random =
    "staged_security_with_data_state_verifier_event
      composition_randomization_bad"
  have event_eq:
    "staged_security_with_data_state_verifier_event composition_bad =
      (\<lambda>out. ?degree out \<or> ?random out)"
    by (rule ext)
      (auto simp: staged_security_with_data_state_verifier_event_def
        composition_bad_def split: option.splits prod.splits)
  have degree_bound:
    "wp_event ?M ?degree adversary_initial_state \<le> 0"
    by (rule
        checked_staged_security_with_data_state_composition_degree_bad_bound)
  have random_bound:
    "wp_event ?M ?random adversary_initial_state \<le>
      composition_error_bound"
    by (rule
        checked_staged_security_with_data_state_composition_randomization_bad_bound_from_alpha_bad_set
        [OF wf controlled alpha_bound])
  have "wp_event ?M
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
    wp_event ?M ?degree adversary_initial_state +
    wp_event ?M ?random adversary_initial_state"
    unfolding event_eq by (rule wp_event_union_bound)
  also have "... \<le> 0 + composition_error_bound"
    by (intro add_mono degree_bound random_bound)
  finally show ?thesis by simp
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_alpha_header_supported_bad_set:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and alpha_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> composition_error_bound"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le> composition_error_bound"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?degree =
    "staged_security_with_data_state_verifier_event composition_degree_bad"
  let ?random =
    "staged_security_with_data_state_verifier_event
      composition_randomization_bad"
  have event_eq:
    "staged_security_with_data_state_verifier_event composition_bad =
      (\<lambda>out. ?degree out \<or> ?random out)"
    by (rule ext)
      (auto simp: staged_security_with_data_state_verifier_event_def
        composition_bad_def split: option.splits prod.splits)
  have degree_bound:
    "wp_event ?M ?degree adversary_initial_state \<le> 0"
    by (rule
        checked_staged_security_with_data_state_composition_degree_bad_bound)
  have random_bound:
    "wp_event ?M ?random adversary_initial_state \<le>
      composition_error_bound"
    by (rule
        checked_staged_security_with_data_state_composition_randomization_bad_bound_from_alpha_header_supported_bad_set
        [OF wf controlled alpha_bound])
  have "wp_event ?M
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
    wp_event ?M ?degree adversary_initial_state +
    wp_event ?M ?random adversary_initial_state"
    unfolding event_eq by (rule wp_event_union_bound)
  also have "... \<le> 0 + composition_error_bound"
    by (intro add_mono degree_bound random_bound)
  finally show ?thesis by simp
qed

lemma checked_staged_security_with_data_state_composition_bad_bound_from_alpha_header_supported_bad_set_general:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and alpha_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (checked_staged_security_with_data_state_alpha_header_supported_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le> C"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?degree =
    "staged_security_with_data_state_verifier_event composition_degree_bad"
  let ?random =
    "staged_security_with_data_state_verifier_event
      composition_randomization_bad"
  have event_eq:
    "staged_security_with_data_state_verifier_event composition_bad =
      (\<lambda>out. ?degree out \<or> ?random out)"
    by (rule ext)
      (auto simp: staged_security_with_data_state_verifier_event_def
        composition_bad_def split: option.splits prod.splits)
  have degree_bound:
    "wp_event ?M ?degree adversary_initial_state \<le> 0"
    by (rule
        checked_staged_security_with_data_state_composition_degree_bad_bound)
  have random_bound:
    "wp_event ?M ?random adversary_initial_state \<le> C"
    by (rule
        checked_staged_security_with_data_state_composition_randomization_bad_bound_from_alpha_header_supported_bad_set
        [OF wf controlled alpha_bound])
  have "wp_event ?M
      (staged_security_with_data_state_verifier_event composition_bad)
      adversary_initial_state \<le>
    wp_event ?M ?degree adversary_initial_state +
    wp_event ?M ?random adversary_initial_state"
    unfolding event_eq by (rule wp_event_union_bound)
  also have "... \<le> 0 + C"
    by (intro add_mono degree_bound random_bound)
  finally show ?thesis by simp
qed

lemma staged_composition_alpha_header_supported_union_fraction_bound_if_no_pairwise_merkle_bad:
  assumes no_bad:
    "\<not> alpha_supported_pairwise_merkle_bad
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
  shows
    "nnreal
      (card
        (alpha_header_supported_union_bad_sets
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          composition_trace_bad_alpha_space
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data))) /
      nnreal (card alpha_space) \<le> composition_error_bound"
  by (rule
      composition_trace_alpha_header_supported_union_fraction_bound_if_unique_candidate)
    (rule
      alpha_header_supported_candidate_unique_if_no_global_pairwise_merkle_bad
      [OF no_bad])

lemma accepted_staged_security_experiment_fri_challengesE:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "out \<in> set_dist
        (execute (staged_security_experiment A) adversary_initial_state)"
    and accepted: "\<not> Option.is_none out"
  obtains result final_state data attacker_state where
    "out = Some (result, final_state)"
    "Some (data, attacker_state) \<in>
      set_dist (execute (staged_transcript_program A)
        adversary_initial_state)"
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    "accepted_fri_challenges
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))
      out
      (staged_trace_fri_challenges data)
      (staged_degree data)
      (staged_composition_fri_challenges data)"
proof -
  from accepted_staged_security_experiment_headerE
      [OF wf controlled outcome accepted]
  obtain result final_state data attacker_state where
    out_eq: "out = Some (result, final_state)"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist (execute (staged_transcript_program A)
          adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and staged_header:
      "verifier_header_transcript
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        (List.concat (staged_query_chunks data))"
    by blast
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from verify_monad_header_random_oracle_replay[OF verifier]
  obtain fr f_fl f_final as dg fl final query_state where
    header:
      "verifier_header_transcript ?s fr (map snd f_fl) f_final as dg
        (map snd fl) final (PTranscript query_state)"
    and query_state_eq:
      "PState query_state =
        verifier_header_state ?s fr (map snd f_fl) f_final as dg
          (map snd fl) final"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          query_state)"
    and query_count_header: "PQueryCounter query_state = PQueryCounter ?s"
    and ext_s_query: "?s \<le> query_state"
    and trace_lookup:
      "\<And>i. i < length f_fl \<Longrightarrow>
        fmlookup (HashMap query_state)
          (TraceFriChallenge (PTraceFriCounter ?s + i)
            (foldl concat (concat (PState ?s) fr)
              (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))"
    and alpha_lookup:
      "\<And>i. i < length as \<Longrightarrow>
        fmlookup (HashMap query_state)
          (AlphaChallenge (PAlphaCounter ?s + i) (foldl concat
            (concat (foldl concat (concat (PState ?s) fr) (map snd f_fl))
              f_final)
            (take i as))) =
          Some (as ! i)"
    and comp_lookup:
      "\<And>i. i < length fl \<Longrightarrow>
        fmlookup (HashMap query_state)
          (CompositionFriChallenge (PCompositionFriCounter ?s + i)
            (foldl concat
              (concat
                (foldl concat
                  (concat
                    (foldl concat (concat (PState ?s) fr) (map snd f_fl))
                    f_final)
                  as)
                dg)
              (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i))"
    and degree_bound: "to_nat dg \<le> maxDegree"
    by blast
  have header_unique:
    "fr = staged_trace_root data \<and>
     map snd f_fl = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     map snd fl = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     PTranscript query_state = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF staged_header header] by simp
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
    by (rule staged_transcript_program_outcome_shape
        [OF wf controlled builder])
  have trace_bs_eq:
    "map fst f_fl = staged_trace_fri_challenges data"
  proof (rule nth_equalityI)
    show "length (map fst f_fl) =
        length (staged_trace_fri_challenges data)"
      using header_unique shape by (metis length_map)
  next
    fix i
    assume i_bound: "i < length (map fst f_fl)"
    then have i_f_fl: "i < length f_fl"
      by simp
    have i_round: "i < ceil_log clength"
      using i_f_fl header_unique shape by (metis length_map)
    have staged_lookup_attacker:
      "fmlookup (HashMap attacker_state)
        (TraceFriChallenge i
          (foldl concat (staged_trace_fri_start_hash data)
            (take (Suc i) (staged_trace_fri_roots data)))) =
        Some (staged_trace_fri_challenges data ! i)"
      by (rule staged_transcript_program_outcome_trace_challenge_lookup
          [OF wf controlled builder i_round])
    have staged_lookup_s:
      "fmlookup (HashMap ?s)
        (TraceFriChallenge i
          (foldl concat (staged_trace_fri_start_hash data)
            (take (Suc i) (staged_trace_fri_roots data)))) =
        Some (staged_trace_fri_challenges data ! i)"
      using staged_lookup_attacker by simp
    have staged_lookup_query:
      "fmlookup (HashMap query_state)
        (TraceFriChallenge i
          (foldl concat (staged_trace_fri_start_hash data)
            (take (Suc i) (staged_trace_fri_roots data)))) =
        Some (staged_trace_fri_challenges data ! i)"
      by (rule hash_extension_lookup[OF staged_lookup_s ext_s_query])
    have verifier_lookup_query:
      "fmlookup (HashMap query_state)
        (TraceFriChallenge i
          (foldl concat (staged_trace_fri_start_hash data)
            (take (Suc i) (staged_trace_fri_roots data)))) =
        Some (fst (f_fl ! i))"
      using trace_lookup[OF i_f_fl] header_unique
      unfolding staged_trace_fri_start_hash_def
      by simp
    show "map fst f_fl ! i = staged_trace_fri_challenges data ! i"
      using verifier_lookup_query staged_lookup_query i_f_fl
      by simp
  qed
  have comp_bs_eq:
    "map fst fl = staged_composition_fri_challenges data"
  proof (rule nth_equalityI)
    show "length (map fst fl) =
        length (staged_composition_fri_challenges data)"
      using header_unique shape by (metis length_map)
  next
    fix i
    assume i_bound: "i < length (map fst fl)"
    then have i_fl: "i < length fl"
      by simp
    have i_round:
      "i < ceil_log (to_nat (staged_degree data) + 1)"
      using i_fl header_unique shape by (metis length_map)
    have staged_lookup_attacker:
      "fmlookup (HashMap attacker_state)
        (CompositionFriChallenge i
          (foldl concat (staged_composition_fri_start_hash data)
            (take (Suc i) (staged_composition_fri_roots data)))) =
        Some (staged_composition_fri_challenges data ! i)"
      by (rule staged_transcript_program_outcome_composition_challenge_lookup
          [OF wf controlled builder i_round])
    have staged_lookup_s:
      "fmlookup (HashMap ?s)
        (CompositionFriChallenge i
          (foldl concat (staged_composition_fri_start_hash data)
            (take (Suc i) (staged_composition_fri_roots data)))) =
        Some (staged_composition_fri_challenges data ! i)"
      using staged_lookup_attacker by simp
    have staged_lookup_query:
      "fmlookup (HashMap query_state)
        (CompositionFriChallenge i
          (foldl concat (staged_composition_fri_start_hash data)
            (take (Suc i) (staged_composition_fri_roots data)))) =
        Some (staged_composition_fri_challenges data ! i)"
      by (rule hash_extension_lookup[OF staged_lookup_s ext_s_query])
    have verifier_lookup_query:
      "fmlookup (HashMap query_state)
        (CompositionFriChallenge i
          (foldl concat (staged_composition_fri_start_hash data)
            (take (Suc i) (staged_composition_fri_roots data)))) =
        Some (fst (fl ! i))"
      using comp_lookup[OF i_fl] header_unique
      unfolding staged_composition_fri_start_hash_def
        staged_trace_fri_start_hash_def
      by simp
    show "map fst fl ! i =
        staged_composition_fri_challenges data ! i"
      using verifier_lookup_query staged_lookup_query i_fl
      by simp
  qed
  have trace_lookup_all:
    "\<forall>i < length f_fl.
      fmlookup (HashMap query_state)
        (TraceFriChallenge (PTraceFriCounter ?s + i)
          (foldl concat (concat (PState ?s) fr)
            (take (Suc i) (map snd f_fl)))) =
      Some (fst (f_fl ! i))"
    using trace_lookup by blast
  have comp_lookup_all:
    "\<forall>i < length fl.
      fmlookup (HashMap query_state)
        (CompositionFriChallenge (PCompositionFriCounter ?s + i)
          (foldl concat
            (concat
              (foldl concat
                (concat
                  (foldl concat (concat (PState ?s) fr) (map snd f_fl))
                  f_final)
                as)
              dg)
            (take (Suc i) (map snd fl)))) =
      Some (fst (fl ! i))"
    using comp_lookup by blast
  have challenges:
    "accepted_fri_challenges ?s (Some (result, final_state))
      (staged_trace_fri_challenges data)
      (staged_degree data)
      (staged_composition_fri_challenges data)"
    unfolding accepted_fri_challenges_def
    by (intro exI[of _ result] exI[of _ final_state] exI[of _ fr]
        exI[of _ f_fl] exI[of _ f_final] exI[of _ as] exI[of _ fl]
        exI[of _ final] exI[of _ query_state])
      (use header query_state_eq query_out query_count_header
        header_unique trace_bs_eq comp_bs_eq trace_lookup_all comp_lookup_all
        in simp)
  have challenges_out:
    "accepted_fri_challenges ?s out
      (staged_trace_fri_challenges data)
      (staged_degree data)
      (staged_composition_fri_challenges data)"
    using challenges out_eq by simp
  show ?thesis
    by (rule that[OF out_eq builder verifier challenges_out])
qed

lemma staged_budget_trace_length:
  assumes "staged_budget_wellformed budgets"
  shows "length (trace_fri_budgets budgets) = ceil_log clength"
  using assms unfolding staged_budget_wellformed_def by simp

lemma staged_budget_composition_length:
  assumes "staged_budget_wellformed budgets"
  shows
    "length (composition_fri_budgets budgets) =
      ceil_log (maxDegree + 1)"
  using assms unfolding staged_budget_wellformed_def by simp

lemma staged_budget_query_length:
  assumes "staged_budget_wellformed budgets"
  shows "length (query_opening_budgets budgets) = rounds"
  using assms unfolding staged_budget_wellformed_def by simp

lemma staged_trace_fri_search_queries_le_total:
  assumes wf: "staged_budget_wellformed budgets"
    and i_bound: "i < ceil_log clength"
  shows
    "staged_trace_fri_search_queries budgets i \<le>
      staged_attacker_query_budget budgets + staged_challenge_query_budget"
proof -
  have take_le:
    "sum_list (take (Suc i) (trace_fri_budgets budgets)) \<le>
      sum_list (trace_fri_budgets budgets)"
    by (rule sum_list_take_le)
  have i_le: "i \<le> ceil_log clength"
    using i_bound by simp
  show ?thesis
    unfolding staged_trace_fri_search_queries_def
      staged_attacker_query_budget_def staged_challenge_query_budget_def
    using take_le i_le by simp
qed

lemma staged_alpha_search_queries_le_total:
  assumes "i \<le> length spec"
  shows
    "staged_alpha_search_queries budgets i \<le>
      staged_attacker_query_budget budgets + staged_challenge_query_budget"
  unfolding staged_alpha_search_queries_def
    staged_attacker_query_budget_def staged_challenge_query_budget_def
  using assms by simp

lemma staged_composition_fri_search_queries_le_total:
  assumes wf: "staged_budget_wellformed budgets"
    and i_bound: "i < ceil_log (maxDegree + 1)"
  shows
    "staged_composition_fri_search_queries budgets i \<le>
      staged_attacker_query_budget budgets + staged_challenge_query_budget"
proof -
  have take_le:
    "sum_list (take (Suc i) (composition_fri_budgets budgets)) \<le>
      sum_list (composition_fri_budgets budgets)"
    by (rule sum_list_take_le)
  have i_le: "i \<le> ceil_log (maxDegree + 1)"
    using i_bound by simp
  show ?thesis
    unfolding staged_composition_fri_search_queries_def
      staged_attacker_query_budget_def staged_challenge_query_budget_def
    using take_le i_le by simp
qed

lemma staged_query_search_queries_le_total:
  assumes wf: "staged_budget_wellformed budgets"
    and i_bound: "i < rounds"
  shows
    "staged_query_search_queries budgets i \<le>
      staged_attacker_query_budget budgets + staged_challenge_query_budget"
proof -
  have take_le:
    "sum_list (take i (query_opening_budgets budgets)) \<le>
      sum_list (query_opening_budgets budgets)"
    by (rule sum_list_take_le)
  have i_le: "i \<le> rounds"
    using i_bound by simp
  show ?thesis
    unfolding staged_query_search_queries_def
      staged_attacker_query_budget_def staged_challenge_query_budget_def
    using take_le i_le by simp
qed

lemma staged_phase_relation_error_mono:
  assumes "q \<le> r"
  shows
    "staged_phase_relation_error fiber_bound q \<le>
      staged_phase_relation_error fiber_bound r"
  unfolding staged_phase_relation_error_def
  by (rule hash_relation_budget_value_mono[OF assms])

lemma staged_phase_target_error_mono:
  assumes "q \<le> r"
  shows "staged_phase_target_error B q \<le> staged_phase_target_error B r"
  unfolding staged_phase_target_error_def
  by (rule hash_target_budget_value_mono[OF assms])

lemma staged_phase_target_error_card_mono:
  assumes "card B \<le> b"
  shows "staged_phase_target_error B q \<le>
    staged_phase_relation_error b q"
  unfolding staged_phase_target_error_def staged_phase_relation_error_def
    hash_target_budget_value_def hash_relation_budget_value_def
  apply (subst nn2real_le_iff[symmetric])
  using assms by (simp add: divide_right_mono mult_left_mono)

lemma staged_dynamic_query_set_subset:
  "query_header_supported_union_good_sets
    (verifier_state_from_adversary attacker_state
      (staged_proof_transcript data))
    query_sampling_success_space
    (staged_trace_root data)
    (staged_trace_fri_roots data)
    (staged_trace_final data)
    (staged_alphas data)
    (staged_degree data)
    (staged_composition_fri_roots data)
    (staged_composition_final data) \<subseteq> query_sample_space"
  by (rule query_header_supported_union_good_sets_subset)

lemma staged_dynamic_query_set_envelope_fraction_bound_if_no_pairwise_merkle_bad:
  assumes no_bad:
    "\<not> query_supported_pairwise_merkle_bad
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data))"
  shows
    "nnreal
      (query_raw_preimage_card_envelope
        (card
          (query_header_supported_union_good_sets
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data))
            query_sampling_success_space
            (staged_trace_root data)
            (staged_trace_fri_roots data)
            (staged_trace_final data)
            (staged_alphas data)
            (staged_degree data)
            (staged_composition_fri_roots data)
            (staged_composition_final data)))) /
      nnreal size \<le> query_error_bound"
  by (rule
      query_header_supported_union_good_sets_fraction_bound_if_no_global_pairwise_merkle_bad
      [OF no_bad query_sampling_success_space_subset
        query_sampling_success_space_envelope_fraction_bound])

lemma staged_dynamic_query_set_target_error_bound_if_no_pairwise_merkle_bad:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and no_bad:
      "\<not> query_supported_pairwise_merkle_bad
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows
    "staged_phase_target_error
      (query_index_raw_preimage
        (query_header_supported_union_good_sets
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          query_sampling_success_space
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data))) q \<le>
      nnreal q * query_error_bound"
  by (rule staged_phase_query_index_target_error_query_bound
      [OF raw_bound staged_dynamic_query_set_subset
        staged_dynamic_query_set_envelope_fraction_bound_if_no_pairwise_merkle_bad
          [OF no_bad]])

lemma staged_alpha_prefix_receive_bad_vector_position_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < length spec"
    and absent:
      "alpha_challenge_values_absent
        (fri_vector_position_values B i) s"
  shows
    "wp_event
      (staged_alpha_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_alpha_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (a, _) \<Rightarrow> a \<in> fri_vector_position_values B i) s \<le>
      staged_phase_target_error (fri_vector_position_values B i)
        (Suc (staged_alpha_search_queries budgets i))"
  by (rule staged_alpha_prefix_receive_bad_value_bound
      [OF wf controlled _ absent])
    (use i_bound in simp)

lemma staged_alpha_prefix_receive_bad_vector_position_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "B \<subseteq> fri_challenge_space (length spec)"
    and i_bound: "i < length spec"
    and absent:
      "alpha_challenge_values_absent
        (fri_vector_position_values B i) s"
  shows
    "wp_event
      (staged_alpha_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_alpha_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (a, _) \<Rightarrow> a \<in> fri_vector_position_values B i) s \<le>
      staged_phase_relation_error (card B)
        (Suc (staged_alpha_search_queries budgets i))"
proof -
  have target:
    "wp_event
      (staged_alpha_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_alpha_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (a, _) \<Rightarrow> a \<in> fri_vector_position_values B i) s \<le>
      staged_phase_target_error (fri_vector_position_values B i)
        (Suc (staged_alpha_search_queries budgets i))"
    by (rule staged_alpha_prefix_receive_bad_vector_position_bound
        [OF wf controlled i_bound absent])
  also have "... \<le>
      staged_phase_relation_error (card B)
        (Suc (staged_alpha_search_queries budgets i))"
    by (rule staged_phase_target_error_card_mono)
      (rule fri_vector_position_values_card_le[OF subset i_bound])
  finally show ?thesis .
qed

lemma staged_alpha_prefix_receive_bad_vector_position_relation_bound_total:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "B \<subseteq> fri_challenge_space (length spec)"
    and i_bound: "i < length spec"
    and absent:
      "alpha_challenge_values_absent
        (fri_vector_position_values B i) s"
  shows
    "wp_event
      (staged_alpha_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_alpha_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (a, _) \<Rightarrow> a \<in> fri_vector_position_values B i) s \<le>
      staged_phase_relation_error (card B)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
proof -
  have local:
    "wp_event
      (staged_alpha_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_alpha_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (a, _) \<Rightarrow> a \<in> fri_vector_position_values B i) s \<le>
      staged_phase_relation_error (card B)
        (Suc (staged_alpha_search_queries budgets i))"
    by (rule staged_alpha_prefix_receive_bad_vector_position_relation_bound
        [OF wf controlled subset i_bound absent])
  also have
    "staged_phase_relation_error (card B)
        (Suc (staged_alpha_search_queries budgets i)) \<le>
      staged_phase_relation_error (card B)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
    by (rule staged_phase_relation_error_mono)
      (simp add: staged_alpha_search_queries_le_total[OF less_imp_le[OF i_bound]])
  finally show ?thesis .
qed

lemma staged_alpha_prefix_receive_keep_prefix_bad_vector_position_relation_bound_total:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "B \<subseteq> fri_challenge_space (length spec)"
    and i_bound: "i < length spec"
    and absent:
      "alpha_challenge_values_absent
        (fri_vector_position_values B i) s"
  shows
    "wp_event
      (staged_alpha_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. receive_alpha_challenge \<bind>
          (\<lambda>a. return (prefix, a))))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some ((_, a), _) \<Rightarrow> a \<in> fri_vector_position_values B i) s \<le>
      staged_phase_relation_error (card B)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
proof -
  let ?P =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (a, _) \<Rightarrow> a \<in> fri_vector_position_values B i"
  let ?Q =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some ((_, a), _) \<Rightarrow> a \<in> fri_vector_position_values B i"
  have cont_eq:
    "\<And>prefix t. wp_event
      (receive_alpha_challenge \<bind> (\<lambda>a. return (prefix, a))) ?Q t =
      wp_event receive_alpha_challenge ?P t"
  proof -
    fix prefix t
    show "wp_event
        (receive_alpha_challenge \<bind> (\<lambda>a. return (prefix, a))) ?Q t =
      wp_event receive_alpha_challenge ?P t"
      unfolding wp_event_def
      apply (subst wp_bind)
      apply (rule arg_cong[where
        f="\<lambda>Q. wp receive_alpha_challenge Q t"])
      apply (rule ext)
      apply (simp add: wp_return split: option.splits prod.splits)
      done
  qed
  have eq:
    "wp_event
      (staged_alpha_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. receive_alpha_challenge \<bind>
          (\<lambda>a. return (prefix, a)))) ?Q s =
      wp_event
        (staged_alpha_challenge_prefix_program A i \<bind>
          (\<lambda>_. receive_alpha_challenge)) ?P s"
    by (rule wp_event_bind_cong_cont) (simp_all add: cont_eq)
  show ?thesis
    unfolding eq
    by (rule staged_alpha_prefix_receive_bad_vector_position_relation_bound_total
        [OF wf controlled subset i_bound absent])
qed

lemma staged_alpha_prefix_bad_trace_vector_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and nonempty: "0 < ceil_log clength"
    and absent:
      "\<And>i. i < ceil_log clength \<Longrightarrow>
        trace_fri_challenge_values_absent
          (fri_vector_position_values B i) s"
  shows
    "wp_event (staged_alpha_prefix_program A)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some ((_, _, trace_bs, _), _) \<Rightarrow> trace_bs \<in> B) s \<le>
      nnreal (ceil_log clength) *
        staged_phase_relation_error (card B)
          (staged_alpha_search_queries budgets 0)"
proof -
  let ?coord =
    "\<lambda>i out. case out of None \<Rightarrow> False
      | Some ((_, _, trace_bs, _), _) \<Rightarrow>
          trace_bs ! i \<in> fri_vector_position_values B i"
  have cover:
    "wp_event (staged_alpha_prefix_program A)
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some ((_, _, trace_bs, _), _) \<Rightarrow> trace_bs \<in> B) s \<le>
      (\<Sum>i < ceil_log clength.
        wp_event (staged_alpha_prefix_program A) (?coord i) s)"
    by (rule staged_alpha_prefix_bad_trace_vector_coordinate_cover_bound
        [OF subset nonempty])
  also have "... \<le>
      (\<Sum>i < ceil_log clength.
        staged_phase_relation_error (card B)
          (staged_alpha_search_queries budgets 0))"
  proof (rule sum_mono)
    fix i
    assume i_in: "i \<in> {..<ceil_log clength}"
    then have i_bound: "i < ceil_log clength"
      by simp
    have target:
      "wp_event (staged_alpha_prefix_program A) (?coord i) s \<le>
        staged_phase_target_error (fri_vector_position_values B i)
          (staged_alpha_search_queries budgets 0)"
      by (rule staged_alpha_prefix_trace_coordinate_bound
          [OF wf controlled i_bound absent[OF i_bound]])
    also have "... \<le>
        staged_phase_relation_error (card B)
          (staged_alpha_search_queries budgets 0)"
      by (rule staged_phase_target_error_card_mono)
        (rule fri_vector_position_values_card_le[OF subset i_bound])
    finally show
      "wp_event (staged_alpha_prefix_program A) (?coord i) s \<le>
        staged_phase_relation_error (card B)
          (staged_alpha_search_queries budgets 0)" .
  qed
  also have "... =
      nnreal (ceil_log clength) *
        staged_phase_relation_error (card B)
          (staged_alpha_search_queries budgets 0)"
    by simp
  finally show ?thesis .
qed

lemma staged_transcript_program_trace_fri_vector_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and nonempty: "0 < ceil_log clength"
    and absent:
      "\<And>i. i < ceil_log clength \<Longrightarrow>
        trace_fri_challenge_values_absent
          (fri_vector_position_values B i) adversary_initial_state"
  shows
    "wp_event (staged_transcript_program A)
      (staged_transcript_trace_fri_vector_hit B)
      adversary_initial_state \<le>
      nnreal (ceil_log clength) *
        staged_phase_relation_error (card B)
          (staged_alpha_search_queries budgets 0)"
proof -
  let ?Head =
    "\<lambda>out. case out of
      None \<Rightarrow> False
    | Some ((_, _, trace_bs, _), _) \<Rightarrow> trace_bs \<in> B"
  have prefix_bound:
    "wp_event (staged_alpha_prefix_program A) ?Head
      adversary_initial_state \<le>
      nnreal (ceil_log clength) *
        staged_phase_relation_error (card B)
          (staged_alpha_search_queries budgets 0)"
    by (rule staged_alpha_prefix_bad_trace_vector_bound
        [OF wf controlled subset nonempty absent])
  show ?thesis
    unfolding staged_transcript_program_alpha_prefix_decomp
  proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
    show "staged_transcript_trace_fri_vector_hit B None \<Longrightarrow>
      ?Head None"
      unfolding staged_transcript_trace_fri_vector_hit_def by simp
  next
    fix x t out
    assume cont:
      "out \<in>
        set_dist
          (execute (staged_after_alpha_prefix_program A x) t)"
      and hit: "staged_transcript_trace_fri_vector_hit B out"
    obtain fr trace_roots trace_bs trace_final where x_eq:
      "x = (fr, trace_roots, trace_bs, trace_final)"
      by (cases x) auto
    have trace_bs_in: "trace_bs \<in> B"
      by (rule staged_after_alpha_prefix_program_trace_fri_vector_hitD
          [OF cont[unfolded x_eq] hit])
    show "?Head (Some (x, t))"
      unfolding x_eq
      using trace_bs_in by simp
  qed
qed

lemma staged_security_with_data_trace_fri_vector_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and nonempty: "0 < ceil_log clength"
    and absent:
      "\<And>i. i < ceil_log clength \<Longrightarrow>
        trace_fri_challenge_values_absent
          (fri_vector_position_values B i) adversary_initial_state"
  shows
    "wp_event (staged_security_experiment_with_data A)
      (staged_security_with_data_trace_fri_vector_hit B)
      adversary_initial_state \<le>
      nnreal (ceil_log clength) *
        staged_phase_relation_error (card B)
          (staged_alpha_search_queries budgets 0)"
proof -
  have transcript_bound:
    "wp_event (staged_transcript_program A)
      (staged_transcript_trace_fri_vector_hit B)
      adversary_initial_state \<le>
      nnreal (ceil_log clength) *
        staged_phase_relation_error (card B)
          (staged_alpha_search_queries budgets 0)"
    by (rule staged_transcript_program_trace_fri_vector_bound
        [OF wf controlled subset nonempty absent])
  show ?thesis
    unfolding staged_security_experiment_with_data_def
  proof (rule wp_event_bind_bound_by_head_event[OF transcript_bound])
    show "staged_security_with_data_trace_fri_vector_hit B None \<Longrightarrow>
      staged_transcript_trace_fri_vector_hit B None"
      unfolding staged_security_with_data_trace_fri_vector_hit_def
        staged_transcript_trace_fri_vector_hit_def
      by simp
  next
    fix data attacker_state out
    assume cont:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>s. put
                (verifier_state_from_adversary s
                  (staged_proof_transcript data)) \<bind>
                (\<lambda>_. verify_monad \<bind>
                  (\<lambda>result. return (data, result)))))
            attacker_state)"
      and hit: "staged_security_with_data_trace_fri_vector_hit B out"
    have data_bad: "staged_trace_fri_challenges data \<in> B"
    proof (cases out)
      case None
      then show ?thesis
        using hit unfolding staged_security_with_data_trace_fri_vector_hit_def
        by simp
    next
      case (Some result)
      then obtain data' result' final_state where out_eq:
        "out = Some ((data', result'), final_state)"
        by (cases result, auto split: prod.splits)
      from cont[unfolded out_eq]
      obtain s1 s2 s3 where
        ret:
          "Some ((data', result'), final_state) \<in>
            set_dist (execute (return (data, result')) s3)"
        by (auto elim!: set_dist_bindE)
      have data'_eq: "data' = data"
        using ret by simp
      show ?thesis
        using hit unfolding out_eq data'_eq
          staged_security_with_data_trace_fri_vector_hit_def
        by simp
    qed
    show "staged_transcript_trace_fri_vector_hit B
        (Some (data, attacker_state))"
      using data_bad unfolding staged_transcript_trace_fri_vector_hit_def
      by simp
  qed
qed

lemma staged_security_with_data_composition_fri_vector_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and absent:
      "\<And>i. i < ceil_log (maxDegree + 1) \<Longrightarrow>
        composition_fri_challenge_values_absent
          (\<Union>dg. fri_vector_position_values (B dg) i)
          adversary_initial_state"
  shows
    "wp_event (staged_security_experiment_with_data A)
      (staged_security_with_data_composition_fri_vector_guarded_hit B)
      adversary_initial_state \<le>
      (\<Sum>i < ceil_log (maxDegree + 1).
        staged_phase_target_error
          (\<Union>dg. fri_vector_position_values (B dg) i)
          (staged_composition_fri_vector_search_queries budgets))"
proof -
  have transcript_bound:
    "wp_event (staged_transcript_program A)
      (staged_transcript_composition_fri_vector_guarded_hit B)
      adversary_initial_state \<le>
      (\<Sum>i < ceil_log (maxDegree + 1).
        staged_phase_target_error
          (\<Union>dg. fri_vector_position_values (B dg) i)
          (staged_composition_fri_vector_search_queries budgets))"
    by (rule staged_transcript_program_composition_fri_vector_bound
        [OF wf controlled subset absent])
  show ?thesis
    unfolding staged_security_experiment_with_data_def
  proof (rule wp_event_bind_bound_by_head_event[OF transcript_bound])
    show
      "staged_security_with_data_composition_fri_vector_guarded_hit B None
        \<Longrightarrow> staged_transcript_composition_fri_vector_guarded_hit B None"
      unfolding
        staged_security_with_data_composition_fri_vector_guarded_hit_def
        staged_transcript_composition_fri_vector_guarded_hit_def
      by simp
  next
    fix data attacker_state out
    assume cont:
      "out \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>s. put
                (verifier_state_from_adversary s
                  (staged_proof_transcript data)) \<bind>
                (\<lambda>_. verify_monad \<bind>
                  (\<lambda>result. return (data, result)))))
            attacker_state)"
      and hit:
        "staged_security_with_data_composition_fri_vector_guarded_hit B out"
    have data_bad:
      "staged_composition_fri_challenges data \<in>
        B (staged_degree data) \<and>
       0 < ceil_log (to_nat (staged_degree data) + 1) \<and>
       ceil_log (to_nat (staged_degree data) + 1) \<le>
        ceil_log (maxDegree + 1)"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          staged_security_with_data_composition_fri_vector_guarded_hit_def
        by simp
    next
      case (Some result)
      then obtain data' result' final_state where out_eq:
        "out = Some ((data', result'), final_state)"
        by (cases result, auto split: prod.splits)
      from cont[unfolded out_eq]
      obtain s1 s2 s3 where
        ret:
          "Some ((data', result'), final_state) \<in>
            set_dist (execute (return (data, result')) s3)"
        by (auto elim!: set_dist_bindE)
      have data'_eq: "data' = data"
        using ret by simp
      show ?thesis
        using hit unfolding out_eq data'_eq
          staged_security_with_data_composition_fri_vector_guarded_hit_def
        by simp
    qed
    show "staged_transcript_composition_fri_vector_guarded_hit B
        (Some (data, attacker_state))"
      using data_bad
      unfolding staged_transcript_composition_fri_vector_guarded_hit_def
      by simp
  qed
qed

lemma staged_trace_fri_prefix_receive_bad_value_bound_total:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < ceil_log clength"
    and absent: "trace_fri_challenge_values_absent B s"
  shows
    "wp_event
      (staged_trace_fri_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_trace_fri_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (b, _) \<Rightarrow> b \<in> B) s \<le>
      staged_phase_target_error B
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
proof -
  have i_len: "i < length (trace_fri_budgets budgets)"
    using wf i_bound unfolding staged_budget_wellformed_def by simp
  have local:
    "wp_event
      (staged_trace_fri_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_trace_fri_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (b, _) \<Rightarrow> b \<in> B) s \<le>
      staged_phase_target_error B
        (Suc (staged_trace_fri_search_queries budgets i))"
    by (rule staged_trace_fri_prefix_receive_bad_value_bound
        [OF controlled i_len absent])
  also have
    "staged_phase_target_error B
        (Suc (staged_trace_fri_search_queries budgets i)) \<le>
      staged_phase_target_error B
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
    by (rule staged_phase_target_error_mono)
      (simp add: staged_trace_fri_search_queries_le_total[OF wf i_bound])
  finally show ?thesis .
qed

lemma staged_trace_fri_prefix_receive_bad_vector_position_bound_total:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < ceil_log clength"
    and absent:
      "trace_fri_challenge_values_absent
        (fri_vector_position_values B i) s"
  shows
    "wp_event
      (staged_trace_fri_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_trace_fri_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i) s \<le>
      staged_phase_target_error (fri_vector_position_values B i)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
  by (rule staged_trace_fri_prefix_receive_bad_value_bound_total
      [OF wf controlled i_bound absent])

lemma staged_trace_fri_prefix_receive_bad_vector_position_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and i_bound: "i < ceil_log clength"
    and absent:
      "trace_fri_challenge_values_absent
        (fri_vector_position_values B i) s"
  shows
    "wp_event
      (staged_trace_fri_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_trace_fri_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i) s \<le>
      staged_phase_relation_error (card B)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
proof -
  have target:
    "wp_event
      (staged_trace_fri_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_trace_fri_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i) s \<le>
      staged_phase_target_error (fri_vector_position_values B i)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
    by (rule staged_trace_fri_prefix_receive_bad_vector_position_bound_total
        [OF wf controlled i_bound absent])
  also have "... \<le>
      staged_phase_relation_error (card B)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
    by (rule staged_phase_target_error_card_mono)
      (rule fri_vector_position_values_card_le[OF subset i_bound])
  finally show ?thesis .
qed

lemma staged_trace_fri_prefix_receive_keep_prefix_bad_vector_position_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and i_bound: "i < ceil_log clength"
    and absent:
      "trace_fri_challenge_values_absent
        (fri_vector_position_values B i) s"
  shows
    "wp_event
      (staged_trace_fri_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. receive_trace_fri_challenge \<bind>
          (\<lambda>b. return (prefix, b))))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some ((_, b), _) \<Rightarrow> b \<in> fri_vector_position_values B i) s \<le>
      staged_phase_relation_error (card B)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
proof -
  let ?P =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i"
  let ?Q =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some ((_, b), _) \<Rightarrow> b \<in> fri_vector_position_values B i"
  have cont_eq:
    "\<And>prefix t. wp_event
      (receive_trace_fri_challenge \<bind> (\<lambda>b. return (prefix, b))) ?Q t =
      wp_event receive_trace_fri_challenge ?P t"
  proof -
    fix prefix t
    show "wp_event
        (receive_trace_fri_challenge \<bind> (\<lambda>b. return (prefix, b))) ?Q t =
      wp_event receive_trace_fri_challenge ?P t"
      unfolding wp_event_def
      apply (subst wp_bind)
      apply (rule arg_cong[where
        f="\<lambda>Q. wp receive_trace_fri_challenge Q t"])
      apply (rule ext)
      apply (simp add: wp_return split: option.splits prod.splits)
      done
  qed
  have eq:
    "wp_event
      (staged_trace_fri_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. receive_trace_fri_challenge \<bind>
          (\<lambda>b. return (prefix, b)))) ?Q s =
      wp_event
        (staged_trace_fri_challenge_prefix_program A i \<bind>
          (\<lambda>_. receive_trace_fri_challenge)) ?P s"
    by (rule wp_event_bind_cong_cont) (simp_all add: cont_eq)
  show ?thesis
    unfolding eq
    by (rule staged_trace_fri_prefix_receive_bad_vector_position_relation_bound
        [OF wf controlled subset i_bound absent])
qed

lemma staged_trace_fri_bad_vector_coordinate_sum_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and absent:
      "\<And>i. i < ceil_log clength \<Longrightarrow>
        trace_fri_challenge_values_absent
          (fri_vector_position_values B i) s"
  shows
    "(\<Sum>i < ceil_log clength.
      wp_event
        (staged_trace_fri_challenge_prefix_program A i \<bind>
          (\<lambda>_. receive_trace_fri_challenge))
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i) s) \<le>
      nnreal (ceil_log clength) *
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget))"
proof -
  have
    "(\<Sum>i < ceil_log clength.
      wp_event
        (staged_trace_fri_challenge_prefix_program A i \<bind>
          (\<lambda>_. receive_trace_fri_challenge))
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i) s) \<le>
      (\<Sum>i < ceil_log clength.
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget)))"
    by (rule sum_mono)
      (rule staged_trace_fri_prefix_receive_bad_vector_position_relation_bound
        [OF wf controlled subset], simp_all add: absent)
  also have "... =
      nnreal (ceil_log clength) *
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget))"
    by simp
  finally show ?thesis .
qed

lemma staged_trace_fri_bad_vector_coordinate_sum_keep_prefix_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and absent:
      "\<And>i. i < ceil_log clength \<Longrightarrow>
        trace_fri_challenge_values_absent
          (fri_vector_position_values B i) s"
  shows
    "(\<Sum>i < ceil_log clength.
      wp_event
        (staged_trace_fri_challenge_prefix_program A i \<bind>
          (\<lambda>prefix. receive_trace_fri_challenge \<bind>
            (\<lambda>b. return (prefix, b))))
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some ((_, b), _) \<Rightarrow>
              b \<in> fri_vector_position_values B i) s) \<le>
      nnreal (ceil_log clength) *
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget))"
proof -
  have
    "(\<Sum>i < ceil_log clength.
      wp_event
        (staged_trace_fri_challenge_prefix_program A i \<bind>
          (\<lambda>prefix. receive_trace_fri_challenge \<bind>
            (\<lambda>b. return (prefix, b))))
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some ((_, b), _) \<Rightarrow>
              b \<in> fri_vector_position_values B i) s) \<le>
      (\<Sum>i < ceil_log clength.
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget)))"
    by (rule sum_mono)
      (rule
        staged_trace_fri_prefix_receive_keep_prefix_bad_vector_position_relation_bound
        [OF wf controlled subset], simp_all add: absent)
  also have "... =
      nnreal (ceil_log clength) *
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget))"
    by simp
  finally show ?thesis .
qed

lemma staged_query_prefix_bad_index_error_mono:
  assumes i_bound: "i < rounds"
    and wf: "staged_budget_wellformed budgets"
  shows
    "staged_query_prefix_bad_index_error budgets B i \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  unfolding staged_query_prefix_bad_index_error_def
  by (rule staged_phase_target_error_mono)
    (rule staged_query_search_queries_le_total[OF wf i_bound])

lemma staged_query_prefix_bad_index_target_bound_total:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event (staged_query_challenge_prefix_program A i)
      (hash_new_output_hit_event (query_index_raw_preimage B) s) s \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  have local:
    "wp_event (staged_query_challenge_prefix_program A i)
      (hash_new_output_hit_event (query_index_raw_preimage B) s) s \<le>
      staged_query_prefix_bad_index_error budgets B i"
    by (rule staged_query_prefix_bad_index_target_bound)
      (use wf controlled i_bound in simp_all)
  also have
    "staged_query_prefix_bad_index_error budgets B i \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule staged_query_prefix_bad_index_error_mono[OF i_bound wf])
  finally show ?thesis .
qed

lemma checked_staged_query_prefix_bad_index_target_bound_total:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event (checked_staged_query_challenge_prefix_program A i)
      (hash_new_output_hit_event (query_index_raw_preimage B) s) s \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  have local:
    "wp_event (checked_staged_query_challenge_prefix_program A i)
      (hash_new_output_hit_event (query_index_raw_preimage B) s) s \<le>
      staged_query_prefix_bad_index_error budgets B i"
    by (rule checked_staged_query_prefix_bad_index_target_bound)
      (use wf controlled i_bound in simp_all)
  also have
    "staged_query_prefix_bad_index_error budgets B i \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
    by (rule staged_query_prefix_bad_index_error_mono[OF i_bound wf])
  finally show ?thesis .
qed

lemma staged_query_prefix_receive_bad_index_bound_total:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and absent: "query_index_raw_preimage_absent B s"
  shows
    "wp_event
      (staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_query_index_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B) s \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
proof -
  have local:
    "wp_event
      (staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_query_index_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B) s \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (Suc (staged_query_search_queries budgets i))"
    by (rule staged_query_prefix_receive_bad_index_bound)
      (use wf controlled i_bound absent in simp_all)
  also have
    "staged_phase_target_error (query_index_raw_preimage B)
        (Suc (staged_query_search_queries budgets i)) \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
    by (rule staged_phase_target_error_mono)
      (simp add: staged_query_search_queries_le_total[OF wf i_bound])
  finally show ?thesis .
qed

lemma staged_query_prefix_receive_bad_index_query_bound_total:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and absent: "query_index_raw_preimage_absent B s"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and envelope:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le> C"
  shows
    "wp_event
      (staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_query_index_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B) s \<le>
      nnreal
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) * C"
proof -
  have local:
    "wp_event
      (staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_query_index_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (raw, _) \<Rightarrow> index (to_nat raw) \<in> B) s \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
    by (rule staged_query_prefix_receive_bad_index_bound_total
        [OF wf controlled i_bound absent])
  also have "... \<le>
      nnreal
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) * C"
    by (rule staged_phase_query_index_target_error_query_bound
        [OF raw_bound subset envelope])
  finally show ?thesis .
qed

lemma staged_query_prefix_receive_header_supported_sampling_bound_total:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and absent:
      "query_index_raw_preimage_absent
        (query_header_supported_union_good_sets verifier_state
          query_sampling_success_space fr f_fri_roots f_final as dg
          composition_fri_roots final)
        prefix_state"
    and raw_bound: "query_index_raw_preimage_bound"
    and no_bad: "\<not> query_supported_pairwise_merkle_bad verifier_state"
  shows
    "wp_event
      (staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_query_index_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (raw, _) \<Rightarrow>
            index (to_nat raw) \<in>
              query_header_supported_union_good_sets verifier_state
                query_sampling_success_space fr f_fri_roots f_final as dg
                composition_fri_roots final)
      prefix_state \<le>
      nnreal
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)) * query_error_bound"
proof -
  let ?B =
    "query_header_supported_union_good_sets verifier_state
      query_sampling_success_space fr f_fri_roots f_final as dg
      composition_fri_roots final"
  have subset: "?B \<subseteq> query_sample_space"
    by (rule query_header_supported_union_good_sets_subset)
  have envelope:
    "nnreal (query_raw_preimage_card_envelope (card ?B)) / nnreal size \<le>
      query_error_bound"
    by (rule
        query_header_supported_union_good_sets_fraction_bound_if_no_global_pairwise_merkle_bad
        [OF no_bad query_sampling_success_space_subset
          query_sampling_success_space_envelope_fraction_bound])
  show ?thesis
    by (rule staged_query_prefix_receive_bad_index_query_bound_total
        [OF wf controlled i_bound absent raw_bound subset envelope])
qed

lemma staged_composition_fri_prefix_receive_bad_value_bound_total:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < ceil_log (maxDegree + 1)"
    and absent: "composition_fri_challenge_values_absent B s"
  shows
    "wp_event
      (staged_composition_fri_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_composition_fri_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (b, _) \<Rightarrow> b \<in> B) s \<le>
      staged_phase_target_error B
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
proof -
  have local:
    "wp_event
      (staged_composition_fri_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_composition_fri_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (b, _) \<Rightarrow> b \<in> B) s \<le>
      staged_phase_target_error B
        (Suc (staged_composition_fri_search_queries budgets i))"
    by (rule staged_composition_fri_prefix_receive_bad_value_bound
        [OF wf controlled i_bound absent])
  also have
    "staged_phase_target_error B
        (Suc (staged_composition_fri_search_queries budgets i)) \<le>
      staged_phase_target_error B
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
    by (rule staged_phase_target_error_mono)
      (simp add: staged_composition_fri_search_queries_le_total
        [OF wf i_bound])
  finally show ?thesis .
qed

lemma staged_composition_fri_prefix_receive_bad_vector_position_bound_total:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < ceil_log (maxDegree + 1)"
    and absent:
      "composition_fri_challenge_values_absent
        (fri_vector_position_values B i) s"
  shows
    "wp_event
      (staged_composition_fri_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_composition_fri_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i) s \<le>
      staged_phase_target_error (fri_vector_position_values B i)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
  by (rule staged_composition_fri_prefix_receive_bad_value_bound_total
      [OF wf controlled i_bound absent])

lemma
  staged_composition_fri_prefix_receive_bad_vector_position_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset:
      "B \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and i_bound: "i < ceil_log (to_nat dg + 1)"
    and dg_bound: "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    and absent:
      "composition_fri_challenge_values_absent
        (fri_vector_position_values B i) s"
  shows
    "wp_event
      (staged_composition_fri_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_composition_fri_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i) s \<le>
      staged_phase_relation_error (card B)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
proof -
  have i_max: "i < ceil_log (maxDegree + 1)"
    using i_bound dg_bound by simp
  have target:
    "wp_event
      (staged_composition_fri_challenge_prefix_program A i \<bind>
        (\<lambda>_. receive_composition_fri_challenge))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i) s \<le>
      staged_phase_target_error (fri_vector_position_values B i)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
    by (rule
        staged_composition_fri_prefix_receive_bad_vector_position_bound_total
        [OF wf controlled i_max absent])
  also have "... \<le>
      staged_phase_relation_error (card B)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
    by (rule staged_phase_target_error_card_mono)
      (rule fri_vector_position_values_card_le[OF subset i_bound])
  finally show ?thesis .
qed

lemma
  staged_composition_fri_prefix_receive_keep_prefix_bad_vector_position_relation_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset:
      "B \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and i_bound: "i < ceil_log (to_nat dg + 1)"
    and dg_bound: "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    and absent:
      "composition_fri_challenge_values_absent
        (fri_vector_position_values B i) s"
  shows
    "wp_event
      (staged_composition_fri_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. receive_composition_fri_challenge \<bind>
          (\<lambda>b. return (prefix, b))))
      (\<lambda>out. case out of None \<Rightarrow> False
        | Some ((_, b), _) \<Rightarrow> b \<in> fri_vector_position_values B i) s \<le>
      staged_phase_relation_error (card B)
        (Suc
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget))"
proof -
  let ?P =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i"
  let ?Q =
    "\<lambda>out. case out of None \<Rightarrow> False
      | Some ((_, b), _) \<Rightarrow> b \<in> fri_vector_position_values B i"
  have cont_eq:
    "\<And>prefix t. wp_event
      (receive_composition_fri_challenge \<bind>
        (\<lambda>b. return (prefix, b))) ?Q t =
      wp_event receive_composition_fri_challenge ?P t"
  proof -
    fix prefix t
    show "wp_event
        (receive_composition_fri_challenge \<bind>
          (\<lambda>b. return (prefix, b))) ?Q t =
      wp_event receive_composition_fri_challenge ?P t"
      unfolding wp_event_def
      apply (subst wp_bind)
      apply (rule arg_cong[where
        f="\<lambda>Q. wp receive_composition_fri_challenge Q t"])
      apply (rule ext)
      apply (simp add: wp_return split: option.splits prod.splits)
      done
  qed
  have eq:
    "wp_event
      (staged_composition_fri_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. receive_composition_fri_challenge \<bind>
          (\<lambda>b. return (prefix, b)))) ?Q s =
      wp_event
        (staged_composition_fri_challenge_prefix_program A i \<bind>
          (\<lambda>_. receive_composition_fri_challenge)) ?P s"
    by (rule wp_event_bind_cong_cont) (simp_all add: cont_eq)
  show ?thesis
    unfolding eq
    by (rule
        staged_composition_fri_prefix_receive_bad_vector_position_relation_bound
        [OF wf controlled subset i_bound dg_bound absent])
qed

lemma staged_composition_fri_bad_vector_coordinate_sum_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset:
      "B \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and dg_bound:
      "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    and absent:
      "\<And>i. i < ceil_log (to_nat dg + 1) \<Longrightarrow>
        composition_fri_challenge_values_absent
          (fri_vector_position_values B i) s"
  shows
    "(\<Sum>i < ceil_log (to_nat dg + 1).
      wp_event
        (staged_composition_fri_challenge_prefix_program A i \<bind>
          (\<lambda>_. receive_composition_fri_challenge))
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i) s) \<le>
      nnreal (ceil_log (to_nat dg + 1)) *
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget))"
proof -
  have
    "(\<Sum>i < ceil_log (to_nat dg + 1).
      wp_event
        (staged_composition_fri_challenge_prefix_program A i \<bind>
          (\<lambda>_. receive_composition_fri_challenge))
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i) s) \<le>
      (\<Sum>i < ceil_log (to_nat dg + 1).
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget)))"
  proof (rule sum_mono)
    fix i
    assume i_bound: "i \<in> {..<ceil_log (to_nat dg + 1)}"
    then have i_lt: "i < ceil_log (to_nat dg + 1)"
      by simp
    show
      "wp_event
        (staged_composition_fri_challenge_prefix_program A i \<bind>
          (\<lambda>_. receive_composition_fri_challenge))
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some (b, _) \<Rightarrow> b \<in> fri_vector_position_values B i) s \<le>
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget))"
      by (rule
          staged_composition_fri_prefix_receive_bad_vector_position_relation_bound
          [OF wf controlled subset i_lt dg_bound absent[OF i_lt]])
  qed
  also have "... =
      nnreal (ceil_log (to_nat dg + 1)) *
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget))"
    by simp
  finally show ?thesis .
qed

lemma staged_composition_fri_bad_vector_coordinate_sum_keep_prefix_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset:
      "B \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and dg_bound:
      "ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)"
    and absent:
      "\<And>i. i < ceil_log (to_nat dg + 1) \<Longrightarrow>
        composition_fri_challenge_values_absent
          (fri_vector_position_values B i) s"
  shows
    "(\<Sum>i < ceil_log (to_nat dg + 1).
      wp_event
        (staged_composition_fri_challenge_prefix_program A i \<bind>
          (\<lambda>prefix. receive_composition_fri_challenge \<bind>
            (\<lambda>b. return (prefix, b))))
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some ((_, b), _) \<Rightarrow>
              b \<in> fri_vector_position_values B i) s) \<le>
      nnreal (ceil_log (to_nat dg + 1)) *
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget))"
proof -
  have
    "(\<Sum>i < ceil_log (to_nat dg + 1).
      wp_event
        (staged_composition_fri_challenge_prefix_program A i \<bind>
          (\<lambda>prefix. receive_composition_fri_challenge \<bind>
            (\<lambda>b. return (prefix, b))))
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some ((_, b), _) \<Rightarrow>
              b \<in> fri_vector_position_values B i) s) \<le>
      (\<Sum>i < ceil_log (to_nat dg + 1).
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget)))"
  proof (rule sum_mono)
    fix i
    assume i_bound: "i \<in> {..<ceil_log (to_nat dg + 1)}"
    then have i_lt: "i < ceil_log (to_nat dg + 1)"
      by simp
    show
      "wp_event
        (staged_composition_fri_challenge_prefix_program A i \<bind>
          (\<lambda>prefix. receive_composition_fri_challenge \<bind>
            (\<lambda>b. return (prefix, b))))
        (\<lambda>out. case out of None \<Rightarrow> False
          | Some ((_, b), _) \<Rightarrow>
              b \<in> fri_vector_position_values B i) s \<le>
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget))"
      by (rule
          staged_composition_fri_prefix_receive_keep_prefix_bad_vector_position_relation_bound
          [OF wf controlled subset i_lt dg_bound absent[OF i_lt]])
  qed
  also have "... =
      nnreal (ceil_log (to_nat dg + 1)) *
        staged_phase_relation_error (card B)
          (Suc
            (staged_attacker_query_budget budgets +
              staged_challenge_query_budget))"
    by simp
  finally show ?thesis .
qed

lemma staged_controlled_trace_root:
  assumes "staged_adversary_controlled budgets A"
  shows
    "controlled_ro_program (trace_root_budget budgets)
      (trace_root_stage A)"
  using assms unfolding staged_adversary_controlled_def by simp

lemma staged_controlled_trace_fri:
  assumes controlled: "staged_adversary_controlled budgets A"
    and "i < length (trace_fri_budgets budgets)"
  shows
    "controlled_ro_program (trace_fri_budgets budgets ! i)
      (trace_fri_root_stage A i bs)"
  using assms unfolding staged_adversary_controlled_def by blast

lemma staged_controlled_trace_final:
  assumes "staged_adversary_controlled budgets A"
  shows
    "controlled_ro_program (trace_final_budget budgets)
      (trace_final_stage A bs)"
  using assms unfolding staged_adversary_controlled_def by blast

lemma staged_controlled_degree:
  assumes "staged_adversary_controlled budgets A"
  shows
    "controlled_ro_program (degree_budget budgets)
      (degree_stage A as)"
  using assms unfolding staged_adversary_controlled_def by blast

lemma staged_controlled_composition_fri:
  assumes controlled: "staged_adversary_controlled budgets A"
    and "i < length (composition_fri_budgets budgets)"
  shows
    "controlled_ro_program (composition_fri_budgets budgets ! i)
      (composition_fri_root_stage A dg i bs)"
  using assms unfolding staged_adversary_controlled_def by blast

lemma staged_controlled_composition_final:
  assumes "staged_adversary_controlled budgets A"
  shows
    "controlled_ro_program (composition_final_budget budgets)
      (composition_final_stage A dg bs)"
  using assms unfolding staged_adversary_controlled_def by blast

lemma staged_controlled_query:
  assumes controlled: "staged_adversary_controlled budgets A"
    and "i < length (query_opening_budgets budgets)"
  shows
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
  using assms unfolding staged_adversary_controlled_def by blast

lemma staged_security_experiment_hash_map_output_collision_bad_bound:
  assumes admissible:
    "admissible_adversary q (staged_semantic_adversary A)"
  shows
    "wp_event (staged_security_experiment A)
      (hash_map_output_collision_bad adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0 (q + verifier_hash_query_budget)"
  unfolding staged_security_experiment_eq_security_experiment
  by (rule security_experiment_hash_map_output_collision_bad_bound
      [OF admissible])

lemma staged_security_experiment_hash_map_output_collision_bad_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (staged_security_experiment A)
      (hash_map_output_collision_bad adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
  by (rule staged_security_experiment_hash_map_output_collision_bad_bound
      [OF admissible_staged_semantic_adversary[OF wf controlled]])

lemma hash_range_budget_checked_staged_security_experiment:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_range_budget
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget)
      (checked_staged_security_experiment A)"
proof -
  have cont:
    "\<And>data. hash_range_budget verifier_hash_query_budget
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad)))"
    using hash_range_budget_verifier_after_adversary
      [of "staged_proof_transcript data" for data]
    unfolding verifier_state_transfer_def sm_bind_assoc .
  have budget:
    "hash_range_budget
      ((staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
        verifier_hash_query_budget)
      (checked_staged_security_experiment A)"
    unfolding checked_staged_security_experiment_def
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_checked_staged_transcript_program
        [OF wf controlled], rule cont)
  then show ?thesis by (simp add: add.assoc)
qed

lemma hash_collision_budget_checked_staged_security_experiment:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "hash_collision_budget
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget + verifier_hash_query_budget)
      (checked_staged_security_experiment A)"
proof -
  have cont_range:
    "\<And>data. hash_range_budget verifier_hash_query_budget
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad)))"
    using hash_range_budget_verifier_after_adversary
      [of "staged_proof_transcript data" for data]
    unfolding verifier_state_transfer_def sm_bind_assoc .
  have cont_collision:
    "\<And>data. hash_collision_budget verifier_hash_query_budget
      (get \<bind>
        (\<lambda>s. put
          (verifier_state_from_adversary s
            (staged_proof_transcript data)) \<bind>
          (\<lambda>_. verify_monad)))"
    using hash_collision_budget_verifier_after_adversary
      [of "staged_proof_transcript data" for data]
    unfolding verifier_state_transfer_def sm_bind_assoc .
  have budget:
    "hash_collision_budget
      ((staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
        verifier_hash_query_budget)
      (checked_staged_security_experiment A)"
    unfolding checked_staged_security_experiment_def
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_checked_staged_transcript_program
        [OF wf controlled],
       rule hash_collision_budget_checked_staged_transcript_program
        [OF wf controlled],
       rule cont_range,
       rule cont_collision)
  then show ?thesis by (simp add: add.assoc)
qed

lemma checked_staged_security_experiment_hash_new_collision_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  let ?q =
    "staged_attacker_query_budget budgets +
      staged_challenge_query_budget + verifier_hash_query_budget"
  have collision_budget:
    "hash_collision_budget ?q (checked_staged_security_experiment A)"
    by (rule hash_collision_budget_checked_staged_security_experiment
        [OF wf controlled])
  have "wp_event (checked_staged_security_experiment A)
      (hash_new_collision_event adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value
        (card (hash_map_output_values adversary_initial_state)) ?q"
    using collision_budget adversary_initial_state_no_output_collision
    unfolding hash_collision_budget_def by blast
  then show ?thesis by simp
qed

lemma checked_staged_security_experiment_hash_map_output_collision_bad_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment A)
      (hash_map_output_collision_bad adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have "wp_event (checked_staged_security_experiment A)
      (hash_map_output_collision_bad adversary_initial_state)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment A)
        (hash_new_collision_event adversary_initial_state)
        adversary_initial_state"
    by (rule wp_event_mono)
      (rule hash_map_output_collision_bad_imp_security_new_collision)
  also have "... \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule checked_staged_security_experiment_hash_new_collision_bound_controlled
        [OF wf controlled])
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_hash_map_output_collision_bad_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        hash_map_output_collision_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?P = "hash_map_output_collision_bad adversary_initial_state"
  let ?projected =
    "\<lambda>out. case out of None \<Rightarrow> ?P None
      | Some (x, t) \<Rightarrow> ?P (Some (snd x, t))"
  have event_le_projected:
    "wp_event ?M
      (staged_security_with_data_state_verifier_event
        hash_map_output_collision_bad)
      adversary_initial_state \<le>
      wp_event ?M ?projected adversary_initial_state"
  proof (rule wp_event_mono)
    fix out
    assume bad:
      "staged_security_with_data_state_verifier_event
        hash_map_output_collision_bad out"
    show "?projected out"
    proof (cases out)
      case None
      then show ?thesis
        using bad unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      have local_bad:
        "hash_map_output_collision_bad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (Some (result, final_state))"
        using bad unfolding out_eq
          staged_security_with_data_state_verifier_event_def by simp
      then have global_bad:
        "hash_map_output_collision_bad adversary_initial_state
          (Some (result, final_state))"
        unfolding hash_map_output_collision_bad_def by simp
      show ?thesis
        unfolding out_eq using global_bad by simp
    qed
  qed
  have projected_eq:
    "wp_event ?M ?projected adversary_initial_state =
      wp_event (checked_staged_security_experiment A) ?P
        adversary_initial_state"
  proof -
    have "?M \<bind> (\<lambda>x. return (snd x)) =
      checked_staged_security_experiment A"
      by (rule checked_staged_security_experiment_with_data_state_projection)
    then have "wp_event (checked_staged_security_experiment A) ?P
        adversary_initial_state =
      wp_event (?M \<bind> (\<lambda>x. return (snd x))) ?P
        adversary_initial_state"
      by simp
    also have "... = wp_event ?M ?projected adversary_initial_state"
      by (subst wp_event_bind_return_map[where f=snd]) simp
    finally show ?thesis by simp
  qed
  have checked_bound:
    "wp_event (checked_staged_security_experiment A)
      (hash_map_output_collision_bad adversary_initial_state)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_experiment_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        hash_map_output_collision_bad)
      adversary_initial_state \<le>
      wp_event ?M ?projected adversary_initial_state"
    by (rule event_le_projected)
  also have "... =
      wp_event (checked_staged_security_experiment A) ?P
        adversary_initial_state"
    by (rule projected_eq)
  also have "... \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule checked_bound)
  finally show ?thesis .
qed

end

end
