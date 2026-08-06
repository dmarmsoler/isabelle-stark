(*  Title:      Stark/Soundness_Staged_Query_Prefix.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Query_Prefix
  imports Soundness_Reductions Staged_Security_Experiment
begin

section \<open>Query and Partial-Opening Reductions\<close>

text \<open>Staged query-prefix replay and prefix receive decomposition lemmas.\<close>

context soundness
begin

text \<open>
  The deterministic partition above reduces soundness to four probability
  bounds.  The bounds themselves require additional cryptographic/algebraic
  interfaces: random-linear-combination soundness, query-sampling freshness,
  and FRI low-degree soundness.  Those assumptions are kept in the separate
  bounded-soundness locale below, rather than hidden as unproved lemmas in this
  base locale.
\<close>

lemma soundness_bound_component_accounting:
  "soundness_bound =
    composition_error_bound + trace_fri_error + composition_fri_error +
      nnreal rounds * query_error_bound"
  unfolding soundness_bound_def by simp

lemma soundness_bound_with_merkle_component_accounting:
  "soundness_bound_with_merkle =
    merkle_binding_error + composition_error_bound + trace_fri_error +
      composition_fri_error + nnreal rounds * query_error_bound"
  unfolding soundness_bound_with_merkle_def soundness_bound_def
  by (simp add: algebra_simps)

lemma wp_event_finite_union_bound:
  fixes B :: "'i \<Rightarrow> prob"
  assumes finite: "finite I"
    and bounds: "\<And>i. i \<in> I \<Longrightarrow> wp_event m (E i) s \<le> B i"
  shows
    "wp_event m (\<lambda>out. \<exists>i \<in> I. E i out) s \<le> (\<Sum>i\<in>I. B i)"
  using finite bounds
proof (induction I)
  case empty
  show ?case
    unfolding wp_event_def wp_def dist_expect_def by simp
next
  case (insert i I)
  have split:
    "wp_event m (\<lambda>out. \<exists>j \<in> insert i I. E j out) s \<le>
      wp_event m (E i) s +
      wp_event m (\<lambda>out. \<exists>j \<in> I. E j out) s"
  proof -
    have "wp_event m (\<lambda>out. \<exists>j \<in> insert i I. E j out) s \<le>
        wp_event m (\<lambda>out. E i out \<or> (\<exists>j \<in> I. E j out)) s"
      by (rule wp_event_mono) auto
    also have "... \<le>
        wp_event m (E i) s +
        wp_event m (\<lambda>out. \<exists>j \<in> I. E j out) s"
      by (rule wp_event_union_bound)
    finally show ?thesis .
  qed
  have tail:
    "wp_event m (\<lambda>out. \<exists>j \<in> I. E j out) s \<le> (\<Sum>j\<in>I. B j)"
    by (rule insert.IH) (use insert.prems in blast)
  have "wp_event m (E i) s +
      wp_event m (\<lambda>out. \<exists>j \<in> I. E j out) s \<le>
      B i + (\<Sum>j\<in>I. B j)"
    by (intro add_mono tail insert.prems) simp
  also have "... = (\<Sum>j\<in>insert i I. B j)"
    using insert.hyps by simp
  finally show ?case
    by (rule order_trans[OF split])
qed

lemma hash_extends_verifier_state_from_adversary_right:
  assumes ext: "s \<le> t"
  shows "s \<le> verifier_state_from_adversary t tr"
  using ext
  unfolding verifier_state_from_adversary_def less_eq_hash_ext_def
    less_eq_fmap_def
  by simp

lemma checked_staged_security_with_data_state_supported_output_local_side_bad_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        supported_output_local_side_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
  unfolding supported_output_local_side_bad_iff_hash_map_output_collision_bad
  by (rule
      checked_staged_security_with_data_state_hash_map_output_collision_bad_bound_controlled
      [OF wf controlled])

lemma checked_staged_security_with_data_state_supported_pairwise_side_bad_bound_controlled:
  fixes coupling_error :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and coupling_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          supported_pairwise_coupling_event)
        adversary_initial_state \<le> coupling_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        supported_pairwise_side_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      coupling_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  have side_eq:
    "?E supported_pairwise_side_bad =
      (\<lambda>out. ?E hash_map_output_collision_bad out \<or>
        ?E supported_pairwise_coupling_event out)"
    unfolding staged_security_with_data_state_verifier_event_def
      supported_pairwise_side_bad_def supported_pairwise_coupling_event_def
    by (rule ext) (auto split: option.splits prod.splits)
  have "wp_event ?M (?E supported_pairwise_side_bad)
      adversary_initial_state \<le>
      wp_event ?M (?E hash_map_output_collision_bad)
        adversary_initial_state +
      wp_event ?M (?E supported_pairwise_coupling_event)
        adversary_initial_state"
    unfolding side_eq
    by (rule wp_event_union_bound)
  also have "... \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget) +
      coupling_error"
    by (intro add_mono coupling_bound
        checked_staged_security_with_data_state_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  finally show ?thesis .
qed

lemma checked_staged_accepted_imp_transcript_pre_or_new_hit:
  assumes support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and acc: "accepted out"
  shows
    "staged_security_with_data_state_transcript_pre_hit out \<or>
      staged_security_with_data_state_transcript_new_hit out"
proof (cases out)
  case None
  then show ?thesis
    using acc unfolding accepted_def by simp
next
  case (Some packed)
  then obtain data attacker_state result final_state where out_eq:
    "out = Some (((data, attacker_state), result), final_state)"
    by (cases packed, auto split: prod.splits)
  let ?tr = "staged_proof_transcript data"
  let ?s = "verifier_state_from_adversary attacker_state ?tr"
  have verifier:
    "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    using checked_staged_security_experiment_with_data_state_outcomeE
      [OF support[unfolded out_eq]]
    by blast
  have split:
    "hash_map_output_values ?s \<inter> set ?tr \<noteq> {} \<or>
      hash_map_new_output_hit (set ?tr) ?s final_state"
    by (rule verify_monad_trace_root_target_preexisting_or_new[OF verifier])
      simp
  then show ?thesis
    unfolding out_eq
      staged_security_with_data_state_transcript_pre_hit_def
      staged_security_with_data_state_transcript_new_hit_def
    by simp
qed

lemma checked_staged_acceptance_transcript_hit_union_bound:
  "wp_event (checked_staged_security_experiment_with_data_state A) accepted
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_pre_hit
      adversary_initial_state +
    wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_transcript_new_hit
      adversary_initial_state"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?pre = staged_security_with_data_state_transcript_pre_hit
  let ?new = staged_security_with_data_state_transcript_new_hit
  have "wp_event ?M accepted adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?pre out \<or> ?new out) adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule checked_staged_accepted_imp_transcript_pre_or_new_hit)
  also have "... \<le>
      wp_event ?M ?pre adversary_initial_state +
      wp_event ?M ?new adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

definition staged_security_with_data_state_query_partial_header_key_hit
  :: "((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_query_partial_header_key_hit out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), _), final_state) \<Rightarrow>
          (let s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data);
           B =
            query_header_supported_partial_union_good_sets s
              query_sampling_success_space
              (staged_trace_root data)
              (staged_trace_fri_roots data)
              (staged_trace_final data)
              (staged_alphas data)
              (staged_degree data)
              (staged_composition_fri_roots data)
              (staged_composition_final data)
           in
            (\<exists>i raw. i < rounds \<and>
              fmlookup (HashMap final_state)
                (QueryIndexChallenge i
                  (state_after_query_chunks
                    (staged_query_start_hash data)
                    (staged_query_chunks data) i)) =
                Some raw \<and>
              index (to_nat raw) \<in> B)))"

definition staged_security_with_data_state_query_bad_hit_at
  :: "nat \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list) \<times>
        'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_security_with_data_state_query_bad_hit_at i out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (((data, attacker_state), result), final_state) \<Rightarrow>
          (let s =
            verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)
           in
            Some (result, final_state) \<in> set_dist (execute verify_monad s) \<and>
            query_index_round_set_hit_at s query_sampling_success_space i
              (Some (result, final_state))))"

lemma staged_security_with_data_state_query_bad_hit_imp_round_hit:
  assumes bad: "staged_security_with_data_state_query_bad_hit out"
  shows "\<exists>i \<in> {..<rounds}.
    staged_security_with_data_state_query_bad_hit_at i out"
proof (cases out)
  case None
  then show ?thesis
    using bad unfolding staged_security_with_data_state_query_bad_hit_def
    by simp
next
  case (Some packed)
  then obtain data attacker_state result final_state where out_eq:
    "out = Some (((data, attacker_state), result), final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from bad[unfolded out_eq
      staged_security_with_data_state_query_bad_hit_def Let_def]
  have verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    and query_bad: "query_bad ?s (Some (result, final_state))"
    by simp_all
  from query_bad_imp_query_index_round_set_hit[OF query_bad]
  obtain i where i_bound: "i < rounds"
    and hit_at:
      "query_index_round_set_hit_at ?s query_sampling_success_space i
        (Some (result, final_state))"
    unfolding query_index_round_set_hit_def by blast
  have "staged_security_with_data_state_query_bad_hit_at i out"
    unfolding out_eq staged_security_with_data_state_query_bad_hit_at_def
      Let_def
    using verifier hit_at by simp
  then show ?thesis
    using i_bound by blast
qed

lemma checked_staged_security_with_data_state_query_bad_hit_bound_from_rounds:
  assumes round_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_bad_hit_at i)
        adversary_initial_state \<le> C i"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out. \<exists>i \<in> {..<rounds}.
        staged_security_with_data_state_query_bad_hit_at i out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule staged_security_with_data_state_query_bad_hit_imp_round_hit)
  also have "... \<le> (\<Sum>i<rounds. C i)"
    by (rule wp_event_finite_UN_bound)
      (simp_all add: round_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_query_bad_imp_partial_header_key_hit_or_collision_on_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and bad: "staged_security_with_data_state_query_bad_hit out"
  shows
    "staged_security_with_data_state_query_partial_header_key_hit out \<or>
     staged_security_with_data_state_verifier_event
       hash_map_output_collision_bad out"
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
    by blast
  show ?thesis
  proof (cases "hash_map_output_collision final_state")
    case True
    then have
      "staged_security_with_data_state_verifier_event
        hash_map_output_collision_bad
        (Some (((data, attacker_state), result), final_state))"
      unfolding staged_security_with_data_state_verifier_event_def
        hash_map_output_collision_bad_def accepted_def
      by simp
    then show ?thesis
      unfolding out_eq by simp
  next
    case clean: False
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
    from bound obtain fr f_fri_roots f_final dg composition_fri_roots final
        rest where
      header':
        "verifier_header_transcript ?s fr f_fri_roots f_final as dg
          composition_fri_roots final rest"
      and trace_bind:
        "merkle_root_binds_table fr trace_table final_state"
      and comp_nonempty: "composition_fri_roots \<noteq> []"
      and comp_bind:
        "merkle_root_binds_table (hd composition_fri_roots) composition_table
          final_state"
      unfolding accepted_with_bound_tables_def by blast
    have eqs:
      "fr = staged_trace_root data \<and>
       f_fri_roots = staged_trace_fri_roots data \<and>
       f_final = staged_trace_final data \<and>
       as = staged_alphas data \<and>
       dg = staged_degree data \<and>
       composition_fri_roots = staged_composition_fri_roots data \<and>
       final = staged_composition_final data \<and>
       rest = List.concat (staged_query_chunks data)"
      using verifier_header_transcript_unique[OF header' staged_header]
      by simp
    have state:
      "query_header_supported_table_candidate_state ?s
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        trace_table composition_table final_state"
      unfolding query_header_supported_table_candidate_state_def
      by (intro exI[of _ result] exI[of _ query_idxs]
          exI[of _ "List.concat (staged_query_chunks data)"])
        (use verifier bound staged_header trace_bind comp_nonempty comp_bind
          eqs in simp)
    have candidate:
      "(trace_table, composition_table) \<in>
        query_header_supported_partial_table_candidates ?s
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
      using
        query_header_supported_table_candidate_state_imp_partial_candidate_state
          [OF state clean]
        query_header_supported_partial_table_candidates_iff_state
      by blast
    have raw_hit:
      "index (to_nat (raw_idxs ! i)) \<in>
        query_header_supported_partial_union_good_sets ?s
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
        unfolding query_header_supported_partial_union_good_sets_def
          raw_idx_eq
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
      unfolding out_eq
        staged_security_with_data_state_query_partial_header_key_hit_def
        Let_def
      using i_bound lookup_i raw_hit by auto
  qed
qed

lemma checked_staged_security_with_data_state_query_bad_bound_from_partial_header_key_hit_or_collision:
  fixes C K :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and partial_header_key_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_header_key_hit
        adversary_initial_state \<le> C"
    and collision_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          hash_map_output_collision_bad)
        adversary_initial_state \<le> K"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le> C + K"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  have "wp_event ?M staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
    wp_event ?M
      (\<lambda>out.
        staged_security_with_data_state_query_partial_header_key_hit out \<or>
        staged_security_with_data_state_verifier_event
          hash_map_output_collision_bad out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in> set_dist (execute ?M adversary_initial_state)"
      and bad: "staged_security_with_data_state_query_bad_hit out"
    show
      "staged_security_with_data_state_query_partial_header_key_hit out \<or>
       staged_security_with_data_state_verifier_event
         hash_map_output_collision_bad out"
      by (rule
          checked_staged_security_with_data_state_query_bad_imp_partial_header_key_hit_or_collision_on_support
          [OF wf controlled support bad])
  qed
  also have "... \<le>
      wp_event ?M staged_security_with_data_state_query_partial_header_key_hit
        adversary_initial_state +
      wp_event ?M
        (staged_security_with_data_state_verifier_event
          hash_map_output_collision_bad)
        adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> C + K"
    by (intro add_mono partial_header_key_bound collision_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_from_partial_header_key_hit_or_collision:
  fixes C K :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and partial_header_key_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_header_key_hit
        adversary_initial_state \<le> C"
    and collision_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          hash_map_output_collision_bad)
        adversary_initial_state \<le> K"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le> C + K"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state"
    by (rule checked_staged_security_with_data_state_query_bad_verifier_event_bound
        [OF order_refl])
  also have "... \<le> C + K"
    by (rule
        checked_staged_security_with_data_state_query_bad_bound_from_partial_header_key_hit_or_collision
        [OF wf controlled partial_header_key_bound collision_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_partial_header_key_hit_bound_from_index_set:
  assumes cover:
    "\<And>data attacker_state.
      query_header_supported_partial_union_good_sets
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
      staged_security_with_data_state_query_partial_header_key_hit
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
      staged_security_with_data_state_query_partial_header_key_hit
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      ?projected adversary_initial_state"
  proof (rule wp_event_mono)
    fix out
    assume hit:
      "staged_security_with_data_state_query_partial_header_key_hit out"
    show "?projected out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding
          staged_security_with_data_state_query_partial_header_key_hit_def
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
        "query_header_supported_partial_union_good_sets ?s
          query_sampling_success_space
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data)"
      from hit[unfolded out_eq
          staged_security_with_data_state_query_partial_header_key_hit_def
          Let_def]
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

lemma checked_staged_security_with_data_state_partial_header_key_hit_bound_from_index_set_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
      "\<And>data attacker_state.
        query_header_supported_partial_union_good_sets
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
      staged_security_with_data_state_query_partial_header_key_hit
      adversary_initial_state \<le>
      staged_phase_target_error (query_index_raw_preimage B)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
  by (rule
      checked_staged_security_with_data_state_partial_header_key_hit_bound_from_index_set
      [OF cover])
    (rule checked_staged_security_with_data_query_index_set_hit_bound
      [OF wf controlled])

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_from_partial_fixed_query_error_cover:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
      "\<And>data attacker_state.
        query_header_supported_partial_union_good_sets
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
    and frac:
      "nnreal (card B) / nnreal (card query_sample_space) \<le>
        query_error_bound"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound +
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have partial_key_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_header_key_hit
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
  proof -
    have "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_header_key_hit
        adversary_initial_state \<le>
        staged_phase_target_error (query_index_raw_preimage B)
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget)"
      by (rule
          checked_staged_security_with_data_state_partial_header_key_hit_bound_from_index_set_controlled
          [OF wf controlled cover])
    also have "... \<le>
        nnreal
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget) * query_error_bound"
      by (rule staged_phase_query_index_target_error_query_bound
          [OF raw_bound subset frac])
    finally show ?thesis .
  qed
  have collision_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        hash_map_output_collision_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_query_bad_verifier_event_bound_from_partial_header_key_hit_or_collision
        [OF wf controlled partial_key_bound collision_bound])
qed

lemma staged_dynamic_partial_query_set_subset:
  "query_header_supported_partial_union_good_sets
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
  by (rule query_header_supported_partial_union_good_sets_subset)

lemma staged_dynamic_partial_query_set_fraction_bound_if_unique_candidate:
  assumes unique:
    "\<exists>trace_table composition_table.
      query_header_supported_partial_table_candidates
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data) \<subseteq>
        {(trace_table, composition_table)}"
  shows
    "nnreal
      (card
        (query_header_supported_partial_union_good_sets
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          query_sampling_success_space
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data))) /
      nnreal (card query_sample_space) \<le> query_error_bound"
  by (rule
      query_header_supported_partial_union_good_sets_fraction_bound_if_unique_candidate
      [OF unique query_sampling_success_space_subset
        query_sampling_success_space_fraction_bound_query_sample_space])

lemma staged_dynamic_partial_query_set_target_error_bound_if_unique_candidate:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and unique:
      "\<exists>trace_table composition_table.
        query_header_supported_partial_table_candidates
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))
          (staged_trace_root data)
          (staged_trace_fri_roots data)
          (staged_trace_final data)
          (staged_alphas data)
          (staged_degree data)
          (staged_composition_fri_roots data)
          (staged_composition_final data) \<subseteq>
          {(trace_table, composition_table)}"
  shows
    "staged_phase_target_error
      (query_index_raw_preimage
        (query_header_supported_partial_union_good_sets
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
      [OF raw_bound staged_dynamic_partial_query_set_subset
        staged_dynamic_partial_query_set_fraction_bound_if_unique_candidate
          [OF unique]])

lemma checked_staged_query_prefix_receive_bad_index_imp_new_output_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i \<le> rounds"
    and absent: "query_index_raw_preimage_absent B s"
    and out:
      "Some (raw, t) \<in>
        set_dist
          (execute
            (checked_staged_query_challenge_prefix_program A i \<bind>
              (\<lambda>_. receive_query_index_challenge)) s)"
    and bad: "index (to_nat raw) \<in> B"
  shows
    "hash_new_output_hit_event (query_index_raw_preimage B) s
      (Some (raw, t))"
proof -
  obtain prefix_out u where prefix:
      "Some (prefix_out, u) \<in>
        set_dist
          (execute (checked_staged_query_challenge_prefix_program A i) s)"
    and recv:
      "Some (raw, t) \<in> set_dist (execute receive_query_index_challenge u)"
    using out by (auto elim!: set_dist_bindE)
  have unchecked_prefix:
    "Some
      ((sqp_degree prefix_out, sqp_composition_final prefix_out,
        sqp_query_chunks prefix_out), u) \<in>
      set_dist (execute (staged_query_challenge_prefix_program A i) s)"
    by (rule checked_staged_query_challenge_prefix_outcome_imp_staged_query_prefix
        [OF prefix])
  have prefix_ext: "s \<le> u"
    using hash_target_program_staged_query_challenge_prefix_program
        [OF wf controlled i_bound, of "query_index_raw_preimage B"]
      unchecked_prefix
    unfolding hash_target_program_def hash_extension_preserving_def
    by blast
  have recv_out:
    "u \<le> t \<and>
     fmlookup (HashMap t)
       (QueryIndexChallenge (PQueryCounter u) (PState u)) = Some raw"
    using receive_query_index_challenge_outcome[OF recv] by blast
  have raw_in: "raw \<in> query_index_raw_preimage B"
    using bad unfolding query_index_raw_preimage_def by simp
  show ?thesis
  proof (cases
      "fmlookup (HashMap s)
        (QueryIndexChallenge (PQueryCounter u) (PState u))")
    case None
    then have "hash_map_new_output_hit (query_index_raw_preimage B) s t"
      unfolding hash_map_new_output_hit_def
      using recv_out raw_in by blast
    then show ?thesis
      unfolding hash_new_output_hit_event_def by simp
  next
    case (Some old_raw)
    have old_lookup_t:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter u) (PState u)) =
        Some old_raw"
      by (rule hash_extension_lookup[OF Some])
        (rule hash_ext_trans[OF prefix_ext conjunct1[OF recv_out]])
    then have old_eq: "old_raw = raw"
      using recv_out by simp
    have "old_raw \<notin> query_index_raw_preimage B"
      using absent Some
      unfolding query_index_raw_preimage_absent_def by blast
    then show ?thesis
      using old_eq raw_in by simp
  qed
qed

definition checked_staged_query_prefix_with_state
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow>
      (('f staged_query_prefix_data \<times> 'f protocol_channel),
        'f protocol_channel) state_monad"
  where
    "checked_staged_query_prefix_with_state A i =
      checked_staged_query_challenge_prefix_program A i \<bind>
        (\<lambda>prefix. get \<bind> (\<lambda>prefix_state.
          return (prefix, prefix_state)))"

definition checked_staged_query_prefix_receive_with_state
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow>
      ((('f staged_query_prefix_data \<times> 'f protocol_channel) \<times> 'f),
        'f protocol_channel) state_monad"
  where
    "checked_staged_query_prefix_receive_with_state A i =
      checked_staged_query_prefix_with_state A i \<bind>
        (\<lambda>prefix_pack. receive_query_index_challenge \<bind> (\<lambda>raw.
          return (prefix_pack, raw)))"

lemma checked_staged_query_program_decomp:
  assumes i_bound: "i < n"
  shows
    "checked_staged_query_program A trace_roots composition_roots start n =
      checked_staged_query_program A trace_roots composition_roots start i \<bind>
        (\<lambda>prefix_chunks.
          receive_query_index_challenge \<bind> (\<lambda>raw.
          let idx = index (to_nat raw) in
          query_opening_stage A (start + i) raw \<bind> (\<lambda>chunk.
          assert
            (verifier_query_round_chunk idx trace_roots composition_roots
              chunk) \<bind> (\<lambda>_.
          record_staged_messages chunk \<bind> (\<lambda>_.
          checked_staged_query_program A trace_roots composition_roots
            (Suc (start + i)) (n - Suc i) \<bind> (\<lambda>suffix_chunks.
          return (prefix_chunks @ chunk # suffix_chunks)))))))"
  using i_bound
proof (induction i arbitrary: start n)
  case 0
  then obtain m where n_eq: "n = Suc m"
    by (cases n) simp_all
  show ?case
    unfolding n_eq
    by (simp add: sm_bind_assoc Let_def)
next
  case (Suc i)
  then obtain m where n_eq: "n = Suc m"
    by (cases n) simp_all
  have i_lt_m: "i < m"
    using Suc.prems unfolding n_eq by simp
  have IH:
    "checked_staged_query_program A trace_roots composition_roots
      (Suc start) m =
      checked_staged_query_program A trace_roots composition_roots
        (Suc start) i \<bind>
        (\<lambda>prefix_chunks.
          receive_query_index_challenge \<bind> (\<lambda>raw.
          let idx = index (to_nat raw) in
          query_opening_stage A (Suc start + i) raw \<bind> (\<lambda>chunk.
          assert
            (verifier_query_round_chunk idx trace_roots composition_roots
              chunk) \<bind> (\<lambda>_.
          record_staged_messages chunk \<bind> (\<lambda>_.
          checked_staged_query_program A trace_roots composition_roots
            (Suc (Suc start + i)) (m - Suc i) \<bind> (\<lambda>suffix_chunks.
          return (prefix_chunks @ chunk # suffix_chunks)))))))"
    by (rule Suc.IH[OF i_lt_m])
  show ?case
    unfolding n_eq
    by (simp add: sm_bind_assoc Let_def IH)
qed

lemma get_bind_const:
  "(get \<bind> (\<lambda>_. m)) = m"
proof transfer
  fix m
  show "dist_bind dist_get (\<lambda>_. m) = m"
  proof
    fix s
    show "dist_bind dist_get (\<lambda>_. m) s = m s"
      apply (rule dist_inject[THEN iffD1])
      unfolding dist_bind.rep_eq dist_get_def bind_cont_map_def
      apply (simp add: o_def map_fun_def dist_delta_dist)
      apply (subst map_bind_delta_left_state[where f="\<lambda>s. Some (s, s)"])
      by (auto split: option.splits prod.splits)
  qed
qed

lemma get_bind_return_state_support:
  "Some ((x, s), s) \<in>
    set_dist (execute (get \<bind> (\<lambda>t. return (x, t))) s)"
proof -
  have get_out: "Some (s, s) \<in> set_dist (execute get s)"
    unfolding set_dist_def get.rep_eq dist_get_def dist_delta_dist
      delta_map_def
    by simp
  have ret_out:
    "Some ((x, s), s) \<in> set_dist (execute (return (x, s)) s)"
    unfolding set_dist_def return.rep_eq dist_return_def dist_delta_dist
      delta_map_def
    by simp
  show ?thesis
    by (rule_tac x=s and t=s in set_dist_bindI)
      (rule get_out, rule ret_out)
qed

lemma get_bind_return_state_outcome:
  assumes outcome:
    "Some ((x_out, captured), final) \<in>
      set_dist (execute (get \<bind> (\<lambda>t. return (x, t))) s)"
  shows "x_out = x \<and> captured = s \<and> final = s"
proof -
  from outcome obtain y u where get_out:
      "Some (y, u) \<in> set_dist (execute get s)"
    and ret_out:
      "Some ((x_out, captured), final) \<in>
        set_dist (execute (return (x, y)) u)"
    by (auto elim!: set_dist_bindE)
  have y_u: "y = s \<and> u = s"
    using get_out
    unfolding set_dist_def get.rep_eq dist_get_def dist_delta_dist
      delta_map_def
    by auto
  have captured_final: "x_out = x \<and> captured = y \<and> final = u"
    using ret_out
    unfolding set_dist_def return.rep_eq dist_return_def dist_delta_dist
      delta_map_def
    by auto
  show ?thesis
    using y_u captured_final by simp
qed

lemma checked_staged_query_prefix_with_state_outcome_state:
  assumes outcome:
    "Some ((prefix, prefix_state), u) \<in>
      set_dist (execute (checked_staged_query_prefix_with_state A i) s)"
  shows "u = prefix_state"
proof -
  show ?thesis
    using outcome
    unfolding checked_staged_query_prefix_with_state_def
    by (auto dest!: get_bind_return_state_outcome
        elim!: set_dist_bindE)
qed

lemma checked_staged_query_prefix_with_state_outcome_canonical:
  assumes outcome:
    "Some ((prefix, prefix_state), u) \<in>
      set_dist (execute (checked_staged_query_prefix_with_state A i) s)"
  shows
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist (execute (checked_staged_query_prefix_with_state A i) s)"
  using outcome checked_staged_query_prefix_with_state_outcome_state[OF outcome]
  by simp

lemma checked_staged_query_prefix_receive_with_state_prefix_support:
  assumes outcome:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i) s)"
  shows
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist (execute (checked_staged_query_prefix_with_state A i) s)"
proof -
  from outcome obtain u where prefix_u:
    "Some ((prefix, prefix_state), u) \<in>
      set_dist (execute (checked_staged_query_prefix_with_state A i) s)"
    unfolding checked_staged_query_prefix_receive_with_state_def
    by (auto elim!: set_dist_bindE)
  show ?thesis
    by (rule checked_staged_query_prefix_with_state_outcome_canonical
        [OF prefix_u])
qed

lemma checked_staged_query_prefix_receive_with_state_receive_support:
  assumes outcome:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i) s)"
  shows
    "Some (raw, raw_state) \<in>
      set_dist (execute receive_query_index_challenge prefix_state)"
proof -
  from outcome obtain u where prefix_u:
    "Some ((prefix, prefix_state), u) \<in>
      set_dist (execute (checked_staged_query_prefix_with_state A i) s)"
    and recv_u:
      "Some (raw, raw_state) \<in>
        set_dist (execute receive_query_index_challenge u)"
    unfolding checked_staged_query_prefix_receive_with_state_def
    by (auto elim!: set_dist_bindE)
  have "u = prefix_state"
    by (rule checked_staged_query_prefix_with_state_outcome_state
        [OF prefix_u])
  then show ?thesis
    using recv_u by simp
qed

lemma checked_staged_query_challenge_prefix_program_outcomeE:
  assumes outcome:
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_challenge_prefix_program A i)
          adversary_initial_state)"
  obtains fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5 as s6 dg
      s7 s8 s9 composition_roots composition_bs s10 composition_final s11
      query_start query_chunks where
    "Some (fr, s1) \<in>
      set_dist (execute (trace_root_stage A) adversary_initial_state)"
    "Some ((), s2) \<in> set_dist (execute (record_staged_message fr) s1)"
    "Some ((trace_roots, trace_bs), s3) \<in>
      set_dist
        (execute
          (staged_trace_fri_program A 0 (ceil_log clength) []) s2)"
    "Some (trace_final, s4) \<in>
      set_dist (execute (trace_final_stage A trace_bs) s3)"
    "Some ((), s5) \<in>
      set_dist (execute (record_staged_message trace_final) s4)"
    "Some (as, s6) \<in>
      set_dist (execute (staged_alpha_program (length spec)) s5)"
    "Some (dg, s7) \<in> set_dist (execute (degree_stage A as) s6)"
    "Some ((), s8) \<in>
      set_dist (execute (record_staged_message dg) s7)"
    "Some ((), s9) \<in>
      set_dist
        (execute
          (assert (ceil_log (to_nat dg + 1) \<le> ceil_log (maxDegree + 1)))
          s8)"
    "Some ((composition_roots, composition_bs), s10) \<in>
      set_dist
        (execute
          (staged_composition_fri_program A dg 0
            (ceil_log (to_nat dg + 1)) []) s9)"
    "Some (composition_final, s11) \<in>
      set_dist
        (execute (composition_final_stage A dg composition_bs) s10)"
    "Some ((), query_start) \<in>
      set_dist (execute (record_staged_message composition_final) s11)"
    "Some (query_chunks, prefix_state) \<in>
      set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            0 i)
          query_start)"
    "prefix =
      \<lparr>sqp_trace_root = fr,
       sqp_trace_fri_roots = trace_roots,
       sqp_trace_fri_challenges = trace_bs,
       sqp_trace_final = trace_final,
       sqp_alphas = as,
       sqp_degree = dg,
       sqp_composition_fri_roots = composition_roots,
       sqp_composition_fri_challenges = composition_bs,
       sqp_composition_final = composition_final,
       sqp_query_chunks = query_chunks\<rparr>"
  using outcome
  unfolding checked_staged_query_challenge_prefix_program_def
    staged_alpha_prefix_program_def Let_def
  by (auto elim!: set_dist_bindE intro: that split: prod.splits)

definition checked_staged_after_query_prefix_receive
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow>
      (('f staged_query_prefix_data \<times> 'f protocol_channel) \<times> 'f) \<Rightarrow>
      ('f staged_proof_data, 'f protocol_channel) state_monad"
  where
    "checked_staged_after_query_prefix_receive A i prefix_pack =
      (case prefix_pack of ((prefix, _), raw) \<Rightarrow>
        do {
          let idx = index (to_nat raw);
          chunk \<leftarrow> query_opening_stage A i raw;
          assert
            (verifier_query_round_chunk idx
              (sqp_trace_fri_roots prefix)
              (sqp_composition_fri_roots prefix) chunk);
          record_staged_messages chunk;
          suffix_chunks \<leftarrow>
            checked_staged_query_program A
              (sqp_trace_fri_roots prefix)
              (sqp_composition_fri_roots prefix)
              (Suc i) (rounds - Suc i);
          return
            \<lparr>staged_trace_root = sqp_trace_root prefix,
             staged_trace_fri_roots = sqp_trace_fri_roots prefix,
             staged_trace_fri_challenges =
                sqp_trace_fri_challenges prefix,
             staged_trace_final = sqp_trace_final prefix,
             staged_alphas = sqp_alphas prefix,
             staged_degree = sqp_degree prefix,
             staged_composition_fri_roots =
                sqp_composition_fri_roots prefix,
             staged_composition_fri_challenges =
                sqp_composition_fri_challenges prefix,
             staged_composition_final = sqp_composition_final prefix,
             staged_query_chunks =
                sqp_query_chunks prefix @ chunk # suffix_chunks\<rparr>
        })"

definition checked_staged_after_query_prefix_receive_with_verifier
  :: "'f staged_adversary \<Rightarrow> nat \<Rightarrow>
      (('f staged_query_prefix_data \<times> 'f protocol_channel) \<times> 'f) \<Rightarrow>
      ((('f staged_proof_data \<times> 'f protocol_channel) \<times> unit list),
        'f protocol_channel) state_monad"
  where
    "checked_staged_after_query_prefix_receive_with_verifier A i prefix_pack =
      checked_staged_after_query_prefix_receive A i prefix_pack \<bind>
        (\<lambda>data.
          get \<bind> (\<lambda>s.
            put
              (verifier_state_from_adversary s
                (staged_proof_transcript data)) \<bind>
              (\<lambda>_.
                verify_monad \<bind>
                  (\<lambda>result. return ((data, s), result)))))"

lemma checked_staged_after_query_prefix_receive_with_verifier_outcome:
  assumes outcome:
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive_with_verifier A i
            prefix_pack)
          s)"
  shows
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive A i prefix_pack) s)"
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
proof -
  from outcome[unfolded
      checked_staged_after_query_prefix_receive_with_verifier_def]
  obtain data' attacker_state' where data':
      "Some (data', attacker_state') \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive A i prefix_pack) s)"
    and rest:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (get \<bind>
              (\<lambda>sa.
                put
                  (verifier_state_from_adversary sa
                    (staged_proof_transcript data')) \<bind>
                (\<lambda>_.
                  verify_monad \<bind>
                    (\<lambda>r. return ((data', sa), r)))))
            attacker_state')"
    by (rule set_dist_bindE) (rule that)
  from rest obtain saved_state state_after_get where get_out:
      "Some (saved_state, state_after_get) \<in>
        set_dist (execute get attacker_state')"
    and after_get:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (put
              (verifier_state_from_adversary saved_state
                (staged_proof_transcript data')) \<bind>
              (\<lambda>_.
                verify_monad \<bind>
                  (\<lambda>r. return ((data', saved_state), r))))
            state_after_get)"
    by (rule set_dist_bindE) (rule that)
  from get_out have saved_state_eq: "saved_state = attacker_state'"
    and state_after_get_eq: "state_after_get = attacker_state'"
    by simp_all
  from after_get[unfolded saved_state_eq state_after_get_eq]
  obtain u verifier_start where put_out:
      "Some (u, verifier_start) \<in>
        set_dist
          (execute
            (put
              (verifier_state_from_adversary attacker_state'
                (staged_proof_transcript data')))
            attacker_state')"
    and after_put:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute
            (verify_monad \<bind>
              (\<lambda>r. return ((data', attacker_state'), r)))
            verifier_start)"
    by (rule set_dist_bindE) (rule that)
  from put_out have verifier_start_eq:
    "verifier_start =
      verifier_state_from_adversary attacker_state'
        (staged_proof_transcript data')"
    by simp
  from after_put[unfolded verifier_start_eq]
  obtain result' final_state' where verifier:
      "Some (result', final_state') \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state'
              (staged_proof_transcript data')))"
    and returned:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute (return ((data', attacker_state'), result'))
            final_state')"
    by (elim set_dist_bindE)
  from returned have data_eq: "data = data'"
    and attacker_state_eq: "attacker_state = attacker_state'"
    and result_eq: "result = result'"
    and final_state_eq: "final_state = final_state'"
    by simp_all
  show
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive A i prefix_pack) s)"
    using data' unfolding data_eq attacker_state_eq by simp
  show
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    using verifier
    unfolding data_eq attacker_state_eq result_eq final_state_eq
    by simp
qed

lemma checked_staged_security_experiment_with_data_state_outcomeI:
  assumes builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
    and verifier:
    "Some (result, final_state) \<in>
      set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
  shows
    "Some (((data, attacker_state), result), final_state) \<in>
      set_dist
        (execute
          (checked_staged_security_experiment_with_data_state A)
          adversary_initial_state)"
  unfolding checked_staged_security_experiment_with_data_state_def
  apply (rule_tac x=data and t=attacker_state in set_dist_bindI)
   apply (rule builder)
  apply (rule_tac x=attacker_state and t=attacker_state in set_dist_bindI)
   apply simp
  apply (rule_tac x="()" and
      t="verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)" in set_dist_bindI)
   apply simp
  apply (rule_tac x=result and t=final_state in set_dist_bindI)
   apply (rule verifier)
  apply simp
  done

lemma checked_staged_transcript_program_query_prefix_receive_decomp:
  assumes i_bound: "i < rounds"
  shows
    "checked_staged_transcript_program A =
      checked_staged_query_prefix_receive_with_state A i \<bind>
        checked_staged_after_query_prefix_receive A i"
proof -
  have query_decomp:
    "\<And>trace_roots composition_roots.
      checked_staged_query_program A trace_roots composition_roots 0 rounds =
      checked_staged_query_program A trace_roots composition_roots 0 i \<bind>
        (\<lambda>prefix_chunks.
          receive_query_index_challenge \<bind> (\<lambda>raw.
          let idx = index (to_nat raw) in
          query_opening_stage A (0 + i) raw \<bind> (\<lambda>chunk.
          assert
            (verifier_query_round_chunk idx trace_roots composition_roots
              chunk) \<bind> (\<lambda>_.
          record_staged_messages chunk \<bind> (\<lambda>_.
          checked_staged_query_program A trace_roots composition_roots
            (Suc (0 + i)) (rounds - Suc i) \<bind> (\<lambda>suffix_chunks.
          return (prefix_chunks @ chunk # suffix_chunks)))))))"
    by (rule checked_staged_query_program_decomp[OF i_bound])
  show ?thesis
    unfolding checked_staged_transcript_program_def
      checked_staged_query_prefix_receive_with_state_def
      checked_staged_query_prefix_with_state_def
      checked_staged_query_challenge_prefix_program_def
      staged_alpha_prefix_program_def
      checked_staged_after_query_prefix_receive_def
    apply (simp add: sm_bind_assoc Let_def split_def query_decomp
        get_bind_const)
    done
qed

lemma checked_staged_transcript_program_query_prefix_receive_cont_support:
  assumes i_bound: "i < rounds"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
  obtains prefix prefix_state raw raw_state where
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "Some (data, attacker_state) \<in>
      set_dist
        (execute
          (checked_staged_after_query_prefix_receive A i
            ((prefix, prefix_state), raw))
          raw_state)"
proof -
  have decomp:
    "checked_staged_transcript_program A =
      checked_staged_query_prefix_receive_with_state A i \<bind>
        checked_staged_after_query_prefix_receive A i"
    by (rule checked_staged_transcript_program_query_prefix_receive_decomp
        [OF i_bound])
  from outcome[unfolded decomp]
  obtain x raw_state where head:
      "Some (x, raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and tail:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive A i x)
            raw_state)"
    by (auto elim!: set_dist_bindE)
  obtain prefix_pack raw where x_eq: "x = (prefix_pack, raw)"
    by (cases x) simp
  obtain prefix prefix_state where prefix_pack_eq:
    "prefix_pack = (prefix, prefix_state)"
    by (cases prefix_pack) simp
  show ?thesis
  proof (rule that[of prefix prefix_state raw raw_state])
    show "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
      using head unfolding x_eq prefix_pack_eq by simp
    show "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive A i
              ((prefix, prefix_state), raw))
            raw_state)"
      using tail unfolding x_eq prefix_pack_eq by simp
  qed
qed

lemma checked_staged_security_experiment_with_data_state_query_prefix_receive_decomp:
  assumes i_bound: "i < rounds"
  shows
    "checked_staged_security_experiment_with_data_state A =
      checked_staged_query_prefix_receive_with_state A i \<bind>
        checked_staged_after_query_prefix_receive_with_verifier A i"
  unfolding checked_staged_security_experiment_with_data_state_def
    checked_staged_transcript_program_query_prefix_receive_decomp[OF i_bound]
    checked_staged_after_query_prefix_receive_with_verifier_def
  by (simp add: sm_bind_assoc)

definition staged_query_prefix_start_hash
  :: "'f staged_query_prefix_data \<Rightarrow> 'f"
  where
    "staged_query_prefix_start_hash prefix =
      concat
        (foldl concat
          (concat
            (foldl concat
              (concat
                (foldl concat
                  (concat 0 (sqp_trace_root prefix))
                  (sqp_trace_fri_roots prefix))
                (sqp_trace_final prefix))
              (sqp_alphas prefix))
            (sqp_degree prefix))
          (sqp_composition_fri_roots prefix))
        (sqp_composition_final prefix)"

lemma checked_staged_query_prefix_with_state_query_chunks_length:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
  shows "length (sqp_query_chunks prefix) = i"
proof -
  from support have prefix_out:
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_challenge_prefix_program A i)
          adversary_initial_state)"
    unfolding checked_staged_query_prefix_with_state_def
    by (auto elim!: set_dist_bindE)
  from prefix_out obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4
      s5 as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 query_start query_chunks where
    query_out:
      "Some (query_chunks, prefix_state) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              0 i) s11)"
    and prefix_eq:
      "prefix =
        \<lparr>sqp_trace_root = fr,
         sqp_trace_fri_roots = trace_roots,
         sqp_trace_fri_challenges = trace_bs,
         sqp_trace_final = trace_final,
         sqp_alphas = as,
         sqp_degree = dg,
         sqp_composition_fri_roots = composition_roots,
         sqp_composition_fri_challenges = composition_bs,
         sqp_composition_final = composition_final,
         sqp_query_chunks = query_chunks\<rparr>"
    using prefix_out
    by (elim checked_staged_query_challenge_prefix_program_outcomeE)
  have bound: "0 + i \<le> length (query_opening_budgets budgets)"
    using wf i_bound unfolding staged_budget_wellformed_def by simp
  from checked_staged_query_program_outcome_with_raws
      [OF controlled bound query_out]
  obtain raw_idxs query_idxs where len: "length query_chunks = i"
    by blast
  then show ?thesis
    unfolding prefix_eq by simp
qed

lemma checked_staged_query_prefix_with_state_alignment:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and support:
      "Some ((prefix, prefix_state), prefix_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_with_state A i)
            adversary_initial_state)"
  shows
    "PQueryCounter prefix_state = i \<and>
     PState prefix_state =
       state_after_query_chunks
        (staged_query_prefix_start_hash prefix)
        (sqp_query_chunks prefix) i \<and>
     length (sqp_query_chunks prefix) = i"
proof -
  from support have prefix_out:
    "Some (prefix, prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_challenge_prefix_program A i)
          adversary_initial_state)"
    unfolding checked_staged_query_prefix_with_state_def
    by (auto elim!: set_dist_bindE)
  from prefix_out obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4
      s5 as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 query_start query_chunks where
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
      "Some ((), query_start) \<in>
        set_dist (execute (record_staged_message composition_final) s11)"
    and query_out:
      "Some (query_chunks, prefix_state) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              0 i)
            query_start)"
    and prefix_eq:
      "prefix =
        \<lparr>sqp_trace_root = fr,
         sqp_trace_fri_roots = trace_roots,
         sqp_trace_fri_challenges = trace_bs,
         sqp_trace_final = trace_final,
         sqp_alphas = as,
         sqp_degree = dg,
         sqp_composition_fri_roots = composition_roots,
         sqp_composition_fri_challenges = composition_bs,
         sqp_composition_final = composition_final,
         sqp_query_chunks = query_chunks\<rparr>"
    using prefix_out
    by (elim checked_staged_query_challenge_prefix_program_outcomeE)
  have root_controlled:
    "controlled_ro_program (trace_root_budget budgets) (trace_root_stage A)"
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
  have root_state: "PState s1 = 0"
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
    "PState s3 = foldl concat (PState s2) trace_roots"
    using staged_trace_fri_program_alignment
        [OF controlled trace_bound trace_out]
    by simp
  have state_s3:
    "PState s3 = foldl concat (concat 0 fr) trace_roots"
    using root_state trace_alignment unfolding s2_eq by simp
  have state_s4: "PState s4 = PState s3"
    using controlled_stage_outcome_fields
        [OF trace_final_controlled final_out]
    by simp
  have s5_eq:
    "s5 = s4\<lparr>
      PState := concat (PState s4) trace_final,
      PTranscript := PTranscript s4 @ [trace_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_final])
  have alpha_alignment:
    "PState s6 = foldl concat (PState s5) as"
    using staged_alpha_program_alignment[OF alpha_out] by simp
  have state_s6:
    "PState s6 =
      foldl concat
        (concat (foldl concat (concat 0 fr) trace_roots) trace_final)
        as"
    using state_s3 state_s4 alpha_alignment unfolding s5_eq by simp
  have state_s7: "PState s7 = PState s6"
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
    "PState s10 = foldl concat (PState s9) composition_roots"
    using staged_composition_fri_program_alignment
        [OF controlled composition_bound composition_out]
    by simp
  have state_s10:
    "PState s10 =
      foldl concat
        (concat
          (foldl concat
            (concat (foldl concat (concat 0 fr) trace_roots) trace_final)
            as)
          dg)
        composition_roots"
    using state_s6 state_s7 composition_alignment
    unfolding s8_eq s9_eq by simp
  have state_s11: "PState s11 = PState s10"
    using controlled_stage_outcome_fields
        [OF composition_final_controlled composition_final_out]
    by simp
  have query_start_eq:
    "query_start = s11\<lparr>
      PState := concat (PState s11) composition_final,
      PTranscript := PTranscript s11 @ [composition_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_composition_final])
  have start_state:
    "PState query_start = staged_query_prefix_start_hash prefix"
    unfolding prefix_eq staged_query_prefix_start_hash_def
    using state_s10 state_s11 unfolding query_start_eq by simp
  have query_counter_start: "PQueryCounter query_start = 0"
  proof -
    have root_counter:
      "PQueryCounter s1 = PQueryCounter adversary_initial_state"
      using controlled_stage_outcome_fields[OF root_controlled root_out]
      by simp
    have trace_counter:
      "PQueryCounter s3 = PQueryCounter s2"
      using staged_trace_fri_program_alignment
          [OF controlled trace_bound trace_out]
      by simp
    have final_counter: "PQueryCounter s4 = PQueryCounter s3"
      using controlled_stage_outcome_fields
          [OF trace_final_controlled final_out]
      by simp
    have alpha_counter: "PQueryCounter s6 = PQueryCounter s5"
      using staged_alpha_program_alignment[OF alpha_out] by simp
    have degree_counter: "PQueryCounter s7 = PQueryCounter s6"
      using controlled_stage_outcome_fields[OF degree_controlled degree_out]
      by simp
    have comp_counter: "PQueryCounter s10 = PQueryCounter s9"
      using staged_composition_fri_program_alignment
          [OF controlled composition_bound composition_out]
      by simp
    have comp_final_counter: "PQueryCounter s11 = PQueryCounter s10"
      using controlled_stage_outcome_fields
          [OF composition_final_controlled composition_final_out]
      by simp
    show ?thesis
      using root_counter trace_counter final_counter alpha_counter
        degree_counter comp_counter comp_final_counter
      unfolding s2_eq s5_eq s8_eq s9_eq query_start_eq by simp
  qed
  have query_bound: "0 + i \<le> length (query_opening_budgets budgets)"
    using wf i_bound unfolding staged_budget_wellformed_def by simp
  from checked_staged_query_program_outcome_with_raws
      [OF controlled query_bound query_out]
  obtain raw_idxs query_idxs where
    len: "length query_chunks = i"
    and state:
      "PState prefix_state =
        state_after_query_chunks (PState query_start) query_chunks i"
    and counter:
      "PQueryCounter prefix_state = PQueryCounter query_start + i"
    by blast
  show ?thesis
    using start_state query_counter_start state counter len
    unfolding prefix_eq by simp
qed

lemma checked_staged_query_program_prefix_receive_support:
  assumes i_bound: "i < n"
    and outcome:
      "Some (chunks, t) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              start n) s)"
  obtains prefix_chunks prefix_state raw raw_state chunk chunk_state
      record_state suffix_chunks
  where
    "Some (prefix_chunks, prefix_state) \<in>
      set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            start i) s)"
    "Some (raw, raw_state) \<in>
      set_dist (execute receive_query_index_challenge prefix_state)"
    "Some (chunk, chunk_state) \<in>
      set_dist
        (execute (query_opening_stage A (start + i) raw) raw_state)"
    "verifier_query_round_chunk (index (to_nat raw))
      trace_roots composition_roots chunk"
    "Some ((), record_state) \<in>
      set_dist (execute (record_staged_messages chunk) chunk_state)"
    "Some (suffix_chunks, t) \<in>
      set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            (Suc (start + i)) (n - Suc i)) record_state)"
    "chunks = prefix_chunks @ chunk # suffix_chunks"
proof -
  have decomp:
    "checked_staged_query_program A trace_roots composition_roots start n =
      checked_staged_query_program A trace_roots composition_roots start i \<bind>
        (\<lambda>prefix_chunks.
          receive_query_index_challenge \<bind> (\<lambda>raw.
          let idx = index (to_nat raw) in
          query_opening_stage A (start + i) raw \<bind> (\<lambda>chunk.
          assert
            (verifier_query_round_chunk idx trace_roots composition_roots
              chunk) \<bind> (\<lambda>_.
          record_staged_messages chunk \<bind> (\<lambda>_.
          checked_staged_query_program A trace_roots composition_roots
            (Suc (start + i)) (n - Suc i) \<bind> (\<lambda>suffix_chunks.
          return (prefix_chunks @ chunk # suffix_chunks)))))))"
    by (rule checked_staged_query_program_decomp[OF i_bound])
  from outcome[unfolded decomp]
  obtain prefix_chunks prefix_state raw raw_state chunk chunk_state
      record_state suffix_chunks where
    prefix_out:
      "Some (prefix_chunks, prefix_state) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              start i) s)"
    and raw_out:
      "Some (raw, raw_state) \<in>
        set_dist (execute receive_query_index_challenge prefix_state)"
    and chunk_out:
      "Some (chunk, chunk_state) \<in>
        set_dist
          (execute (query_opening_stage A (start + i) raw) raw_state)"
    and chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    and record_out:
      "Some ((), record_state) \<in>
        set_dist (execute (record_staged_messages chunk) chunk_state)"
    and suffix_out:
      "Some (suffix_chunks, t) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              (Suc (start + i)) (n - Suc i)) record_state)"
    and chunks_eq: "chunks = prefix_chunks @ chunk # suffix_chunks"
    by (auto simp: assert_def throw_no_outcome elim!: set_dist_bindE
        split: if_splits)
  show ?thesis
    by (rule that[OF prefix_out raw_out chunk_out chunk_shape record_out
          suffix_out chunks_eq])
qed

lemma state_after_query_chunks_append_prefix:
  assumes len_prefix: "length prefix = i"
  shows
    "state_after_query_chunks st (prefix @ suffix) i =
      state_after_query_chunks st prefix i"
  using len_prefix
  unfolding state_after_query_chunks_def by simp

lemma checked_staged_query_program_prefix_receive_state_alignment:
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "start + n \<le> length (query_opening_budgets budgets)"
    and i_bound: "i < n"
    and outcome:
      "Some (chunks, t) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              start n) s)"
  obtains prefix_chunks prefix_state raw raw_state chunk chunk_state
      record_state suffix_chunks
  where
    "Some (prefix_chunks, prefix_state) \<in>
      set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            start i) s)"
    "Some (raw, raw_state) \<in>
      set_dist (execute receive_query_index_challenge prefix_state)"
    "Some (chunk, chunk_state) \<in>
      set_dist
        (execute (query_opening_stage A (start + i) raw) raw_state)"
    "verifier_query_round_chunk (index (to_nat raw))
      trace_roots composition_roots chunk"
    "Some ((), record_state) \<in>
      set_dist (execute (record_staged_messages chunk) chunk_state)"
    "Some (suffix_chunks, t) \<in>
      set_dist
        (execute
          (checked_staged_query_program A trace_roots composition_roots
            (Suc (start + i)) (n - Suc i)) record_state)"
    "chunks = prefix_chunks @ chunk # suffix_chunks"
    "PQueryCounter prefix_state = PQueryCounter s + i"
    "PState prefix_state = state_after_query_chunks (PState s) chunks i"
proof -
  from checked_staged_query_program_prefix_receive_support
      [OF i_bound outcome]
  obtain prefix_chunks prefix_state raw raw_state chunk chunk_state
      record_state suffix_chunks where
    prefix_out:
      "Some (prefix_chunks, prefix_state) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              start i) s)"
    and raw_out:
      "Some (raw, raw_state) \<in>
        set_dist (execute receive_query_index_challenge prefix_state)"
    and chunk_out:
      "Some (chunk, chunk_state) \<in>
        set_dist
          (execute (query_opening_stage A (start + i) raw) raw_state)"
    and chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    and record_out:
      "Some ((), record_state) \<in>
        set_dist (execute (record_staged_messages chunk) chunk_state)"
    and suffix_out:
      "Some (suffix_chunks, t) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              (Suc (start + i)) (n - Suc i)) record_state)"
    and chunks_eq: "chunks = prefix_chunks @ chunk # suffix_chunks"
    by (rule checked_staged_query_program_prefix_receive_support
        [OF i_bound outcome])
  have prefix_bound: "start + i \<le> length (query_opening_budgets budgets)"
    using bound i_bound by simp
  from checked_staged_query_program_outcome_with_raws
      [OF controlled prefix_bound prefix_out]
  obtain raw_prefix query_prefix where
    len_prefix: "length prefix_chunks = i"
    and state_prefix:
      "PState prefix_state =
        state_after_query_chunks (PState s) prefix_chunks i"
    and counter_prefix:
      "PQueryCounter prefix_state = PQueryCounter s + i"
    by blast
  have state_full:
    "PState prefix_state = state_after_query_chunks (PState s) chunks i"
    using state_prefix len_prefix
    unfolding chunks_eq
    by (simp add: state_after_query_chunks_append_prefix)
  show ?thesis
    by (rule that[OF prefix_out raw_out chunk_out chunk_shape record_out
          suffix_out chunks_eq counter_prefix state_full])
qed

lemma checked_staged_transcript_program_query_prefix_receive_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
  obtains prefix prefix_state raw raw_state
  where
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "sqp_trace_root prefix = staged_trace_root data"
    "sqp_trace_fri_roots prefix = staged_trace_fri_roots data"
    "sqp_trace_fri_challenges prefix =
      staged_trace_fri_challenges data"
    "sqp_trace_final prefix = staged_trace_final data"
    "sqp_alphas prefix = staged_alphas data"
    "sqp_degree prefix = staged_degree data"
    "sqp_composition_fri_roots prefix =
      staged_composition_fri_roots data"
    "sqp_composition_fri_challenges prefix =
      staged_composition_fri_challenges data"
    "sqp_composition_final prefix = staged_composition_final data"
    "sqp_query_chunks prefix = take i (staged_query_chunks data)"
    "PQueryCounter prefix_state = i"
    "PState prefix_state =
      state_after_query_chunks
        (staged_query_start_hash data) (staged_query_chunks data) i"
    "prefix_state \<le> attacker_state"
    "raw_state \<le> attacker_state"
    "fmlookup (HashMap raw_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
proof -
  from outcome obtain fr s1 s2 trace_roots trace_bs s3 trace_final s4 s5
      as s6 dg s7 s8 s9 composition_roots composition_bs s10
      composition_final s11 query_start query_chunks where
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
      "Some ((), query_start) \<in>
        set_dist (execute (record_staged_message composition_final) s11)"
    and query_out:
      "Some (query_chunks, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              0 rounds)
            query_start)"
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
    unfolding checked_staged_transcript_program_def Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have assert_out_Suc:
    "Some ((), s9) \<in>
      set_dist
        (execute
          (assert
            (ceil_log (Suc (to_nat dg)) \<le>
              ceil_log (Suc maxDegree))) s8)"
    unfolding Suc_eq_plus1
    by (rule assert_out)
  have composition_out_Suc:
    "Some ((composition_roots, composition_bs), s10) \<in>
      set_dist
        (execute
          (staged_composition_fri_program A dg 0
            (ceil_log (Suc (to_nat dg))) []) s9)"
    unfolding Suc_eq_plus1
    by (rule composition_out)
  have query_bound: "0 + rounds \<le> length (query_opening_budgets budgets)"
    using wf unfolding staged_budget_wellformed_def by simp
  from checked_staged_query_program_prefix_receive_state_alignment
      [OF controlled query_bound i_bound query_out]
  obtain prefix_chunks prefix_state raw raw_state chunk chunk_state
      record_state suffix_chunks where
    prefix_query_out:
      "Some (prefix_chunks, prefix_state) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              0 i) query_start)"
    and raw_out:
      "Some (raw, raw_state) \<in>
        set_dist (execute receive_query_index_challenge prefix_state)"
    and chunk_out:
      "Some (chunk, chunk_state) \<in>
        set_dist
          (execute (query_opening_stage A (0 + i) raw) raw_state)"
    and chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    and record_out:
      "Some ((), record_state) \<in>
        set_dist (execute (record_staged_messages chunk) chunk_state)"
    and suffix_out:
      "Some (suffix_chunks, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              (Suc (0 + i)) (rounds - Suc i)) record_state)"
    and chunks_eq: "query_chunks = prefix_chunks @ chunk # suffix_chunks"
    and counter_prefix:
      "PQueryCounter prefix_state = PQueryCounter query_start + i"
    and state_prefix:
      "PState prefix_state =
        state_after_query_chunks (PState query_start) query_chunks i"
    by (rule checked_staged_query_program_prefix_receive_state_alignment
        [OF controlled query_bound i_bound query_out])
  let ?prefix =
    "\<lparr>sqp_trace_root = fr,
     sqp_trace_fri_roots = trace_roots,
     sqp_trace_fri_challenges = trace_bs,
     sqp_trace_final = trace_final,
     sqp_alphas = as,
     sqp_degree = dg,
     sqp_composition_fri_roots = composition_roots,
     sqp_composition_fri_challenges = composition_bs,
     sqp_composition_final = composition_final,
     sqp_query_chunks = prefix_chunks\<rparr>"
  have alpha_prefix_out:
    "Some ((fr, trace_roots, trace_bs, trace_final), s5) \<in>
      set_dist
        (execute (staged_alpha_prefix_program A) adversary_initial_state)"
  proof -
    have after_record_final:
      "Some ((fr, trace_roots, trace_bs, trace_final), s5) \<in>
        set_dist
          (execute
            (record_staged_message trace_final \<bind>
              (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final)))
            s4)"
      by (rule_tac x="()" and t=s5 in set_dist_bindI)
        (rule record_final, simp)
    have after_final:
      "Some ((fr, trace_roots, trace_bs, trace_final), s5) \<in>
        set_dist
          (execute
            (trace_final_stage A trace_bs \<bind>
              (\<lambda>trace_final.
                record_staged_message trace_final \<bind>
                (\<lambda>_. return (fr, trace_roots, trace_bs, trace_final))))
            s3)"
      by (rule_tac x=trace_final and t=s4 in set_dist_bindI)
        (rule final_out, rule after_record_final)
    have after_trace:
      "Some ((fr, trace_roots, trace_bs, trace_final), s5) \<in>
        set_dist
          (execute
            (staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
              (\<lambda>(trace_roots, trace_bs).
                trace_final_stage A trace_bs \<bind>
                (\<lambda>trace_final.
                  record_staged_message trace_final \<bind>
                  (\<lambda>_. return
                    (fr, trace_roots, trace_bs, trace_final)))))
            s2)"
      apply (rule_tac x="(trace_roots, trace_bs)" and t=s3
          in set_dist_bindI)
       apply (rule trace_out)
      apply (simp add: after_final)
      done
    have after_record_root:
      "Some ((fr, trace_roots, trace_bs, trace_final), s5) \<in>
        set_dist
          (execute
            (record_staged_message fr \<bind>
              (\<lambda>_. staged_trace_fri_program A 0 (ceil_log clength) [] \<bind>
                (\<lambda>(trace_roots, trace_bs).
                  trace_final_stage A trace_bs \<bind>
                  (\<lambda>trace_final.
                    record_staged_message trace_final \<bind>
                    (\<lambda>_. return
                      (fr, trace_roots, trace_bs, trace_final))))))
            s1)"
      by (rule_tac x="()" and t=s2 in set_dist_bindI)
        (rule record_root, rule after_trace)
    show ?thesis
      unfolding staged_alpha_prefix_program_def
      by (rule_tac x=fr and t=s1 in set_dist_bindI)
        (rule root_out, rule after_record_root)
  qed
  have prefix_program_out:
    "Some (?prefix, prefix_state) \<in>
      set_dist
        (execute
          (checked_staged_query_challenge_prefix_program A i)
          adversary_initial_state)"
  proof -
    have after_prefix_query:
      "Some (?prefix, prefix_state) \<in>
        set_dist
          (execute
            (checked_staged_query_program A trace_roots composition_roots
              0 i \<bind>
              (\<lambda>query_chunks.
                return
                  \<lparr>sqp_trace_root = fr,
                   sqp_trace_fri_roots = trace_roots,
                   sqp_trace_fri_challenges = trace_bs,
                   sqp_trace_final = trace_final,
                   sqp_alphas = as,
                   sqp_degree = dg,
                   sqp_composition_fri_roots = composition_roots,
                   sqp_composition_fri_challenges = composition_bs,
                   sqp_composition_final = composition_final,
                   sqp_query_chunks = query_chunks\<rparr>))
            query_start)"
      by (rule_tac x=prefix_chunks and t=prefix_state in set_dist_bindI)
        (rule prefix_query_out, simp)
    have after_record_composition_final:
      "Some (?prefix, prefix_state) \<in>
        set_dist
          (execute
            (record_staged_message composition_final \<bind>
              (\<lambda>_.
                checked_staged_query_program A trace_roots composition_roots
                  0 i \<bind>
                (\<lambda>query_chunks.
                  return
                    \<lparr>sqp_trace_root = fr,
                     sqp_trace_fri_roots = trace_roots,
                     sqp_trace_fri_challenges = trace_bs,
                     sqp_trace_final = trace_final,
                     sqp_alphas = as,
                     sqp_degree = dg,
                     sqp_composition_fri_roots = composition_roots,
                     sqp_composition_fri_challenges = composition_bs,
                     sqp_composition_final = composition_final,
                     sqp_query_chunks = query_chunks\<rparr>)))
            s11)"
      by (rule_tac x="()" and t=query_start in set_dist_bindI)
        (rule record_composition_final, rule after_prefix_query)
    have after_composition_final:
      "Some (?prefix, prefix_state) \<in>
        set_dist
          (execute
            (composition_final_stage A dg composition_bs \<bind>
              (\<lambda>composition_final.
                record_staged_message composition_final \<bind>
                (\<lambda>_.
                  checked_staged_query_program A trace_roots
                    composition_roots 0 i \<bind>
                  (\<lambda>query_chunks.
                    return
                      \<lparr>sqp_trace_root = fr,
                       sqp_trace_fri_roots = trace_roots,
                       sqp_trace_fri_challenges = trace_bs,
                       sqp_trace_final = trace_final,
                       sqp_alphas = as,
                       sqp_degree = dg,
                       sqp_composition_fri_roots = composition_roots,
                       sqp_composition_fri_challenges = composition_bs,
                       sqp_composition_final = composition_final,
                       sqp_query_chunks = query_chunks\<rparr>))))
            s10)"
      by (rule_tac x=composition_final and t=s11 in set_dist_bindI)
        (rule composition_final_out, rule after_record_composition_final)
    have after_composition:
      "Some (?prefix, prefix_state) \<in>
        set_dist
          (execute
            (staged_composition_fri_program A dg 0
              (ceil_log (Suc (to_nat dg))) [] \<bind>
              (\<lambda>(composition_roots, composition_bs).
                composition_final_stage A dg composition_bs \<bind>
                (\<lambda>composition_final.
                  record_staged_message composition_final \<bind>
                  (\<lambda>_.
                    checked_staged_query_program A trace_roots
                      composition_roots 0 i \<bind>
                    (\<lambda>query_chunks.
                      return
                        \<lparr>sqp_trace_root = fr,
                         sqp_trace_fri_roots = trace_roots,
                         sqp_trace_fri_challenges = trace_bs,
                         sqp_trace_final = trace_final,
                         sqp_alphas = as,
                         sqp_degree = dg,
                         sqp_composition_fri_roots = composition_roots,
                         sqp_composition_fri_challenges = composition_bs,
                         sqp_composition_final = composition_final,
                         sqp_query_chunks = query_chunks\<rparr>)))))
            s9)"
      apply (rule_tac x="(composition_roots, composition_bs)" and t=s10
          in set_dist_bindI)
       apply (rule composition_out_Suc)
      apply (simp add: after_composition_final)
      done
    have after_assert:
      "Some (?prefix, prefix_state) \<in>
        set_dist
          (execute
            (assert (ceil_log (Suc (to_nat dg)) \<le>
              ceil_log (Suc maxDegree)) \<bind>
              (\<lambda>_.
                staged_composition_fri_program A dg 0
                  (ceil_log (Suc (to_nat dg))) [] \<bind>
                (\<lambda>(composition_roots, composition_bs).
                  composition_final_stage A dg composition_bs \<bind>
                  (\<lambda>composition_final.
                    record_staged_message composition_final \<bind>
                    (\<lambda>_.
                      checked_staged_query_program A trace_roots
                        composition_roots 0 i \<bind>
                      (\<lambda>query_chunks.
                        return
                          \<lparr>sqp_trace_root = fr,
                           sqp_trace_fri_roots = trace_roots,
                           sqp_trace_fri_challenges = trace_bs,
                           sqp_trace_final = trace_final,
                           sqp_alphas = as,
                           sqp_degree = dg,
                           sqp_composition_fri_roots = composition_roots,
                           sqp_composition_fri_challenges = composition_bs,
                           sqp_composition_final = composition_final,
                           sqp_query_chunks = query_chunks\<rparr>))))))
            s8)"
      apply (rule_tac x="()" and t=s9 in set_dist_bindI)
       apply (rule assert_out_Suc)
      apply (simp add: after_composition)
      done
    have after_record_degree:
      "Some (?prefix, prefix_state) \<in>
        set_dist
          (execute
            (record_staged_message dg \<bind>
              (\<lambda>_.
                assert (ceil_log (Suc (to_nat dg)) \<le>
                  ceil_log (Suc maxDegree)) \<bind>
                (\<lambda>_.
                  staged_composition_fri_program A dg 0
                    (ceil_log (Suc (to_nat dg))) [] \<bind>
                  (\<lambda>(composition_roots, composition_bs).
                    composition_final_stage A dg composition_bs \<bind>
                    (\<lambda>composition_final.
                      record_staged_message composition_final \<bind>
                      (\<lambda>_.
                        checked_staged_query_program A trace_roots
                          composition_roots 0 i \<bind>
                        (\<lambda>query_chunks.
                          return
                            \<lparr>sqp_trace_root = fr,
                             sqp_trace_fri_roots = trace_roots,
                             sqp_trace_fri_challenges = trace_bs,
                             sqp_trace_final = trace_final,
                             sqp_alphas = as,
                             sqp_degree = dg,
                             sqp_composition_fri_roots = composition_roots,
                             sqp_composition_fri_challenges = composition_bs,
                             sqp_composition_final = composition_final,
                             sqp_query_chunks = query_chunks\<rparr>)))))))
            s7)"
      apply (rule_tac x="()" and t=s8 in set_dist_bindI)
       apply (rule record_degree)
      apply (simp add: after_assert)
      done
    have after_degree:
      "Some (?prefix, prefix_state) \<in>
        set_dist
          (execute
            (degree_stage A as \<bind>
              (\<lambda>dg.
                record_staged_message dg \<bind>
                (\<lambda>_.
                  assert (ceil_log (Suc (to_nat dg)) \<le>
                    ceil_log (Suc maxDegree)) \<bind>
                  (\<lambda>_.
                    staged_composition_fri_program A dg 0
                      (ceil_log (Suc (to_nat dg))) [] \<bind>
                    (\<lambda>(composition_roots, composition_bs).
                      composition_final_stage A dg composition_bs \<bind>
                      (\<lambda>composition_final.
                        record_staged_message composition_final \<bind>
                        (\<lambda>_.
                          checked_staged_query_program A trace_roots
                            composition_roots 0 i \<bind>
                          (\<lambda>query_chunks.
                            return
                              \<lparr>sqp_trace_root = fr,
                               sqp_trace_fri_roots = trace_roots,
                               sqp_trace_fri_challenges = trace_bs,
                               sqp_trace_final = trace_final,
                               sqp_alphas = as,
                               sqp_degree = dg,
                               sqp_composition_fri_roots = composition_roots,
                               sqp_composition_fri_challenges = composition_bs,
                               sqp_composition_final = composition_final,
                               sqp_query_chunks = query_chunks\<rparr>))))))))
            s6)"
      apply (rule_tac x=dg and t=s7 in set_dist_bindI)
       apply (rule degree_out)
      apply (simp add: after_record_degree)
      done
    have after_alpha:
      "Some (?prefix, prefix_state) \<in>
        set_dist
          (execute
            (staged_alpha_program (length spec) \<bind>
              (\<lambda>as.
                degree_stage A as \<bind>
                (\<lambda>dg.
                  record_staged_message dg \<bind>
                  (\<lambda>_.
                    assert (ceil_log (Suc (to_nat dg)) \<le>
                      ceil_log (Suc maxDegree)) \<bind>
                    (\<lambda>_.
                      staged_composition_fri_program A dg 0
                        (ceil_log (Suc (to_nat dg))) [] \<bind>
                      (\<lambda>(composition_roots, composition_bs).
                        composition_final_stage A dg composition_bs \<bind>
                        (\<lambda>composition_final.
                          record_staged_message composition_final \<bind>
                          (\<lambda>_.
                            checked_staged_query_program A trace_roots
                              composition_roots 0 i \<bind>
                            (\<lambda>query_chunks.
                              return
                                \<lparr>sqp_trace_root = fr,
                                 sqp_trace_fri_roots = trace_roots,
                                 sqp_trace_fri_challenges = trace_bs,
                                 sqp_trace_final = trace_final,
                                 sqp_alphas = as,
                                 sqp_degree = dg,
                                 sqp_composition_fri_roots = composition_roots,
                                 sqp_composition_fri_challenges = composition_bs,
                                 sqp_composition_final = composition_final,
                                 sqp_query_chunks = query_chunks\<rparr>)))))))))
            s5)"
      apply (rule_tac x=as and t=s6 in set_dist_bindI)
       apply (rule alpha_out)
      apply (simp add: after_degree)
      done
    show ?thesis
      unfolding checked_staged_query_challenge_prefix_program_def Let_def
      apply (rule_tac x="(fr, trace_roots, trace_bs, trace_final)" and t=s5
          in set_dist_bindI)
       apply (rule alpha_prefix_out)
      apply (simp add: after_alpha)
      done
  qed
  have prefix_with_state_out:
    "Some ((?prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i)
          adversary_initial_state)"
    unfolding checked_staged_query_prefix_with_state_def
    by (rule set_dist_bindI[where x="?prefix" and t=prefix_state,
          OF prefix_program_out get_bind_return_state_support])
  have prefix_receive_out:
    "Some (((?prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    unfolding checked_staged_query_prefix_receive_with_state_def
    by (intro set_dist_bindI[OF prefix_with_state_out]
        set_dist_bindI[OF raw_out])
      simp
  have root_controlled:
    "controlled_ro_program (trace_root_budget budgets) (trace_root_stage A)"
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
  have root_state: "PState s1 = 0"
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
    "PState s3 = foldl concat (PState s2) trace_roots"
    using staged_trace_fri_program_alignment
        [OF controlled trace_bound trace_out]
    by simp
  have state_s3:
    "PState s3 = foldl concat (concat 0 fr) trace_roots"
    using root_state trace_alignment unfolding s2_eq by simp
  have state_s4: "PState s4 = PState s3"
    using controlled_stage_outcome_fields
        [OF trace_final_controlled final_out]
    by simp
  have s5_eq:
    "s5 = s4\<lparr>
      PState := concat (PState s4) trace_final,
      PTranscript := PTranscript s4 @ [trace_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_final])
  have alpha_alignment:
    "PState s6 = foldl concat (PState s5) as"
    using staged_alpha_program_alignment[OF alpha_out] by simp
  have state_s6:
    "PState s6 =
      foldl concat
        (concat (foldl concat (concat 0 fr) trace_roots) trace_final)
        as"
    using state_s3 state_s4 alpha_alignment unfolding s5_eq by simp
  have state_s7: "PState s7 = PState s6"
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
    "PState s10 = foldl concat (PState s9) composition_roots"
    using staged_composition_fri_program_alignment
        [OF controlled composition_bound composition_out]
    by simp
  have state_s10:
    "PState s10 =
      foldl concat
        (concat
          (foldl concat
            (concat (foldl concat (concat 0 fr) trace_roots) trace_final)
            as)
          dg)
        composition_roots"
    using state_s6 state_s7 composition_alignment
    unfolding s8_eq s9_eq by simp
  have state_s11: "PState s11 = PState s10"
    using controlled_stage_outcome_fields
        [OF composition_final_controlled composition_final_out]
    by simp
  have query_start_eq:
    "query_start = s11\<lparr>
      PState := concat (PState s11) composition_final,
      PTranscript := PTranscript s11 @ [composition_final]\<rparr>"
    by (rule record_staged_message_outcome[OF record_composition_final])
  have state_query_start:
    "PState query_start =
      concat
        (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat 0 fr) trace_roots) trace_final)
              as)
            dg)
          composition_roots)
        composition_final"
    using state_s10 state_s11 unfolding query_start_eq by simp
  have start_state:
    "PState query_start = staged_query_start_hash data"
    unfolding data_eq staged_query_start_hash_def
      staged_composition_fri_start_hash_def staged_trace_fri_start_hash_def
    using state_query_start by simp
  have query_counter_start: "PQueryCounter query_start = 0"
  proof -
    have root_fields:
      "PQueryCounter s1 = PQueryCounter adversary_initial_state"
      using controlled_stage_outcome_fields[OF root_controlled root_out]
      by simp
    have trace_counters:
      "PQueryCounter s3 = PQueryCounter s2"
      using staged_trace_fri_program_alignment
          [OF controlled trace_bound trace_out]
      by simp
    have final_counter: "PQueryCounter s4 = PQueryCounter s3"
      using controlled_stage_outcome_fields
          [OF trace_final_controlled final_out]
      by simp
    have alpha_counter: "PQueryCounter s6 = PQueryCounter s5"
      using staged_alpha_program_alignment[OF alpha_out] by simp
    have degree_counter: "PQueryCounter s7 = PQueryCounter s6"
      using controlled_stage_outcome_fields[OF degree_controlled degree_out]
      by simp
    have comp_counter: "PQueryCounter s10 = PQueryCounter s9"
      using staged_composition_fri_program_alignment
          [OF controlled composition_bound composition_out]
      by simp
    have comp_final_counter: "PQueryCounter s11 = PQueryCounter s10"
      using controlled_stage_outcome_fields
          [OF composition_final_controlled composition_final_out]
      by simp
    show ?thesis
      using root_fields trace_counters final_counter alpha_counter
        degree_counter comp_counter comp_final_counter
      unfolding s2_eq s5_eq s8_eq s9_eq query_start_eq by simp
  qed
  have prefix_counter: "PQueryCounter prefix_state = i"
    using counter_prefix query_counter_start by simp
  have prefix_state_eq:
    "PState prefix_state =
      state_after_query_chunks
        (staged_query_start_hash data) (staged_query_chunks data) i"
    using state_prefix start_state unfolding data_eq by simp
  have prefix_query_bound: "0 + i \<le> length (query_opening_budgets budgets)"
    using query_bound i_bound by simp
  have prefix_len: "length prefix_chunks = i"
  proof -
    from checked_staged_query_program_outcome_with_raws
        [OF controlled prefix_query_bound prefix_query_out]
    show ?thesis
      by blast
  qed
  have prefix_chunks_eq:
    "prefix_chunks = take i query_chunks"
    using chunks_eq prefix_len by simp
  have receive_lookup:
    "fmlookup (HashMap raw_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    using receive_query_index_challenge_outcome[OF raw_out]
      prefix_counter prefix_state_eq
    by simp
  have stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled wf i_bound
    unfolding staged_adversary_controlled_def staged_budget_wellformed_def
    by simp
  have raw_chunk_ext: "raw_state \<le> chunk_state"
  proof -
    have chunk_out_i:
      "Some (chunk, chunk_state) \<in>
        set_dist (execute (query_opening_stage A i raw) raw_state)"
      using chunk_out by simp
    show ?thesis
      using controlled_ro_program_extension[OF stage_controlled] chunk_out_i
      unfolding hash_extension_preserving_def by blast
  qed
  have prefix_raw_ext: "prefix_state \<le> raw_state"
    by (rule receive_query_index_challenge_extends[OF raw_out])
  have record_state_eq:
    "record_state = chunk_state\<lparr>
      PState := foldl concat (PState chunk_state) chunk,
      PTranscript := PTranscript chunk_state @ chunk\<rparr>"
    by (rule record_staged_messages_outcome[OF record_out])
  have chunk_record_ext: "chunk_state \<le> record_state"
    unfolding record_state_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have suffix_bound:
    "Suc (0 + i) + (rounds - Suc i) \<le>
      length (query_opening_budgets budgets)"
    using query_bound i_bound by simp
  have suffix_target:
    "hash_target_program {}
      (sum_list
        (take (rounds - Suc i)
          (drop (Suc (0 + i)) (query_opening_budgets budgets))) +
        (rounds - Suc i))
      (checked_staged_query_program A trace_roots composition_roots
        (Suc (0 + i)) (rounds - Suc i))"
    by (rule hash_target_program_checked_staged_query_program
        [OF controlled suffix_bound])
  have suffix_ext: "record_state \<le> attacker_state"
    using hash_target_program_extension[OF suffix_target] suffix_out
    unfolding hash_extension_preserving_def by blast
  have raw_ext: "raw_state \<le> attacker_state"
    by (rule hash_ext_trans[OF raw_chunk_ext])
      (rule hash_ext_trans[OF chunk_record_ext suffix_ext])
  have prefix_ext: "prefix_state \<le> attacker_state"
    by (rule hash_ext_trans[OF prefix_raw_ext raw_ext])
  show ?thesis
    by (rule that[OF prefix_receive_out])
      (use data_eq prefix_chunks_eq prefix_counter prefix_state_eq prefix_ext
        raw_ext receive_lookup in simp_all)
qed

lemma checked_staged_transcript_program_query_prefix_receive_final_lookup_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and final_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
  obtains prefix prefix_state raw_state where
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show ?thesis
  proof (rule checked_staged_transcript_program_query_prefix_receive_support
      [OF wf controlled i_bound outcome])
    fix prefix prefix_state raw' raw_state
    assume prefix_receive:
        "Some (((prefix, prefix_state), raw'), raw_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_receive_with_state A i)
              adversary_initial_state)"
      and raw_ext: "raw_state \<le> attacker_state"
      and raw_lookup:
        "fmlookup (HashMap raw_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data) (staged_query_chunks data) i)) =
          Some raw'"
  have raw_ext_s: "raw_state \<le> ?s"
    by (rule hash_extends_verifier_state_from_adversary_right[OF raw_ext])
  have s_ext_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  have raw_ext_final: "raw_state \<le> final_state"
    by (rule hash_ext_trans[OF raw_ext_s s_ext_final])
  have final_lookup_raw':
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw'"
    by (rule hash_extension_lookup[OF raw_lookup raw_ext_final])
  have raw_eq: "raw' = raw"
    using final_lookup final_lookup_raw' by simp
  have prefix_receive_raw:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    using prefix_receive raw_eq by simp
  show ?thesis
    by (rule that[OF prefix_receive_raw])
  qed
qed

lemma checked_staged_transcript_program_query_prefix_receive_final_lookup_support_with_alphas:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and final_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
  obtains prefix prefix_state raw_state where
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "sqp_alphas prefix = staged_alphas data"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show ?thesis
  proof (rule checked_staged_transcript_program_query_prefix_receive_support
      [OF wf controlled i_bound outcome])
    fix prefix prefix_state raw' raw_state
    assume prefix_receive:
        "Some (((prefix, prefix_state), raw'), raw_state) \<in>
          set_dist
            (execute (checked_staged_query_prefix_receive_with_state A i)
              adversary_initial_state)"
      and alphas_eq: "sqp_alphas prefix = staged_alphas data"
      and raw_ext: "raw_state \<le> attacker_state"
      and raw_lookup:
        "fmlookup (HashMap raw_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data) (staged_query_chunks data) i)) =
          Some raw'"
    have raw_ext_s: "raw_state \<le> ?s"
      by (rule hash_extends_verifier_state_from_adversary_right[OF raw_ext])
    have s_ext_final: "?s \<le> final_state"
      by (rule verify_monad_hash_extends[OF verifier])
    have raw_ext_final: "raw_state \<le> final_state"
      by (rule hash_ext_trans[OF raw_ext_s s_ext_final])
    have final_lookup_raw':
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw'"
      by (rule hash_extension_lookup[OF raw_lookup raw_ext_final])
    have raw_eq: "raw' = raw"
      using final_lookup final_lookup_raw' by simp
    have prefix_receive_raw:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
      using prefix_receive raw_eq by simp
    show ?thesis
      by (rule that[OF prefix_receive_raw alphas_eq])
  qed
qed

end

end
