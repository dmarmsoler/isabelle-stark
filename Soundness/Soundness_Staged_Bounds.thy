(*  Title:      Stark/Soundness_Staged_Bounds.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Bounds
  imports
    Soundness_Staged_Transcript
    Soundness_Staged_Partial_Query
    Soundness_Staged_Partial_Query_Branch
    Staged_Security_Experiment_Composition_Partial
    Staged_Security_Experiment_Composition_Query_Residual
    Staged_Security_Experiment_Composition_Query_Actual_Run
begin

text \<open>Staged soundness bad-event bounds and accepted-execution partitions.\<close>

context soundness
begin

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_from_query_bad_rounds:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and round_bound:
      "\<And>i. i < rounds \<Longrightarrow>
        wp_event (checked_staged_security_experiment_with_data_state A)
          (staged_security_with_data_state_query_bad_hit_at i)
          adversary_initial_state \<le> C i"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
proof -
	  have "wp_event (checked_staged_security_experiment_with_data_state A)
	      (staged_security_with_data_state_verifier_event query_bad)
	      adversary_initial_state \<le>
	    wp_event (checked_staged_security_experiment_with_data_state A)
	      staged_security_with_data_state_query_bad_hit
	      adversary_initial_state"
	    by (rule checked_staged_security_with_data_state_query_bad_verifier_event_bound)
	      simp
  also have "... \<le> (\<Sum>i<rounds. C i)"
    by (rule
        checked_staged_security_with_data_state_query_bad_hit_bound_from_rounds)
      (rule round_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_from_committed_prefix_hit_or_tree_output:
  fixes committed_error tree_error :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and committed_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_committed_prefix_hit A)
        adversary_initial_state \<le> committed_error"
    and tree_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_tree_output_hit A)
        adversary_initial_state \<le> tree_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le> committed_error + tree_error"
proof -
	  have "wp_event (checked_staged_security_experiment_with_data_state A)
	      (staged_security_with_data_state_verifier_event query_bad)
	      adversary_initial_state \<le>
	    wp_event (checked_staged_security_experiment_with_data_state A)
	      staged_security_with_data_state_query_bad_hit
	      adversary_initial_state"
	    by (rule checked_staged_security_with_data_state_query_bad_verifier_event_bound)
	      simp
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_committed_prefix_hit A)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_tree_output_hit A)
        adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_query_bad_bound_from_committed_prefix_hit_or_tree_output
        [OF wf controlled])
  also have "... \<le> committed_error + tree_error"
    by (intro add_mono committed_bound tree_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_from_length_committed_prefix_hit_or_tree_output:
  fixes committed_error tree_error :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and committed_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_length_committed_prefix_hit A)
        adversary_initial_state \<le> committed_error"
    and tree_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_tree_output_hit A)
        adversary_initial_state \<le> tree_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le> committed_error + tree_error"
proof -
	  have "wp_event (checked_staged_security_experiment_with_data_state A)
	      (staged_security_with_data_state_verifier_event query_bad)
	      adversary_initial_state \<le>
	    wp_event (checked_staged_security_experiment_with_data_state A)
	      staged_security_with_data_state_query_bad_hit
	      adversary_initial_state"
	    by (rule checked_staged_security_with_data_state_query_bad_verifier_event_bound)
	      simp
  also have "... \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_length_committed_prefix_hit A)
        adversary_initial_state +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_tree_output_hit A)
        adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_query_bad_bound_from_length_committed_prefix_hit_or_tree_output
        [OF wf controlled])
  also have "... \<le> committed_error + tree_error"
    by (intro add_mono committed_bound tree_bound)
  finally show ?thesis .
qed

lemma staged_security_with_data_state_query_tree_output_hit_imp_partial_header_key_hit_or_collision:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and tree_hit:
      "staged_security_with_data_state_query_tree_output_hit A out"
  shows
    "staged_security_with_data_state_query_partial_header_key_hit out \<or>
     staged_security_with_data_state_verifier_event
       hash_map_output_collision_bad out"
proof (cases out)
  case None
  then show ?thesis
    using tree_hit
    unfolding staged_security_with_data_state_query_tree_output_hit_def
    by simp
next
  case (Some packed)
  then obtain data attacker_state result final_state where out_eq:
    "out = Some (((data, attacker_state), result), final_state)"
    by (cases packed, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
	  have tree_body:
	    "\<exists>i prefix prefix_state raw raw_state trace_table composition_table
	        as query_idxs trace_tree composition_tree.
	      i < rounds \<and>
	      Some (data, attacker_state) \<in>
	        set_dist
	          (execute (checked_staged_transcript_program A)
	            adversary_initial_state) \<and>
	      Some (result, final_state) \<in> set_dist (execute verify_monad ?s) \<and>
	      accepted_with_bound_tables ?s (Some (result, final_state))
	        trace_table composition_table as query_idxs \<and>
	      fmlookup (HashMap final_state)
	        (QueryIndexChallenge i
	          (state_after_query_chunks
	            (staged_query_start_hash data) (staged_query_chunks data) i)) =
	        Some raw \<and>
	      index (to_nat raw) \<in>
	        query_sampling_success_space trace_table composition_table
	          (staged_alphas data) \<and>
	      Some (((prefix, prefix_state), raw), raw_state) \<in>
	        set_dist
	          (execute (checked_staged_query_prefix_receive_with_state A i)
	            adversary_initial_state) \<and>
	      sqp_composition_fri_roots prefix \<noteq> [] \<and>
	      created_tree trace_table trace_tree final_state \<and>
	      sqp_trace_root prefix = value trace_tree \<and>
	      created_tree composition_table composition_tree final_state \<and>
	      hd (sqp_composition_fri_roots prefix) = value composition_tree \<and>
	      hash_map_new_output_hit
	        (set_tree trace_tree \<union> set_tree composition_tree)
	        prefix_state final_state"
	    using tree_hit
	    unfolding out_eq
	      staged_security_with_data_state_query_tree_output_hit_def Let_def
	    by simp
	  from tree_body
	  obtain i prefix prefix_state raw raw_state trace_table composition_table
	      as query_idxs trace_tree composition_tree where
	    i_bound: "i < rounds"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in>
        set_dist (execute verify_monad ?s)"
    and bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and lookup_final_raw:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
	    and raw_hit:
	      "index (to_nat raw) \<in>
	        query_sampling_success_space trace_table composition_table
	          (staged_alphas data)"
	    by blast
	  have accepted_out: "accepted (Some (result, final_state))"
	    unfolding accepted_def by simp
	  show ?thesis
	  proof (cases "hash_map_output_collision final_state")
	    case True
	    then show ?thesis
	      unfolding out_eq staged_security_with_data_state_verifier_event_def
	        hash_map_output_collision_bad_def
	      using accepted_out by simp
  next
    case clean: False
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
    from bound obtain fr f_fri_roots f_final dg composition_fri_roots final
        rest where
      header:
        "verifier_header_transcript ?s fr f_fri_roots f_final as dg
          composition_fri_roots final rest"
      and trace_bind:
        "merkle_root_binds_table fr trace_table final_state"
      and comp_nonempty: "composition_fri_roots \<noteq> []"
      and comp_bind:
        "merkle_root_binds_table (hd composition_fri_roots)
          composition_table final_state"
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
      using verifier_header_transcript_unique[OF header staged_header]
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
	    have raw_partial_hit:
	      "index (to_nat raw) \<in>
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
	      have raw_in_sample:
	        "index (to_nat raw) \<in> query_sample_space"
	        using raw_hit query_sampling_success_space_subset by blast
	      show ?thesis
	      unfolding query_header_supported_partial_union_good_sets_def
	        using candidate raw_hit raw_in_sample by blast
	    qed
    then show ?thesis
      unfolding out_eq
        staged_security_with_data_state_query_partial_header_key_hit_def
        Let_def
      using i_bound lookup_final_raw by auto
  qed
qed

lemma staged_security_with_data_state_query_tree_output_hit_bound_from_partial_header_key_hit_or_collision:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_tree_output_hit A)
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_header_key_hit
      adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        hash_map_output_collision_bad)
      adversary_initial_state"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?partial = staged_security_with_data_state_query_partial_header_key_hit
  let ?collision =
    "staged_security_with_data_state_verifier_event
      hash_map_output_collision_bad"
  have "wp_event ?M (staged_security_with_data_state_query_tree_output_hit A)
      adversary_initial_state \<le>
    wp_event ?M (\<lambda>out. ?partial out \<or> ?collision out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (rule
        staged_security_with_data_state_query_tree_output_hit_imp_partial_header_key_hit_or_collision
        [OF wf controlled])
  also have "... \<le>
      wp_event ?M ?partial adversary_initial_state +
      wp_event ?M ?collision adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_by_length_prefixes_partial_header_and_collision:
  fixes partial_error collision_error :: prob
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and partial_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_header_key_hit
        adversary_initial_state \<le> partial_error"
    and collision_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          hash_map_output_collision_bad)
        adversary_initial_state \<le> collision_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le>
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound +
        hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1)) +
      (partial_error + collision_error)"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?Tree = "staged_security_with_data_state_query_tree_output_hit A"
  let ?PrefixSum =
    "(\<Sum>i<rounds.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1))"
  have tree_bound:
    "wp_event ?M ?Tree adversary_initial_state \<le>
      partial_error + collision_error"
  proof -
    have "wp_event ?M ?Tree adversary_initial_state \<le>
        wp_event ?M staged_security_with_data_state_query_partial_header_key_hit
          adversary_initial_state +
        wp_event ?M
          (staged_security_with_data_state_verifier_event
            hash_map_output_collision_bad)
          adversary_initial_state"
      by (rule
          staged_security_with_data_state_query_tree_output_hit_bound_from_partial_header_key_hit_or_collision
          [OF wf controlled])
    also have "... \<le> partial_error + collision_error"
      by (intro add_mono partial_bound collision_bound)
    finally show ?thesis .
  qed
  have "wp_event ?M
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le>
      ?PrefixSum + wp_event ?M ?Tree adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_query_bad_verifier_event_bound_by_length_prefixes_and_tree
        [OF raw_bound wf controlled])
  also have "... \<le> ?PrefixSum + (partial_error + collision_error)"
    by (intro add_mono order_refl tree_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_by_length_prefixes_partial_header_and_controlled_collision:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and partial_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_header_key_hit
        adversary_initial_state \<le> partial_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le>
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound +
        hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1)) +
      (partial_error +
        hash_collision_budget_value 0
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget + verifier_hash_query_budget))"
proof -
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
    checked_staged_security_with_data_state_query_bad_verifier_event_bound_by_length_prefixes_partial_header_and_collision
        [OF raw_bound wf controlled partial_bound collision_bound])
qed

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_by_length_prefixes_partial_header_and_controlled_collision_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and partial_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_header_key_hit
        adversary_initial_state \<le> partial_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le>
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound +
        hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1)) +
      (partial_error +
        hash_collision_budget_value 0
          (staged_attacker_query_budget budgets +
            staged_challenge_query_budget + verifier_hash_query_budget))"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_query_bad_verifier_event_bound_by_length_prefixes_partial_header_and_controlled_collision
        [OF raw_bound wf controlled partial_bound])
qed

lemma checked_staged_security_with_data_state_partial_trace_openings_inconsistent_bad_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_trace_openings_inconsistent_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_trace_openings_inconsistent_bad)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          hash_map_output_collision_bad)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro: partial_trace_openings_inconsistent_bad_imp_hash_map_output_collision_bad
        split: option.splits prod.splits)
  also have "... \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_partial_composition_openings_inconsistent_bad_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_composition_openings_inconsistent_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_composition_openings_inconsistent_bad)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          hash_map_output_collision_bad)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          partial_composition_openings_inconsistent_bad_imp_hash_map_output_collision_bad
        split: option.splits prod.splits)
  also have "... \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          hash_map_output_collision_bad)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro: partial_merkle_inconsistency_bad_imp_hash_map_output_collision_bad
        split: option.splits prod.splits)
  also have "... \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  finally show ?thesis .
qed

lemma checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad_bound_controlled:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad
      adversary_initial_state \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
proof -
  have event_eq:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad
      adversary_initial_state =
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        partial_merkle_inconsistency_bad)
      adversary_initial_state"
    unfolding
      checked_staged_security_with_actual_alpha_prefix_partial_merkle_inconsistency_bad_def
    using
      checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection
      [of A partial_merkle_inconsistency_bad]
    by simp
  show ?thesis
    unfolding event_eq
    by (rule
        checked_staged_security_with_data_state_partial_merkle_inconsistency_bad_bound_controlled
        [OF wf controlled])
qed

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
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        supported_output_local_side_bad)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          hash_map_output_collision_bad)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        supported_output_local_side_bad_iff_hash_map_output_collision_bad
        split: option.splits prod.splits)
  also have "... \<le>
      hash_collision_budget_value 0
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget + verifier_hash_query_budget)"
    by (rule
        checked_staged_security_with_data_state_hash_map_output_collision_bad_bound_controlled
        [OF wf controlled])
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_supported_pairwise_side_bad_bound_from_coupling:
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
  have event_eq:
    "?E supported_pairwise_side_bad =
      (\<lambda>out. ?E hash_map_output_collision_bad out \<or>
        ?E supported_pairwise_coupling_event out)"
    by (rule ext)
      (auto simp: staged_security_with_data_state_verifier_event_def
        supported_pairwise_side_bad_def
        split: option.splits prod.splits)
  have "wp_event ?M (?E supported_pairwise_side_bad)
      adversary_initial_state \<le>
      wp_event ?M (?E hash_map_output_collision_bad)
        adversary_initial_state +
      wp_event ?M (?E supported_pairwise_coupling_event)
        adversary_initial_state"
    unfolding event_eq by (rule wp_event_union_bound)
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

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_from_committed_prefix_partial_header_and_collision:
  fixes committed_error partial_error collision_error :: prob
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and committed_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_committed_prefix_hit A)
        adversary_initial_state \<le> committed_error"
    and partial_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        staged_security_with_data_state_query_partial_header_key_hit
        adversary_initial_state \<le> partial_error"
    and collision_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          hash_map_output_collision_bad)
        adversary_initial_state \<le> collision_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le>
      committed_error + (partial_error + collision_error)"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  have tree_bound:
    "wp_event ?M (staged_security_with_data_state_query_tree_output_hit A)
      adversary_initial_state \<le> partial_error + collision_error"
  proof -
    have "wp_event ?M
        (staged_security_with_data_state_query_tree_output_hit A)
        adversary_initial_state \<le>
        wp_event ?M staged_security_with_data_state_query_partial_header_key_hit
          adversary_initial_state +
        wp_event ?M
          (staged_security_with_data_state_verifier_event
            hash_map_output_collision_bad)
          adversary_initial_state"
      by (rule
          staged_security_with_data_state_query_tree_output_hit_bound_from_partial_header_key_hit_or_collision
          [OF wf controlled])
    also have "... \<le> partial_error + collision_error"
      by (intro add_mono partial_bound collision_bound)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_query_bad_verifier_event_bound_from_committed_prefix_hit_or_tree_output
        [OF wf controlled committed_bound tree_bound])
qed

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_from_partial_opening_fixed_query_error_cover:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and cover:
    "\<And>data attacker_state i.
      i < rounds \<Longrightarrow>
      query_header_supported_partial_opening_success_indices_at
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (staged_trace_root data)
        (staged_trace_fri_roots data)
        (staged_trace_final data)
        (staged_alphas data)
        (staged_degree data)
        (staged_composition_fri_roots data)
        (staged_composition_final data)
        i \<subseteq> B"
    and raw_bound: "query_index_raw_preimage_bound"
    and subset: "B \<subseteq> query_sample_space"
    and frac:
      "nnreal (query_raw_preimage_card_envelope (card B)) / nnreal size \<le>
        query_error_bound"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event query_bad)
      adversary_initial_state \<le>
      nnreal
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) * query_error_bound"
  by (rule checked_staged_security_with_data_state_query_bad_verifier_event_bound)
    (rule
      checked_staged_security_with_data_state_query_bad_bound_from_partial_opening_fixed_query_error_cover
      [OF wf controlled cover raw_bound subset frac])

lemma staged_transcript_query_partial_header_key_hit_iff_round_hit:
  "staged_transcript_query_partial_header_key_hit out \<longleftrightarrow>
    (\<exists>i \<in> {..<rounds}.
      staged_transcript_query_partial_header_key_hit_at i out)"
  unfolding staged_transcript_query_partial_header_key_hit_alt
    staged_transcript_query_partial_header_key_hit_at_def
  by (auto split: option.splits prod.splits)

lemma checked_staged_transcript_query_partial_header_key_hit_bound_from_rounds:
  assumes round_bound:
    "\<And>i. i < rounds \<Longrightarrow>
      wp_event (checked_staged_transcript_program A)
        (staged_transcript_query_partial_header_key_hit_at i)
        adversary_initial_state \<le> C i"
  shows
    "wp_event (checked_staged_transcript_program A)
      staged_transcript_query_partial_header_key_hit
      adversary_initial_state \<le> (\<Sum>i<rounds. C i)"
proof -
	  have event_eq:
	    "staged_transcript_query_partial_header_key_hit =
	      (\<lambda>out. \<exists>i \<in> {..<rounds}.
	        staged_transcript_query_partial_header_key_hit_at i out)"
	    by (rule ext)
	      (simp add:
	        staged_transcript_query_partial_header_key_hit_iff_round_hit)
  show ?thesis
    unfolding event_eq
    by (rule wp_event_finite_union_bound)
      (simp_all add: round_bound)
qed

lemma checked_staged_security_with_data_state_partial_header_key_hit_bound_from_dynamic_transcript:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and transcript_bound:
      "wp_event (checked_staged_transcript_program A)
        staged_transcript_query_partial_header_key_hit
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_partial_header_key_hit
      adversary_initial_state \<le> C"
  unfolding checked_staged_security_experiment_with_data_state_def
proof (rule wp_event_bind_bound_by_head_event[OF transcript_bound])
  show
    "staged_security_with_data_state_query_partial_header_key_hit None \<Longrightarrow>
      staged_transcript_query_partial_header_key_hit None"
    unfolding staged_security_with_data_state_query_partial_header_key_hit_def
      staged_transcript_query_partial_header_key_hit_def
    by simp
next
  fix data attacker_state out
  assume builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and cont:
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
    and hit:
      "staged_security_with_data_state_query_partial_header_key_hit out"
  from checked_staged_transcript_program_outcome_query_lookups
      [OF wf controlled builder]
  obtain raw_idxs query_idxs where
    len_raw: "length raw_idxs = rounds"
    and lookup_attacker:
      "\<forall>j < rounds.
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
          Some (raw_idxs ! j)"
    by blast
  from hit obtain data' attacker_state' result final_state i raw where
    out_eq:
      "out = Some (((data', attacker_state'), result), final_state)"
    and i_bound: "i < rounds"
    and lookup_final:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data')
            (staged_query_chunks data') i)) =
        Some raw"
    and raw_hit:
      "index (to_nat raw) \<in>
        query_header_supported_partial_union_good_sets
          (verifier_state_from_adversary attacker_state'
            (staged_proof_transcript data'))
          query_sampling_success_space
          (staged_trace_root data')
          (staged_trace_fri_roots data')
          (staged_trace_final data')
          (staged_alphas data')
          (staged_degree data')
          (staged_composition_fri_roots data')
          (staged_composition_final data')"
    unfolding staged_security_with_data_state_query_partial_header_key_hit_def
    by (auto split: option.splits prod.splits)
  from cont[unfolded out_eq] obtain verifier_state verifier_result where
    verifier:
      "Some (verifier_result, final_state) \<in>
        set_dist
          (execute verify_monad
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and data'_eq: "data' = data"
    and attacker_state'_eq: "attacker_state' = attacker_state"
    by (auto elim!: set_dist_bindE)
  have ext:
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data) \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  have lookup_initial:
    "fmlookup
      (HashMap
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    using lookup_attacker i_bound by simp
  have lookup_final_from_initial:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    by (rule hash_extension_lookup[OF lookup_initial ext])
  have raw_eq: "raw = raw_idxs ! i"
    using lookup_final lookup_final_from_initial data'_eq by simp
  have lookup_attacker_i:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data)
          (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    using lookup_attacker i_bound by simp
  have raw_idxs_hit:
    "index (to_nat (raw_idxs ! i)) \<in>
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
        (staged_composition_final data)"
    using raw_hit raw_eq data'_eq attacker_state'_eq by simp
  show "staged_transcript_query_partial_header_key_hit
      (Some (data, attacker_state))"
    unfolding staged_transcript_query_partial_header_key_hit_def Let_def
    using i_bound lookup_attacker_i raw_idxs_hit by auto
qed

definition checked_staged_event_soundness_bound
  :: "prob \<Rightarrow> prob \<Rightarrow> prob \<Rightarrow> prob"
  where
    "checked_staged_event_soundness_bound merkle_error composition_error
      query_error =
        merkle_error + composition_error + trace_fri_error +
        composition_fri_error + query_error"

lemma soundness_bad_event_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes comp_bound:
      "wp_event verify_monad (composition_bad s) s \<le> composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad (trace_fri_bad s) s \<le> trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad (composition_fri_bad s) s \<le> composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le> nnreal rounds * query_error_bound"
  shows "wp_event verify_monad (soundness_bad_event s) s \<le> soundness_bound"
proof -
  have "wp_event verify_monad (soundness_bad_event s) s \<le>
      wp_event verify_monad (composition_bad s) s +
      wp_event verify_monad (trace_fri_bad s) s +
      wp_event verify_monad (composition_fri_bad s) s +
      wp_event verify_monad (query_bad s) s"
    unfolding soundness_bad_event_def
    by (rule wp_event_union_bound4)
  also have "... \<le>
      composition_error_bound + trace_fri_error + composition_fri_error +
      nnreal rounds * query_error_bound"
    by (intro add_mono comp_bound trace_fri_bound comp_fri_bound query_bound)
  also have "... = soundness_bound"
    by (simp add: soundness_bound_component_accounting)
  finally show ?thesis .
qed

lemma soundness_bad_event_table_aware_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes comp_bound:
      "wp_event verify_monad (composition_bad s) s \<le> composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad (trace_fri_bad_with_tables s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad (composition_fri_bad_with_tables s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le> nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad (soundness_bad_event_table_aware s) s \<le>
      soundness_bound"
proof -
  have "wp_event verify_monad (soundness_bad_event_table_aware s) s \<le>
      wp_event verify_monad (composition_bad s) s +
      wp_event verify_monad (trace_fri_bad_with_tables s) s +
      wp_event verify_monad (composition_fri_bad_with_tables s) s +
      wp_event verify_monad (query_bad s) s"
    unfolding soundness_bad_event_table_aware_def
    by (rule wp_event_union_bound4)
  also have "... \<le>
      composition_error_bound + trace_fri_error + composition_fri_error +
      nnreal rounds * query_error_bound"
    by (intro add_mono comp_bound trace_fri_bound comp_fri_bound query_bound)
  also have "... = soundness_bound"
    by (simp add: soundness_bound_component_accounting)
  finally show ?thesis .
qed

lemma soundness_bad_event_partial_opening_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes comp_bound:
      "wp_event verify_monad (composition_bad s) s \<le> composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad (trace_fri_bad_with_partial_openings s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad
        (composition_fri_bad_with_partial_openings s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le> nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad (soundness_bad_event_partial_opening s) s \<le>
      soundness_bound"
proof -
  have "wp_event verify_monad (soundness_bad_event_partial_opening s) s \<le>
      wp_event verify_monad (composition_bad s) s +
      wp_event verify_monad (trace_fri_bad_with_partial_openings s) s +
      wp_event verify_monad
        (composition_fri_bad_with_partial_openings s) s +
      wp_event verify_monad (query_bad s) s"
    unfolding soundness_bad_event_partial_opening_def
    by (rule wp_event_union_bound4)
  also have "... \<le>
      composition_error_bound + trace_fri_error + composition_fri_error +
      nnreal rounds * query_error_bound"
    by (intro add_mono comp_bound trace_fri_bound comp_fri_bound query_bound)
  also have "... = soundness_bound"
    by (simp add: soundness_bound_component_accounting)
  finally show ?thesis .
qed

lemma soundness_bad_event_table_aware_with_merkle_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes merkle_bound:
      "wp_event verify_monad (fri_merkle_binding_bad s) s \<le>
        merkle_binding_error"
    and comp_bound:
      "wp_event verify_monad (composition_bad s) s \<le>
        composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad (trace_fri_bad_with_tables s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad (composition_fri_bad_with_tables s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_table_aware_with_merkle s) s \<le>
      soundness_bound_with_merkle"
proof -
  have table_bound:
    "wp_event verify_monad (soundness_bad_event_table_aware s) s \<le>
      soundness_bound"
    by (rule soundness_bad_event_table_aware_union_bound
        [OF comp_bound trace_fri_bound comp_fri_bound query_bound])
  have "wp_event verify_monad
        (soundness_bad_event_table_aware_with_merkle s) s \<le>
      wp_event verify_monad (fri_merkle_binding_bad s) s +
      wp_event verify_monad (soundness_bad_event_table_aware s) s"
    unfolding soundness_bad_event_table_aware_with_merkle_def
    by (rule wp_event_union_bound)
  also have "... \<le> merkle_binding_error + soundness_bound"
    by (intro add_mono merkle_bound table_bound)
  also have "... = soundness_bound_with_merkle"
    unfolding soundness_bound_with_merkle_def by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma soundness_bad_event_partial_opening_with_merkle_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes merkle_bound:
      "wp_event verify_monad (fri_merkle_binding_bad s) s \<le>
        merkle_binding_error"
    and comp_bound:
      "wp_event verify_monad (composition_bad s) s \<le>
        composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad (trace_fri_bad_with_partial_openings s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad
        (composition_fri_bad_with_partial_openings s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_partial_opening_with_merkle s) s \<le>
      soundness_bound_with_merkle"
proof -
  have partial_bound:
    "wp_event verify_monad (soundness_bad_event_partial_opening s) s \<le>
      soundness_bound"
    by (rule soundness_bad_event_partial_opening_union_bound
        [OF comp_bound trace_fri_bound comp_fri_bound query_bound])
  have "wp_event verify_monad
        (soundness_bad_event_partial_opening_with_merkle s) s \<le>
      wp_event verify_monad (fri_merkle_binding_bad s) s +
      wp_event verify_monad (soundness_bad_event_partial_opening s) s"
    unfolding soundness_bad_event_partial_opening_with_merkle_def
    by (rule wp_event_union_bound)
  also have "... \<le> merkle_binding_error + soundness_bound"
    by (intro add_mono merkle_bound partial_bound)
  also have "... = soundness_bound_with_merkle"
    unfolding soundness_bound_with_merkle_def by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma soundness_bad_event_partial_opening_with_initial_merkle_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes merkle_bound:
      "wp_event verify_monad (initial_merkle_binding_bad s) s \<le>
        merkle_binding_error"
    and comp_bound:
      "wp_event verify_monad (composition_bad s) s \<le>
        composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad (trace_fri_bad_with_partial_openings s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad
        (composition_fri_bad_with_partial_openings s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_partial_opening_with_initial_merkle s) s \<le>
      soundness_bound_with_merkle"
proof -
  have partial_bound:
    "wp_event verify_monad (soundness_bad_event_partial_opening s) s \<le>
      soundness_bound"
    by (rule soundness_bad_event_partial_opening_union_bound
        [OF comp_bound trace_fri_bound comp_fri_bound query_bound])
  have "wp_event verify_monad
        (soundness_bad_event_partial_opening_with_initial_merkle s) s \<le>
      wp_event verify_monad (initial_merkle_binding_bad s) s +
      wp_event verify_monad (soundness_bad_event_partial_opening s) s"
    unfolding soundness_bad_event_partial_opening_with_initial_merkle_def
    by (rule wp_event_union_bound)
  also have "... \<le> merkle_binding_error + soundness_bound"
    by (intro add_mono merkle_bound partial_bound)
  also have "... = soundness_bound_with_merkle"
    unfolding soundness_bound_with_merkle_def by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma soundness_bad_event_partial_opening_with_partial_merkle_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le>
        merkle_binding_error"
    and comp_bound:
      "wp_event verify_monad (composition_bad s) s \<le>
        composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad (trace_fri_bad_with_partial_openings s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad
        (composition_fri_bad_with_partial_openings s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_partial_opening_with_partial_merkle s) s \<le>
      soundness_bound_with_merkle"
proof -
  have partial_bound:
    "wp_event verify_monad (soundness_bad_event_partial_opening s) s \<le>
      soundness_bound"
    by (rule soundness_bad_event_partial_opening_union_bound
        [OF comp_bound trace_fri_bound comp_fri_bound query_bound])
  have "wp_event verify_monad
        (soundness_bad_event_partial_opening_with_partial_merkle s) s \<le>
      wp_event verify_monad (partial_merkle_inconsistency_bad s) s +
      wp_event verify_monad (soundness_bad_event_partial_opening s) s"
    unfolding soundness_bad_event_partial_opening_with_partial_merkle_def
    by (rule wp_event_union_bound)
  also have "... \<le> merkle_binding_error + soundness_bound"
    by (intro add_mono merkle_bound partial_bound)
  also have "... = soundness_bound_with_merkle"
    unfolding soundness_bound_with_merkle_def by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma soundness_bad_event_partial_candidate_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes comp_bound:
      "wp_event verify_monad
        (composition_bad_with_partial_candidates s) s \<le>
        composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_partial_candidates s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad
        (composition_fri_bad_with_partial_candidates s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_partial_candidates s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad (soundness_bad_event_partial_candidate s) s \<le>
      soundness_bound"
proof -
  have "wp_event verify_monad (soundness_bad_event_partial_candidate s) s \<le>
      wp_event verify_monad
        (composition_bad_with_partial_candidates s) s +
      wp_event verify_monad
        (trace_fri_bad_with_partial_candidates s) s +
      wp_event verify_monad
        (composition_fri_bad_with_partial_candidates s) s +
      wp_event verify_monad (query_bad_with_partial_candidates s) s"
    unfolding soundness_bad_event_partial_candidate_def
    by (rule wp_event_union_bound4)
  also have "... \<le> composition_error_bound + trace_fri_error +
      composition_fri_error + nnreal rounds * query_error_bound"
    by (intro add_mono comp_bound trace_fri_bound comp_fri_bound
        query_bound)
  also have "... = soundness_bound"
    unfolding soundness_bound_def by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma soundness_bad_event_partial_candidate_with_partial_merkle_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le>
        merkle_binding_error"
    and comp_bound:
      "wp_event verify_monad
        (composition_bad_with_partial_candidates s) s \<le>
        composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_partial_candidates s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad
        (composition_fri_bad_with_partial_candidates s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_partial_candidates s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_partial_candidate_with_partial_merkle s) s \<le>
      soundness_bound_with_merkle"
proof -
  have partial_bound:
    "wp_event verify_monad (soundness_bad_event_partial_candidate s) s \<le>
      soundness_bound"
    by (rule soundness_bad_event_partial_candidate_union_bound
        [OF comp_bound trace_fri_bound comp_fri_bound query_bound])
  have "wp_event verify_monad
        (soundness_bad_event_partial_candidate_with_partial_merkle s) s \<le>
      wp_event verify_monad (partial_merkle_inconsistency_bad s) s +
      wp_event verify_monad (soundness_bad_event_partial_candidate s) s"
    unfolding soundness_bad_event_partial_candidate_with_partial_merkle_def
    by (rule wp_event_union_bound)
  also have "... \<le> merkle_binding_error + soundness_bound"
    by (intro add_mono merkle_bound partial_bound)
  also have "... = soundness_bound_with_merkle"
    unfolding soundness_bound_with_merkle_def by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_partial_candidate_with_partial_merkle_union_bound:
  fixes merkle_error composition_error trace_fri_error'
    composition_fri_error' query_error :: prob
  assumes merkle_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          partial_merkle_inconsistency_bad)
        adversary_initial_state \<le> merkle_error"
    and comp_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_error"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> trace_fri_error'"
    and comp_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          composition_fri_bad_with_partial_candidates)
        adversary_initial_state \<le> composition_fri_error'"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_partial_candidates)
        adversary_initial_state \<le> query_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_with_partial_merkle)
      adversary_initial_state \<le>
      merkle_error + composition_error + trace_fri_error' +
      composition_fri_error' + query_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?merkle = "?E partial_merkle_inconsistency_bad"
  let ?comp = "?E composition_bad_with_partial_candidates"
  let ?trace = "?E trace_fri_bad_with_partial_candidates"
  let ?comp_fri = "?E composition_fri_bad_with_partial_candidates"
  let ?query = "?E query_bad_with_partial_candidates"
  let ?partial = "?E soundness_bad_event_partial_candidate"
  let ?with_merkle =
    "?E soundness_bad_event_partial_candidate_with_partial_merkle"
  have partial_bound:
    "wp_event ?M ?partial adversary_initial_state \<le>
      composition_error + trace_fri_error' + composition_fri_error' +
      query_error"
  proof -
    have "wp_event ?M ?partial adversary_initial_state \<le>
        wp_event ?M
          (\<lambda>out. ?comp out \<or> ?trace out \<or> ?comp_fri out \<or>
            ?query out)
          adversary_initial_state"
      by (rule wp_event_mono)
        (auto simp: staged_security_with_data_state_verifier_event_def
          soundness_bad_event_partial_candidate_def
          split: option.splits prod.splits)
    also have "... \<le>
        wp_event ?M ?comp adversary_initial_state +
        wp_event ?M ?trace adversary_initial_state +
        wp_event ?M ?comp_fri adversary_initial_state +
        wp_event ?M ?query adversary_initial_state"
      by (rule wp_event_union_bound4)
    also have "... \<le>
        composition_error + trace_fri_error' + composition_fri_error' +
        query_error"
      by (intro add_mono comp_bound trace_fri_bound comp_fri_bound
          query_bound)
    finally show ?thesis .
  qed
  have "wp_event ?M ?with_merkle adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?merkle out \<or> ?partial out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        soundness_bad_event_partial_candidate_with_partial_merkle_def
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?merkle adversary_initial_state +
      wp_event ?M ?partial adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      merkle_error +
      (composition_error + trace_fri_error' + composition_fri_error' +
        query_error)"
    by (intro add_mono merkle_bound partial_bound)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma soundness_bad_event_partial_candidate_empty_header_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes comp_bound:
      "wp_event verify_monad
        (composition_bad_with_empty_composition_header_candidates s) s \<le>
        composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_empty_composition_header_candidates s) s \<le>
        trace_fri_error"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_empty_composition_header_candidates s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_partial_candidate_empty_header s) s \<le>
      composition_error_bound + trace_fri_error +
        nnreal rounds * query_error_bound"
proof -
  have "wp_event verify_monad
        (soundness_bad_event_partial_candidate_empty_header s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          composition_bad_with_empty_composition_header_candidates s out \<or>
          trace_fri_bad_with_empty_composition_header_candidates s out \<or>
          query_bad_with_empty_composition_header_candidates s out \<or>
          False) s"
    unfolding soundness_bad_event_partial_candidate_empty_header_def
    by simp
  also have "... \<le>
      wp_event verify_monad
        (composition_bad_with_empty_composition_header_candidates s) s +
      wp_event verify_monad
        (trace_fri_bad_with_empty_composition_header_candidates s) s +
      wp_event verify_monad
        (query_bad_with_empty_composition_header_candidates s) s +
      wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_union_bound4)
  also have "... =
      wp_event verify_monad
        (composition_bad_with_empty_composition_header_candidates s) s +
      wp_event verify_monad
        (trace_fri_bad_with_empty_composition_header_candidates s) s +
      wp_event verify_monad
        (query_bad_with_empty_composition_header_candidates s) s"
    unfolding wp_event_def wp_def dist_expect_def by simp
  also have "... \<le>
      composition_error_bound + trace_fri_error +
        nnreal rounds * query_error_bound"
    by (intro add_mono comp_bound trace_fri_bound query_bound)
  finally show ?thesis .
qed

lemma composition_bad_with_empty_composition_header_candidates_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes false_statement: "\<not> exists_valid_trace"
    and degree_bound:
      "wp_event verify_monad
        (composition_degree_bad_with_empty_composition_header_candidates s) s
        \<le> degree_error"
    and randomization_bound:
      "wp_event verify_monad
        (composition_randomization_bad_with_empty_composition_header_candidates
          s) s \<le> randomization_error"
  shows
    "wp_event verify_monad
      (composition_bad_with_empty_composition_header_candidates s) s \<le>
      degree_error + randomization_error"
proof -
  have "wp_event verify_monad
        (composition_bad_with_empty_composition_header_candidates s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          composition_degree_bad_with_empty_composition_header_candidates
            s out \<or>
          composition_randomization_bad_with_empty_composition_header_candidates
            s out) s"
    by (rule wp_event_mono)
      (rule composition_bad_with_empty_composition_header_candidates_split
        [OF false_statement])
  also have "... \<le>
      wp_event verify_monad
        (composition_degree_bad_with_empty_composition_header_candidates s) s +
      wp_event verify_monad
        (composition_randomization_bad_with_empty_composition_header_candidates
          s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> degree_error + randomization_error"
    by (intro add_mono degree_bound randomization_bound)
  finally show ?thesis .
qed

lemma soundness_bad_event_partial_candidate_empty_header_split_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes false_statement: "\<not> exists_valid_trace"
    and degree_bound:
      "wp_event verify_monad
        (composition_degree_bad_with_empty_composition_header_candidates s) s
        \<le> degree_error"
    and randomization_bound:
      "wp_event verify_monad
        (composition_randomization_bad_with_empty_composition_header_candidates
          s) s \<le> randomization_error"
    and trace_fri_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_empty_composition_header_candidates s) s \<le>
        trace_fri_error"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_empty_composition_header_candidates s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_partial_candidate_empty_header s) s \<le>
      degree_error + randomization_error + trace_fri_error +
        nnreal rounds * query_error_bound"
proof -
  have "wp_event verify_monad
      (soundness_bad_event_partial_candidate_empty_header s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          composition_degree_bad_with_empty_composition_header_candidates
            s out \<or>
          composition_randomization_bad_with_empty_composition_header_candidates
            s out \<or>
          trace_fri_bad_with_empty_composition_header_candidates s out \<or>
          query_bad_with_empty_composition_header_candidates s out) s"
  proof (rule wp_event_mono)
    fix out
    assume empty:
      "soundness_bad_event_partial_candidate_empty_header s out"
    then consider
        (comp) "composition_bad_with_empty_composition_header_candidates s out"
      | (trace) "trace_fri_bad_with_empty_composition_header_candidates s out"
      | (query) "query_bad_with_empty_composition_header_candidates s out"
      unfolding soundness_bad_event_partial_candidate_empty_header_def
      by blast
    then show
      "composition_degree_bad_with_empty_composition_header_candidates
          s out \<or>
        composition_randomization_bad_with_empty_composition_header_candidates
          s out \<or>
        trace_fri_bad_with_empty_composition_header_candidates s out \<or>
        query_bad_with_empty_composition_header_candidates s out"
    proof cases
      case comp
      then show ?thesis
        using composition_bad_with_empty_composition_header_candidates_split
          [OF false_statement comp]
        by blast
    qed blast+
  qed
  also have "... \<le>
      wp_event verify_monad
        (composition_degree_bad_with_empty_composition_header_candidates s) s +
      wp_event verify_monad
        (composition_randomization_bad_with_empty_composition_header_candidates
          s) s +
      wp_event verify_monad
        (trace_fri_bad_with_empty_composition_header_candidates s) s +
      wp_event verify_monad
        (query_bad_with_empty_composition_header_candidates s) s"
    by (rule wp_event_union_bound4)
  also have "... \<le>
      degree_error + randomization_error + trace_fri_error +
        nnreal rounds * query_error_bound"
    by (intro add_mono degree_bound randomization_bound trace_fri_bound
        query_bound)
  finally show ?thesis .
qed

lemma soundness_bad_event_partial_candidate_empty_header_reduced_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes false_statement: "\<not> exists_valid_trace"
    and randomization_bound:
      "wp_event verify_monad
        (composition_randomization_bad_with_empty_composition_header_candidates
          s) s \<le> composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_empty_composition_header_candidates s) s \<le>
        trace_fri_error"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_empty_composition_header_candidates s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_partial_candidate_empty_header s) s \<le>
      composition_error_bound + trace_fri_error +
        nnreal rounds * query_error_bound"
proof -
  have split_bound:
    "wp_event verify_monad
      (soundness_bad_event_partial_candidate_empty_header s) s \<le>
      0 + composition_error_bound + trace_fri_error +
        nnreal rounds * query_error_bound"
    by (rule soundness_bad_event_partial_candidate_empty_header_split_union_bound
        [OF false_statement
          composition_degree_bad_with_empty_composition_header_candidates_bound
          randomization_bound trace_fri_bound query_bound])
  then show ?thesis by simp
qed

lemma soundness_bad_event_partial_candidate_empty_header_bound_from_alpha_hit:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes false_statement: "\<not> exists_valid_trace"
    and alpha_bound:
      "wp_event verify_monad
        (composition_alpha_bad_set_hit_with_empty_composition_header_candidates
          s) s \<le> composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_empty_composition_header_candidates s) s \<le>
        trace_fri_error"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_empty_composition_header_candidates s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_partial_candidate_empty_header s) s \<le>
      composition_error_bound + trace_fri_error +
        nnreal rounds * query_error_bound"
proof -
  have randomization_bound:
    "wp_event verify_monad
      (composition_randomization_bad_with_empty_composition_header_candidates
        s) s \<le> composition_error_bound"
  proof -
    have "wp_event verify_monad
        (composition_randomization_bad_with_empty_composition_header_candidates
          s) s \<le>
        wp_event verify_monad
          (composition_alpha_bad_set_hit_with_empty_composition_header_candidates
            s) s"
      by (rule
        wp_composition_randomization_bad_with_empty_composition_header_candidates_le_alpha_hit)
    also have "... \<le> composition_error_bound"
      by (rule alpha_bound)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule soundness_bad_event_partial_candidate_empty_header_reduced_union_bound
        [OF false_statement randomization_bound trace_fri_bound query_bound])
qed

lemma soundness_bad_event_partial_candidate_empty_header_bound_from_partial_opening_alpha_union_hit:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes false_statement: "\<not> exists_valid_trace"
    and alpha_bound:
      "wp_event verify_monad
        (composition_alpha_partial_opening_union_hit_with_empty_header s) s \<le>
        composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_empty_composition_header_candidates s) s \<le>
        trace_fri_error"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_empty_composition_header_candidates s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_partial_candidate_empty_header s) s \<le>
      composition_error_bound + trace_fri_error +
        nnreal rounds * query_error_bound"
proof -
  have alpha_hit_bound:
    "wp_event verify_monad
      (composition_alpha_bad_set_hit_with_empty_composition_header_candidates
        s) s \<le> composition_error_bound"
  proof -
    have "wp_event verify_monad
        (composition_alpha_bad_set_hit_with_empty_composition_header_candidates
          s) s \<le>
        wp_event verify_monad
          (composition_alpha_partial_opening_union_hit_with_empty_header s) s"
      by (rule
        wp_composition_alpha_bad_set_hit_with_empty_header_le_partial_opening_union_hit)
    also have "... \<le> composition_error_bound"
      by (rule alpha_bound)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule soundness_bad_event_partial_candidate_empty_header_bound_from_alpha_hit
        [OF false_statement alpha_hit_bound trace_fri_bound query_bound])
qed

lemma soundness_bad_event_partial_candidate_empty_header_bound_from_alpha_header_partial_union_hit:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes false_statement: "\<not> exists_valid_trace"
    and alpha_bound:
      "wp_event verify_monad
        (alpha_header_list_set_hit s
          (alpha_header_supported_partial_union_bad_sets s
            composition_trace_bad_alpha_space)) s \<le>
        composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_empty_composition_header_candidates s) s \<le>
        trace_fri_error"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_empty_composition_header_candidates s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_partial_candidate_empty_header s) s \<le>
      composition_error_bound + trace_fri_error +
        nnreal rounds * query_error_bound"
proof -
  have partial_alpha_bound:
    "wp_event verify_monad
      (composition_alpha_partial_opening_union_hit_with_empty_header s) s \<le>
      composition_error_bound"
  proof -
    have "wp_event verify_monad
        (composition_alpha_partial_opening_union_hit_with_empty_header s) s
        \<le>
        wp_event verify_monad
          (alpha_header_list_set_hit s
            (alpha_header_supported_partial_union_bad_sets s
              composition_trace_bad_alpha_space)) s"
      by (rule
        wp_composition_alpha_partial_opening_union_hit_with_empty_header_le_alpha_header_partial_union)
    also have "... \<le> composition_error_bound"
      by (rule alpha_bound)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule
        soundness_bad_event_partial_candidate_empty_header_bound_from_partial_opening_alpha_union_hit
        [OF false_statement partial_alpha_bound trace_fri_bound query_bound])
qed

lemma checked_staged_security_with_actual_alpha_prefix_partial_candidate_randomization_imp_partial_header_bad_set_hit_on_support:
  assumes support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad_with_partial_candidates out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      composition_trace_bad_alpha_space out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding checked_staged_security_with_actual_alpha_prefix_verifier_event_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state),
          result), final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have verifier:
    "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    using support
    unfolding out_eq
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have local_random:
    "composition_randomization_bad_with_partial_candidates ?s
      (Some (result, final_state))"
    using hit
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      Let_def
    by simp
  have local_hit:
    "composition_alpha_bad_set_hit_with_partial_candidates ?s
      (Some (result, final_state))"
    by (rule composition_randomization_bad_with_partial_candidates_imp_alpha_hit
        [OF local_random])
  have partial_header:
    "alpha_header_list_set_hit ?s
      (alpha_header_supported_partial_union_bad_sets ?s
        composition_trace_bad_alpha_space)
      (Some (result, final_state))"
    by (rule
        composition_alpha_bad_set_hit_with_partial_candidates_imp_alpha_header_partial_union_on_support
        [OF verifier local_hit])
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_def
      Let_def
    using partial_header by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_partial_candidate_randomization_le_partial_header_bad_set_hit:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_randomization_bad_with_partial_candidates)
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      composition_trace_bad_alpha_space)
    adversary_initial_state"
  by (rule wp_event_mono_on_support)
    (rule
      checked_staged_security_with_actual_alpha_prefix_partial_candidate_randomization_imp_partial_header_bad_set_hit_on_support)

lemma checked_staged_security_with_actual_alpha_prefix_partial_candidate_composition_randomization_bound_from_prefix_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad_with_partial_candidates)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  have partial_header_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_bound_from_prefix_drift_and_budgets
        [OF wf controlled prefix_bound drift_bound])
  have "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad_with_partial_candidates)
      adversary_initial_state \<le>
      wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_candidate_randomization_le_partial_header_bad_set_hit)
  also have "... \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule partial_header_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_partial_candidate_composition_randomization_bound_from_prefix_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_partial_candidates)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  have projected:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_partial_candidates)
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_randomization_bad_with_partial_candidates)
      adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection)
  show ?thesis
    unfolding projected
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_candidate_composition_randomization_bound_from_prefix_drift_and_budgets
        [OF wf controlled prefix_bound drift_bound])
qed

lemma checked_staged_security_with_data_state_partial_candidate_composition_bad_bound_from_prefix_drift_and_budgets:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_bad_with_partial_candidates)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?degree = "?E composition_degree_bad_with_partial_candidates"
  let ?random = "?E composition_randomization_bad_with_partial_candidates"
  let ?bad = "?E composition_bad_with_partial_candidates"
  have degree_false: "?degree = (\<lambda>out. False)"
    by (rule ext)
      (auto simp: staged_security_with_data_state_verifier_event_def
        composition_degree_bad_with_partial_candidates_false
        split: option.splits prod.splits)
  have degree_bound:
    "wp_event ?M ?degree adversary_initial_state \<le> 0"
    unfolding degree_false wp_event_def wp_def dist_expect_def by simp
  have random_bound:
    "wp_event ?M ?random adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_data_state_partial_candidate_composition_randomization_bound_from_prefix_drift_and_budgets
        [OF wf controlled prefix_bound drift_bound])
  have "wp_event ?M ?bad adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. ?degree out \<or> ?random out)
        adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest: composition_bad_with_partial_candidates_split
          [OF false_statement]
        split: option.splits prod.splits)
  also have "... \<le>
      wp_event ?M ?degree adversary_initial_state +
      wp_event ?M ?random adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le>
      0 + (P + D +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0))"
    by (intro add_mono degree_bound random_bound)
  finally show ?thesis
    by simp
qed

lemma checked_staged_security_with_data_state_partial_candidate_composition_bad_bound_from_drift_and_budgets:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_bad_with_partial_candidates)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  let ?P =
    "composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  have transcript_bound:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound_from_budgets
        [OF wf controlled])
  have prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  have
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_bad_with_partial_candidates)
      adversary_initial_state \<le>
      ?P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_data_state_partial_candidate_composition_bad_bound_from_prefix_drift_and_budgets
        [OF false_statement wf controlled prefix_bound drift_bound])
  then show ?thesis
    by (simp add: add.assoc)
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_partial_alpha_hit_imp_partial_header_bad_set_hit_on_support:
  assumes support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
              A)
            adversary_initial_state)"
    and hit:
      "checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header out"
  shows
    "checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      composition_trace_bad_alpha_space out"
proof (cases out)
  case None
  then show ?thesis
    using hit
    unfolding checked_staged_security_with_actual_alpha_prefix_verifier_event_def
    by simp
next
  case (Some result_pack)
  then obtain prefix prefix_state data attacker_state result final_state
    where out_eq:
      "out =
        Some (((((prefix, prefix_state), data), attacker_state),
          result), final_state)"
    by (cases result_pack, auto split: prod.splits)
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have verifier:
    "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    using support
    unfolding out_eq
      checked_staged_security_experiment_with_actual_alpha_prefix_data_state_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have local_hit:
    "composition_alpha_partial_opening_union_hit_with_empty_header ?s
      (Some (result, final_state))"
    using hit
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_verifier_event_def
      Let_def
    by simp
  have partial_header:
    "alpha_header_list_set_hit ?s
      (alpha_header_supported_partial_union_bad_sets ?s
        composition_trace_bad_alpha_space)
      (Some (result, final_state))"
    by (rule
        composition_alpha_partial_opening_union_hit_with_empty_header_imp_alpha_header_partial_union_on_support
        [OF verifier local_hit])
  show ?thesis
    unfolding out_eq
      checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_def
      Let_def
    using partial_header by simp
qed

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_partial_alpha_hit_le_partial_header_bad_set_hit:
  "wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_verifier_event
      composition_alpha_partial_opening_union_hit_with_empty_header)
    adversary_initial_state \<le>
   wp_event
    (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
    (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
      composition_trace_bad_alpha_space)
    adversary_initial_state"
  by (rule wp_event_mono_on_support)
    (rule
      checked_staged_security_with_actual_alpha_prefix_empty_header_partial_alpha_hit_imp_partial_header_bad_set_hit_on_support)

lemma checked_staged_security_with_actual_alpha_prefix_empty_header_partial_alpha_hit_bound_from_prefix_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
  shows
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  have partial_header_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit_bound_from_prefix_drift_and_budgets
        [OF wf controlled prefix_bound drift_bound])
  have "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header)
      adversary_initial_state \<le>
      wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_partial_header_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_partial_alpha_hit_le_partial_header_bad_set_hit)
  also have "... \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule partial_header_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_empty_header_partial_alpha_hit_bound_from_prefix_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  have projected:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header)
      adversary_initial_state =
     wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state A)
      (checked_staged_security_with_actual_alpha_prefix_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header)
      adversary_initial_state"
    by (rule
        checked_staged_security_with_data_state_verifier_event_actual_alpha_prefix_projection)
  show ?thesis
    unfolding projected
    by (rule
        checked_staged_security_with_actual_alpha_prefix_empty_header_partial_alpha_hit_bound_from_prefix_drift_and_budgets
        [OF wf controlled prefix_bound drift_bound])
qed

lemma checked_staged_security_with_data_state_empty_header_composition_randomization_bound_from_prefix_drift_and_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
proof -
  have alpha_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_data_state_empty_header_partial_alpha_hit_bound_from_prefix_drift_and_budgets
        [OF wf controlled prefix_bound drift_bound])
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_randomization_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_alpha_partial_opening_union_hit_with_empty_header)
      adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_alpha_bad_set_hit_with_empty_header_imp_partial_opening_union_hit
          composition_randomization_bad_with_empty_composition_header_candidates_imp_alpha_hit
        split: option.splits prod.splits)
  also have "... \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule alpha_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_empty_header_bad_event_bound_from_prefix_drift_trace_fri_and_query:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and prefix_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> P"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> empty_query_error"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header)
      adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + empty_query_error"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?E = staged_security_with_data_state_verifier_event
  let ?degree =
    "?E composition_degree_bad_with_empty_composition_header_candidates"
  let ?random =
    "?E composition_randomization_bad_with_empty_composition_header_candidates"
  let ?trace =
    "?E trace_fri_bad_with_empty_composition_header_candidates"
  let ?query =
    "?E query_bad_with_empty_composition_header_candidates"
  let ?bad = "?E soundness_bad_event_partial_candidate_empty_header"
  have degree_false: "?degree = (\<lambda>out. False)"
    by (rule ext)
      (auto simp: staged_security_with_data_state_verifier_event_def
        composition_degree_bad_with_empty_composition_header_candidates_false
        split: option.splits prod.splits)
  have degree_bound:
    "wp_event ?M ?degree adversary_initial_state \<le> 0"
    unfolding degree_false wp_event_def wp_def dist_expect_def by simp
  have random_bound:
    "wp_event ?M ?random adversary_initial_state \<le>
      P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0)"
    by (rule
        checked_staged_security_with_data_state_empty_header_composition_randomization_bound_from_prefix_drift_and_budgets
        [OF wf controlled prefix_bound drift_bound])
  have "wp_event ?M ?bad adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. ?degree out \<or> ?random out \<or> ?trace out \<or>
          ?query out)
        adversary_initial_state"
  proof (rule wp_event_mono)
    fix out
    assume bad: "?bad out"
    show "?degree out \<or> ?random out \<or> ?trace out \<or> ?query out"
    proof (cases out)
      case None
      then show ?thesis
        using bad
        unfolding staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed, auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      have local_bad:
        "soundness_bad_event_partial_candidate_empty_header ?s
          (Some (result, final_state))"
        using bad
        unfolding out_eq staged_security_with_data_state_verifier_event_def
        by simp
      then consider
          (comp)
            "composition_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state))"
        | (trace)
            "trace_fri_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state))"
        | (query)
            "query_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state))"
        unfolding soundness_bad_event_partial_candidate_empty_header_def
        by blast
      then show ?thesis
      proof cases
        case comp
        then have comp_split:
          "composition_degree_bad_with_empty_composition_header_candidates ?s
              (Some (result, final_state)) \<or>
           composition_randomization_bad_with_empty_composition_header_candidates
              ?s (Some (result, final_state))"
          by (rule
              composition_bad_with_empty_composition_header_candidates_split
              [OF false_statement])
        then show ?thesis
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          using comp_split by (auto split: option.splits prod.splits)
      next
        case trace
        then show ?thesis
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          by simp
      next
        case query
        then show ?thesis
          unfolding out_eq staged_security_with_data_state_verifier_event_def
          by simp
      qed
    qed
  qed
  also have "... \<le>
      wp_event ?M ?degree adversary_initial_state +
      wp_event ?M ?random adversary_initial_state +
      wp_event ?M ?trace adversary_initial_state +
      wp_event ?M ?query adversary_initial_state"
    by (rule wp_event_union_bound4)
  also have "... \<le>
      0 +
      (P + D +
        staged_phase_relation_error size
          (staged_alpha_search_queries budgets 0)) +
      trace_fri_error + empty_query_error"
    by (intro add_mono degree_bound random_bound trace_fri_bound query_bound)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_data_state_empty_header_bad_event_bound_from_drift_trace_fri_and_query:
  assumes false_statement: "\<not> exists_valid_trace"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and drift_bound:
      "wp_event
        (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
          A)
        (checked_staged_security_with_actual_alpha_prefix_partial_header_candidate_drift
          composition_trace_bad_alpha_space)
        adversary_initial_state \<le> D"
    and trace_fri_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          trace_fri_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> trace_fri_error"
    and query_bound:
      "wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_verifier_event
          query_bad_with_empty_composition_header_candidates)
        adversary_initial_state \<le> nnreal rounds * query_error_bound"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header)
      adversary_initial_state \<le>
      composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0) +
      D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound"
proof -
  let ?P =
    "composition_error_bound +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      hash_collision_budget_value 0
        (staged_alpha_search_queries budgets 0)"
  have transcript_bound:
    "wp_event (checked_staged_transcript_with_alpha_prefix_program A)
      (checked_staged_transcript_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_transcript_with_alpha_prefix_actual_bad_set_hit_bound_from_budgets
        [OF wf controlled])
  have prefix_bound:
    "wp_event
      (checked_staged_security_experiment_with_actual_alpha_prefix_data_state
        A)
      (checked_staged_security_with_actual_alpha_prefix_bad_set_hit
        composition_trace_bad_alpha_space)
      adversary_initial_state \<le> ?P"
    by (rule
        checked_staged_security_with_actual_alpha_prefix_bad_set_hit_bound_from_transcript
        [OF transcript_bound])
  have
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        soundness_bad_event_partial_candidate_empty_header)
      adversary_initial_state \<le>
      ?P + D +
      staged_phase_relation_error size
        (staged_alpha_search_queries budgets 0) +
      trace_fri_error + nnreal rounds * query_error_bound"
    by (rule
        checked_staged_security_with_data_state_empty_header_bad_event_bound_from_prefix_drift_trace_fri_and_query
        [OF false_statement wf controlled prefix_bound drift_bound
          trace_fri_bound query_bound])
  then show ?thesis
    by (simp add: add.assoc)
qed

lemma soundness_bad_event_table_aware_with_pairwise_side_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
    and pairwise_side_error :: prob
  assumes side_bound:
      "wp_event verify_monad (supported_pairwise_side_bad s) s \<le>
        pairwise_side_error"
    and merkle_bound:
      "wp_event verify_monad (fri_merkle_binding_bad s) s \<le>
        merkle_binding_error"
    and comp_bound:
      "wp_event verify_monad (composition_bad s) s \<le> composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad (trace_fri_bad_with_tables s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad (composition_fri_bad_with_tables s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le> nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_table_aware_with_pairwise_side s) s \<le>
      pairwise_side_error + soundness_bound_with_merkle"
proof -
  have merkle_table_bound:
    "wp_event verify_monad
      (soundness_bad_event_table_aware_with_merkle s) s \<le>
      soundness_bound_with_merkle"
    by (rule soundness_bad_event_table_aware_with_merkle_union_bound
        [OF merkle_bound comp_bound trace_fri_bound comp_fri_bound
          query_bound])
  have "wp_event verify_monad
        (soundness_bad_event_table_aware_with_pairwise_side s) s \<le>
      wp_event verify_monad (supported_pairwise_side_bad s) s +
      wp_event verify_monad
        (soundness_bad_event_table_aware_with_merkle s) s"
    unfolding soundness_bad_event_table_aware_with_pairwise_side_def
    by (rule wp_event_union_bound)
  also have "... \<le> pairwise_side_error + soundness_bound_with_merkle"
    by (intro add_mono side_bound merkle_table_bound)
  finally show ?thesis .
qed

lemma soundness_bad_event_table_aware_with_output_local_side_union_bound:
  fixes s :: "('f, 'a) protocol_channel_scheme"
    and output_local_side_error :: prob
  assumes side_bound:
      "wp_event verify_monad (supported_output_local_side_bad s) s \<le>
        output_local_side_error"
    and merkle_bound:
      "wp_event verify_monad (fri_merkle_binding_bad s) s \<le>
        merkle_binding_error"
    and comp_bound:
      "wp_event verify_monad (composition_bad s) s \<le> composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad (trace_fri_bad_with_tables s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad (composition_fri_bad_with_tables s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad
      (soundness_bad_event_table_aware_with_output_local_side s) s \<le>
      output_local_side_error + soundness_bound_with_merkle"
proof -
  have merkle_table_bound:
    "wp_event verify_monad
      (soundness_bad_event_table_aware_with_merkle s) s \<le>
      soundness_bound_with_merkle"
    by (rule soundness_bad_event_table_aware_with_merkle_union_bound
        [OF merkle_bound comp_bound trace_fri_bound comp_fri_bound
          query_bound])
  have "wp_event verify_monad
        (soundness_bad_event_table_aware_with_output_local_side s) s \<le>
      wp_event verify_monad (supported_output_local_side_bad s) s +
      wp_event verify_monad
        (soundness_bad_event_table_aware_with_merkle s) s"
    unfolding soundness_bad_event_table_aware_with_output_local_side_def
    by (rule wp_event_union_bound)
  also have "... \<le>
      output_local_side_error + soundness_bound_with_merkle"
    by (intro add_mono side_bound merkle_table_bound)
  finally show ?thesis .
qed

lemma soundness_from_bad_event_partition:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes false_statement: "\<not> exists_valid_trace"
    and partition:
      "\<And>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
        out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
        accepted out \<Longrightarrow> soundness_bad_event s out"
    and comp_bound: "wp_event verify_monad (composition_bad s) s \<le> composition_error_bound"
    and trace_fri_bound: "wp_event verify_monad (trace_fri_bad s) s \<le> trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad (composition_fri_bad s) s \<le> composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le> nnreal rounds * query_error_bound"
  shows "wp_event verify_monad accepted s \<le> soundness_bound"
proof -
  have bad_event_bound:
    "wp_event verify_monad (soundness_bad_event s) s \<le> soundness_bound"
    by (rule soundness_bad_event_union_bound
        [OF comp_bound trace_fri_bound comp_fri_bound query_bound])
  have accepted_subset:
    "\<And>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
      out \<in> set_dist (execute verify_monad s) \<Longrightarrow> accepted out \<Longrightarrow>
      soundness_bad_event s out"
  proof -
    fix out :: "(unit list \<times> ('f, 'a) protocol_channel_scheme) option"
    assume supp: "out \<in> set_dist (execute verify_monad s)"
    assume "accepted out"
    then show "soundness_bad_event s out"
      by (rule partition[OF supp])
  qed
  have "wp_event verify_monad accepted s \<le>
      wp_event verify_monad (soundness_bad_event s) s"
    by (rule wp_event_mono_on_support) (rule accepted_subset)
  also have "... \<le> soundness_bound"
    by (rule bad_event_bound)
  finally show ?thesis .
qed

lemma soundness_from_table_aware_bad_event_partition:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes false_statement: "\<not> exists_valid_trace"
    and partition:
      "\<And>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
        out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
        accepted out \<Longrightarrow>
        soundness_bad_event_table_aware_with_merkle s out"
    and merkle_bound:
      "wp_event verify_monad (fri_merkle_binding_bad s) s \<le>
        merkle_binding_error"
    and comp_bound:
      "wp_event verify_monad (composition_bad s) s \<le>
        composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad (trace_fri_bad_with_tables s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad (composition_fri_bad_with_tables s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le>
        nnreal rounds * query_error_bound"
  shows "wp_event verify_monad accepted s \<le> soundness_bound_with_merkle"
proof -
  have bad_event_bound:
    "wp_event verify_monad
      (soundness_bad_event_table_aware_with_merkle s) s \<le>
      soundness_bound_with_merkle"
    by (rule soundness_bad_event_table_aware_with_merkle_union_bound
        [OF merkle_bound comp_bound trace_fri_bound comp_fri_bound
          query_bound])
  have accepted_subset:
    "\<And>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
      out \<in> set_dist (execute verify_monad s) \<Longrightarrow> accepted out \<Longrightarrow>
      soundness_bad_event_table_aware_with_merkle s out"
  proof -
    fix out :: "(unit list \<times> ('f, 'a) protocol_channel_scheme) option"
    assume supp: "out \<in> set_dist (execute verify_monad s)"
    assume "accepted out"
    then show "soundness_bad_event_table_aware_with_merkle s out"
      by (rule partition[OF supp])
  qed
  have "wp_event verify_monad accepted s \<le>
      wp_event verify_monad
        (soundness_bad_event_table_aware_with_merkle s) s"
    by (rule wp_event_mono_on_support) (rule accepted_subset)
  also have "... \<le> soundness_bound_with_merkle"
    by (rule bad_event_bound)
  finally show ?thesis .
qed

lemma soundness_from_partial_opening_bad_event_partition:
  fixes s :: "('f, 'a) protocol_channel_scheme"
    and B :: prob
  assumes partition:
      "\<And>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
        out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
        accepted out \<Longrightarrow>
        soundness_bad_event_partial_opening_with_merkle s out"
    and bad_event_bound:
      "wp_event verify_monad
        (soundness_bad_event_partial_opening_with_merkle s) s \<le> B"
  shows "wp_event verify_monad accepted s \<le> B"
proof -
  have "wp_event verify_monad accepted s \<le>
      wp_event verify_monad
        (soundness_bad_event_partial_opening_with_merkle s) s"
    by (rule wp_event_mono_on_support) (rule partition)
  also have "... \<le> B"
    by (rule bad_event_bound)
  finally show ?thesis .
qed

lemma soundness_from_table_aware_bad_event_partition_with_pairwise_side:
  fixes s :: "('f, 'a) protocol_channel_scheme"
    and pairwise_side_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and partition:
      "\<And>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
        out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
        accepted out \<Longrightarrow>
        soundness_bad_event_table_aware_with_pairwise_side s out"
    and side_bound:
      "wp_event verify_monad (supported_pairwise_side_bad s) s \<le>
        pairwise_side_error"
    and merkle_bound:
      "wp_event verify_monad (fri_merkle_binding_bad s) s \<le>
        merkle_binding_error"
    and comp_bound:
      "wp_event verify_monad (composition_bad s) s \<le>
        composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad (trace_fri_bad_with_tables s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad (composition_fri_bad_with_tables s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad accepted s \<le>
      pairwise_side_error + soundness_bound_with_merkle"
proof -
  have bad_event_bound:
    "wp_event verify_monad
      (soundness_bad_event_table_aware_with_pairwise_side s) s \<le>
      pairwise_side_error + soundness_bound_with_merkle"
    by (rule soundness_bad_event_table_aware_with_pairwise_side_union_bound
        [OF side_bound merkle_bound comp_bound trace_fri_bound comp_fri_bound
          query_bound])
  have accepted_subset:
    "\<And>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
      out \<in> set_dist (execute verify_monad s) \<Longrightarrow> accepted out \<Longrightarrow>
      soundness_bad_event_table_aware_with_pairwise_side s out"
  proof -
    fix out :: "(unit list \<times> ('f, 'a) protocol_channel_scheme) option"
    assume supp: "out \<in> set_dist (execute verify_monad s)"
    assume "accepted out"
    then show "soundness_bad_event_table_aware_with_pairwise_side s out"
      by (rule partition[OF supp])
  qed
  have "wp_event verify_monad accepted s \<le>
      wp_event verify_monad
        (soundness_bad_event_table_aware_with_pairwise_side s) s"
    by (rule wp_event_mono_on_support) (rule accepted_subset)
  also have "... \<le> pairwise_side_error + soundness_bound_with_merkle"
    by (rule bad_event_bound)
  finally show ?thesis .
qed

lemma soundness_from_table_aware_bad_event_partition_with_output_local_side:
  fixes s :: "('f, 'a) protocol_channel_scheme"
    and output_local_side_error :: prob
  assumes false_statement: "\<not> exists_valid_trace"
    and partition:
      "\<And>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
        out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
        accepted out \<Longrightarrow>
        soundness_bad_event_table_aware_with_output_local_side s out"
    and side_bound:
      "wp_event verify_monad (supported_output_local_side_bad s) s \<le>
        output_local_side_error"
    and merkle_bound:
      "wp_event verify_monad (fri_merkle_binding_bad s) s \<le>
        merkle_binding_error"
    and comp_bound:
      "wp_event verify_monad (composition_bad s) s \<le>
        composition_error_bound"
    and trace_fri_bound:
      "wp_event verify_monad (trace_fri_bad_with_tables s) s \<le>
        trace_fri_error"
    and comp_fri_bound:
      "wp_event verify_monad (composition_fri_bad_with_tables s) s \<le>
        composition_fri_error"
    and query_bound:
      "wp_event verify_monad (query_bad s) s \<le>
        nnreal rounds * query_error_bound"
  shows
    "wp_event verify_monad accepted s \<le>
      output_local_side_error + soundness_bound_with_merkle"
proof -
  have bad_event_bound:
    "wp_event verify_monad
      (soundness_bad_event_table_aware_with_output_local_side s) s \<le>
      output_local_side_error + soundness_bound_with_merkle"
    by (rule
        soundness_bad_event_table_aware_with_output_local_side_union_bound
        [OF side_bound merkle_bound comp_bound trace_fri_bound comp_fri_bound
          query_bound])
  have "wp_event verify_monad accepted s \<le>
      wp_event verify_monad
        (soundness_bad_event_table_aware_with_output_local_side s) s"
    by (rule wp_event_mono_on_support) (rule partition)
  also have "... \<le>
      output_local_side_error + soundness_bound_with_merkle"
    by (rule bad_event_bound)
  finally show ?thesis .
qed

lemma accepted_execution_partition_obligation:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes false_statement: "\<not> exists_valid_trace"
    and bind: "initial_merkle_binding_no_bad s"
  shows
    "\<And>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
      out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
      accepted out \<Longrightarrow>
      soundness_bad_event s out"
proof -
  fix out :: "(unit list \<times> ('f, 'a) protocol_channel_scheme) option"
  assume outcome: "out \<in> set_dist (execute verify_monad s)"
    and acc: "accepted out"
  from acc obtain result final_state where out_eq: "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  have verify_out:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using outcome out_eq by simp
  from verify_monad_merkle_bound_witnesses[OF bind verify_out]
  obtain trace_table composition_table as query_idxs where bound:
    "accepted_with_bound_tables s (Some (result, final_state))
      trace_table composition_table as query_idxs"
    by blast
  have "composition_bad s (Some (result, final_state)) \<or>
      trace_fri_bad s (Some (result, final_state)) \<or>
      composition_fri_bad s (Some (result, final_state)) \<or>
      query_bad s (Some (result, final_state))"
    by (rule accepted_bound_table_partition[OF false_statement bound])
  then show "soundness_bad_event s out"
    unfolding soundness_bad_event_def using out_eq by simp
qed

lemma accepted_execution_partition_obligation_partial_opening:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes false_statement: "\<not> exists_valid_trace"
  shows
    "\<And>out :: (unit list \<times> ('f, 'a) protocol_channel_scheme) option.
      out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
      accepted out \<Longrightarrow>
      soundness_bad_event_partial_opening_with_merkle s out"
  by (rule accepted_partition_soundness_bad_event_partial_opening_with_merkle
      [OF false_statement])

end

end
