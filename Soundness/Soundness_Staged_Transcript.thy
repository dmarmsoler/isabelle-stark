(*  Title:      Stark/Soundness_Staged_Transcript.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Staged_Transcript
  imports Soundness_Staged_Query
begin

text \<open>Transcript-level staged query events and their transfer to verifier executions.\<close>

context soundness
begin

definition staged_transcript_query_partial_header_key_hit
  :: "('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "staged_transcript_query_partial_header_key_hit out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (data, attacker_state) \<Rightarrow>
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
              fmlookup (HashMap attacker_state)
                (QueryIndexChallenge i
                  (state_after_query_chunks
                    (staged_query_start_hash data)
                    (staged_query_chunks data) i)) =
                Some raw \<and>
              index (to_nat raw) \<in> B)))"

lemma staged_transcript_query_partial_header_key_hit_alt:
  "staged_transcript_query_partial_header_key_hit out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (data, attacker_state) \<Rightarrow>
        (\<exists>i raw. i < rounds \<and>
          fmlookup (HashMap attacker_state)
            (QueryIndexChallenge i
              (state_after_query_chunks
                (staged_query_start_hash data)
                (staged_query_chunks data) i)) =
            Some raw \<and>
          index (to_nat raw) \<in>
            staged_partial_query_target data attacker_state))"
  unfolding staged_transcript_query_partial_header_key_hit_def
    staged_partial_query_target_def Let_def
  by (simp split: option.splits prod.splits)

definition staged_transcript_query_partial_header_key_hit_at
  :: "nat \<Rightarrow> ('f staged_proof_data \<times> 'f protocol_channel) option \<Rightarrow>
      bool"
  where
    "staged_transcript_query_partial_header_key_hit_at i out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (data, attacker_state) \<Rightarrow>
          (\<exists>raw. i < rounds \<and>
            fmlookup (HashMap attacker_state)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
              Some raw \<and>
            index (to_nat raw) \<in>
              staged_partial_query_target data attacker_state))"

lemma checked_staged_transcript_program_query_prefix_receive_lookup_support:
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
    "raw_state \<le> attacker_state"
    "fmlookup (HashMap raw_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
proof (rule checked_staged_transcript_program_query_prefix_receive_support
    [OF wf controlled i_bound outcome])
  fix prefix prefix_state raw raw_state
  assume prefix_receive:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    and raw_ext: "raw_state \<le> attacker_state"
    and lookup:
      "fmlookup (HashMap raw_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
  show ?thesis
    by (rule that[OF prefix_receive raw_ext lookup])
qed

lemma checked_staged_security_with_data_state_accepted_shape_query_prefix_receive_index:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and support:
      "Some (((data, attacker_state), result), final_state) \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
    and shape:
      "accepted_transcript_shape
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state)) as query_idxs"
    and i_bound: "i < rounds"
  obtains prefix prefix_state raw raw_state
  where
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    "index (to_nat raw) = query_idxs ! i"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_security_experiment_with_data_state_outcomeE
      [OF support]
  have builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and verifier:
      "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
    by blast+
  from checked_staged_security_with_data_state_accepted_shape_query_keys
      [OF wf controlled support shape]
  obtain raw_idxs where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and lookup_final:
      "\<And>j. j < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
        Some (raw_idxs ! j)"
    by blast
  from checked_staged_transcript_program_query_prefix_receive_lookup_support
      [OF wf controlled i_bound builder]
  obtain prefix prefix_state raw raw_state where
    prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and raw_ext: "raw_state \<le> attacker_state"
    and lookup_raw:
      "fmlookup (HashMap raw_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    by blast
  have attacker_ext_s: "attacker_state \<le> ?s"
  proof -
    have "attacker_state \<le> attacker_state"
      unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    then show ?thesis
      by (rule hash_extends_verifier_state_from_adversary_right)
  qed
  have s_ext_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  have raw_ext_final: "raw_state \<le> final_state"
    by (rule hash_ext_trans[OF raw_ext])
      (rule hash_ext_trans[OF attacker_ext_s s_ext_final])
  have lookup_final_raw:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule hash_extension_lookup[OF lookup_raw raw_ext_final])
  have raw_eq: "raw_idxs ! i = raw"
    using lookup_final[OF i_bound] lookup_final_raw by simp
  have idx_eq: "index (to_nat raw) = query_idxs ! i"
    using query_idxs_eq len_raw i_bound raw_eq by simp
  show ?thesis
    by (rule that[OF prefix_receive idx_eq])
qed

lemma checked_staged_transcript_program_query_prefix_receive_match_support:
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
    "prefix_state \<le> attacker_state"
    "raw_state \<le> attacker_state"
    "fmlookup (HashMap raw_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
proof (rule checked_staged_transcript_program_query_prefix_receive_support
    [OF wf controlled i_bound outcome])
  fix prefix prefix_state raw raw_state
  assume prefix_receive:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    and root_eq: "sqp_trace_root prefix = staged_trace_root data"
    and trace_roots_eq:
      "sqp_trace_fri_roots prefix = staged_trace_fri_roots data"
    and trace_bs_eq:
      "sqp_trace_fri_challenges prefix =
        staged_trace_fri_challenges data"
    and trace_final_eq: "sqp_trace_final prefix = staged_trace_final data"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    and degree_eq: "sqp_degree prefix = staged_degree data"
    and comp_roots_eq:
      "sqp_composition_fri_roots prefix =
        staged_composition_fri_roots data"
    and comp_bs_eq:
      "sqp_composition_fri_challenges prefix =
        staged_composition_fri_challenges data"
    and comp_final_eq:
      "sqp_composition_final prefix = staged_composition_final data"
    and query_chunks_eq:
      "sqp_query_chunks prefix = take i (staged_query_chunks data)"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and raw_ext: "raw_state \<le> attacker_state"
    and lookup:
      "fmlookup (HashMap raw_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
  show ?thesis
    by (rule that[OF prefix_receive root_eq trace_roots_eq trace_bs_eq
          trace_final_eq alphas_eq degree_eq comp_roots_eq comp_bs_eq
          comp_final_eq query_chunks_eq prefix_ext raw_ext lookup])
qed

lemma checked_staged_transcript_query_hit_at_prefix_receive_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and hit:
      "staged_transcript_query_partial_header_key_hit_at i
        (Some (data, attacker_state))"
  shows
    "\<exists>prefix prefix_state raw raw_state.
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      checked_staged_query_prefix_fixed_transcript_target_hit
        data attacker_state
        (Some (((prefix, prefix_state), raw), raw_state))"
proof -
  from hit obtain raw_hit where
    i_bound: "i < rounds"
    and lookup_attacker:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw_hit"
    and raw_hit_target:
      "index (to_nat raw_hit) \<in> staged_partial_query_target data attacker_state"
    unfolding staged_transcript_query_partial_header_key_hit_at_def
    by auto
  from checked_staged_transcript_program_query_prefix_receive_lookup_support
      [OF wf controlled i_bound outcome]
  obtain prefix prefix_state raw raw_state where
    prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and raw_ext: "raw_state \<le> attacker_state"
    and lookup_raw:
      "fmlookup (HashMap raw_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    by (rule checked_staged_transcript_program_query_prefix_receive_lookup_support
        [OF wf controlled i_bound outcome])
  have lookup_attacker_raw:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule hash_extension_lookup[OF lookup_raw raw_ext])
  have raw_eq: "raw = raw_hit"
    using lookup_attacker lookup_attacker_raw by simp
  have fixed_hit:
    "checked_staged_query_prefix_fixed_transcript_target_hit
      data attacker_state
      (Some (((prefix, prefix_state), raw), raw_state))"
    using raw_hit_target unfolding raw_eq
      checked_staged_query_prefix_fixed_transcript_target_hit_def
      checked_staged_query_prefix_dynamic_index_hit_def
    by simp
  show ?thesis
    using prefix_receive fixed_hit by blast
qed

lemma checked_staged_transcript_query_hit_at_prefix_completion_receive_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and hit:
      "staged_transcript_query_partial_header_key_hit_at i
        (Some (data, attacker_state))"
  shows
    "\<exists>prefix prefix_state raw raw_state.
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_partial_query_target i)
        (Some (((prefix, prefix_state), raw), raw_state))"
proof -
  from hit obtain raw_hit where
    i_bound: "i < rounds"
    and lookup_attacker:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw_hit"
    and raw_hit_target:
      "index (to_nat raw_hit) \<in> staged_partial_query_target data attacker_state"
    unfolding staged_transcript_query_partial_header_key_hit_at_def
    by auto
  from checked_staged_transcript_program_query_prefix_receive_match_support
      [OF wf controlled i_bound outcome]
  obtain prefix prefix_state raw raw_state where
    prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and root_eq: "sqp_trace_root prefix = staged_trace_root data"
    and trace_roots_eq:
      "sqp_trace_fri_roots prefix = staged_trace_fri_roots data"
    and trace_bs_eq:
      "sqp_trace_fri_challenges prefix =
        staged_trace_fri_challenges data"
    and trace_final_eq:
      "sqp_trace_final prefix = staged_trace_final data"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    and degree_eq: "sqp_degree prefix = staged_degree data"
    and comp_roots_eq:
      "sqp_composition_fri_roots prefix =
        staged_composition_fri_roots data"
    and comp_bs_eq:
      "sqp_composition_fri_challenges prefix =
        staged_composition_fri_challenges data"
    and comp_final_eq:
      "sqp_composition_final prefix = staged_composition_final data"
    and query_chunks_eq:
      "sqp_query_chunks prefix = take i (staged_query_chunks data)"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and raw_ext: "raw_state \<le> attacker_state"
    and lookup_raw:
      "fmlookup (HashMap raw_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    by (rule checked_staged_transcript_program_query_prefix_receive_match_support
        [OF wf controlled i_bound outcome])
  have lookup_attacker_raw:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule hash_extension_lookup[OF lookup_raw raw_ext])
  have raw_eq: "raw = raw_hit"
    using lookup_attacker lookup_attacker_raw by simp
  have match:
    "staged_query_prefix_matches_data i prefix data"
    unfolding staged_query_prefix_matches_data_def
    using root_eq trace_roots_eq trace_bs_eq trace_final_eq alphas_eq
      degree_eq comp_roots_eq comp_bs_eq comp_final_eq query_chunks_eq
    by simp
  have prefix_target:
    "index (to_nat raw) \<in>
      staged_query_prefix_partial_query_target i prefix prefix_state"
    unfolding raw_eq
    using raw_hit_target
      staged_partial_query_target_subset_prefix_completion[OF match prefix_ext]
    by blast
  have prefix_hit:
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_partial_query_target i)
      (Some (((prefix, prefix_state), raw), raw_state))"
    using prefix_target
    unfolding checked_staged_query_prefix_dynamic_index_hit_def
    by simp
  show ?thesis
    using prefix_receive prefix_hit by blast
qed

lemma checked_staged_after_query_prefix_receive_partial_hit_imp_prefix_hit:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and head_support:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and cont_support:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive A i
              ((prefix, prefix_state), raw))
            raw_state)"
    and hit:
      "staged_transcript_query_partial_header_key_hit_at i
        (Some (data, attacker_state))"
  shows
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_partial_query_target i)
      (Some (((prefix, prefix_state), raw), raw_state))"
proof -
  have prefix_support:
    "Some ((prefix, prefix_state), prefix_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_with_state A i)
          adversary_initial_state)"
    by (rule checked_staged_query_prefix_receive_with_state_prefix_support
        [OF head_support])
  have recv:
    "Some (raw, raw_state) \<in>
      set_dist (execute receive_query_index_challenge prefix_state)"
    by (rule checked_staged_query_prefix_receive_with_state_receive_support
        [OF head_support])
  from checked_staged_query_prefix_with_state_alignment
      [OF wf controlled i_bound prefix_support]
  have prefix_counter: "PQueryCounter prefix_state = i"
    and prefix_state:
      "PState prefix_state =
        state_after_query_chunks
          (staged_query_prefix_start_hash prefix)
          (sqp_query_chunks prefix) i"
    and prefix_len: "length (sqp_query_chunks prefix) = i"
    by blast+
  from cont_support obtain chunk chunk_state record_state suffix_chunks where
    chunk_out:
      "Some (chunk, chunk_state) \<in>
        set_dist (execute (query_opening_stage A i raw) raw_state)"
    and record_out:
      "Some ((), record_state) \<in>
        set_dist (execute (record_staged_messages chunk) chunk_state)"
    and suffix_out:
      "Some (suffix_chunks, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_query_program A
              (sqp_trace_fri_roots prefix)
              (sqp_composition_fri_roots prefix)
              (Suc i) (rounds - Suc i))
            record_state)"
	    and data_eq:
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
	         staged_query_chunks =
	            sqp_query_chunks prefix @ chunk # suffix_chunks\<rparr>"
	    unfolding checked_staged_after_query_prefix_receive_def Let_def
	    by (auto elim!: set_dist_bindE simp: assert_def throw_no_outcome
	        split: if_splits)
  have match: "staged_query_prefix_matches_data i prefix data"
    unfolding staged_query_prefix_matches_data_def data_eq
    using prefix_len by simp
  have start_hash:
    "staged_query_start_hash data = staged_query_prefix_start_hash prefix"
    by (rule staged_query_start_hash_of_prefix_completion[OF match])
  have prefix_key_state:
    "PState prefix_state =
      state_after_query_chunks
        (staged_query_start_hash data) (staged_query_chunks data) i"
    using prefix_state prefix_len start_hash
    unfolding data_eq
    by (simp add: state_after_query_chunks_append_prefix)
  have receive_lookup:
    "fmlookup (HashMap raw_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    using receive_query_index_challenge_outcome[OF recv]
      prefix_counter prefix_key_state
    by simp
  have prefix_raw_ext: "prefix_state \<le> raw_state"
    by (rule receive_query_index_challenge_extends[OF recv])
  have stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled wf i_bound
    unfolding staged_adversary_controlled_def staged_budget_wellformed_def
    by simp
  have raw_chunk_ext: "raw_state \<le> chunk_state"
    using controlled_ro_program_extension[OF stage_controlled] chunk_out
    unfolding hash_extension_preserving_def
    by blast
  have record_state_eq:
    "record_state = chunk_state\<lparr>
      PState := foldl concat (PState chunk_state) chunk,
      PTranscript := PTranscript chunk_state @ chunk\<rparr>"
    by (rule record_staged_messages_outcome[OF record_out])
  have chunk_record_ext: "chunk_state \<le> record_state"
    unfolding record_state_eq less_eq_hash_ext_def less_eq_fmap_def
    by simp
  have suffix_bound:
    "Suc i + (rounds - Suc i) \<le> length (query_opening_budgets budgets)"
    using wf i_bound unfolding staged_budget_wellformed_def by simp
  have suffix_target:
    "hash_target_program {}
      (sum_list
        (take (rounds - Suc i)
          (drop (Suc i) (query_opening_budgets budgets))) +
        (rounds - Suc i))
      (checked_staged_query_program A
        (sqp_trace_fri_roots prefix)
        (sqp_composition_fri_roots prefix)
        (Suc i) (rounds - Suc i))"
    by (rule hash_target_program_checked_staged_query_program
        [OF controlled suffix_bound])
  have suffix_ext: "record_state \<le> attacker_state"
    using hash_target_program_extension[OF suffix_target] suffix_out
    unfolding hash_extension_preserving_def
    by blast
  have raw_ext: "raw_state \<le> attacker_state"
    by (rule hash_ext_trans[OF raw_chunk_ext])
      (rule hash_ext_trans[OF chunk_record_ext suffix_ext])
  have prefix_ext: "prefix_state \<le> attacker_state"
    by (rule hash_ext_trans[OF prefix_raw_ext raw_ext])
  from hit obtain raw_hit where
    lookup_attacker:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw_hit"
    and raw_hit_target:
      "index (to_nat raw_hit) \<in>
        staged_partial_query_target data attacker_state"
    unfolding staged_transcript_query_partial_header_key_hit_at_def
    by auto
  have lookup_attacker_raw:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule hash_extension_lookup[OF receive_lookup raw_ext])
  have raw_eq: "raw = raw_hit"
    using lookup_attacker lookup_attacker_raw by simp
  have prefix_target:
    "index (to_nat raw) \<in>
      staged_query_prefix_partial_query_target i prefix prefix_state"
    unfolding raw_eq
    using raw_hit_target
      staged_partial_query_target_subset_prefix_completion[OF match prefix_ext]
    by blast
  show ?thesis
    using prefix_target
    unfolding checked_staged_query_prefix_dynamic_index_hit_def
    by simp
qed

lemma checked_staged_transcript_program_query_prefix_receive_compact_support:
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
    "sqp_alphas prefix = staged_alphas data"
    "sqp_composition_fri_roots prefix =
      staged_composition_fri_roots data"
    "prefix_state \<le> attacker_state"
    "raw_state \<le> attacker_state"
    "fmlookup (HashMap raw_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
proof (rule checked_staged_transcript_program_query_prefix_receive_match_support
    [OF wf controlled i_bound outcome])
  fix prefix prefix_state raw raw_state
  assume prefix_receive:
    "Some (((prefix, prefix_state), raw), raw_state) \<in>
      set_dist
        (execute (checked_staged_query_prefix_receive_with_state A i)
          adversary_initial_state)"
    and root_eq: "sqp_trace_root prefix = staged_trace_root data"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    and comp_roots_eq:
      "sqp_composition_fri_roots prefix =
        staged_composition_fri_roots data"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and raw_ext: "raw_state \<le> attacker_state"
    and lookup:
      "fmlookup (HashMap raw_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
  show ?thesis
    by (rule that[OF prefix_receive root_eq alphas_eq comp_roots_eq
          prefix_ext raw_ext lookup])
qed

lemma checked_staged_after_query_prefix_receive_extends:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and data_out:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive A i
              ((prefix, prefix_state), raw))
            raw_state)"
  shows "raw_state \<le> attacker_state"
proof -
  from data_out obtain chunk chunk_state record_state suffix_chunks where
    chunk_out:
      "Some (chunk, chunk_state) \<in>
        set_dist (execute (query_opening_stage A i raw) raw_state)"
    and record_out:
      "Some ((), record_state) \<in>
        set_dist (execute (record_staged_messages chunk) chunk_state)"
	    and suffix_out:
	      "Some (suffix_chunks, attacker_state) \<in>
	        set_dist
	          (execute
	            (checked_staged_query_program A
	              (sqp_trace_fri_roots prefix)
	              (sqp_composition_fri_roots prefix)
	              (Suc i) (rounds - Suc i))
	            record_state)"
	    unfolding checked_staged_after_query_prefix_receive_def Let_def
	    by (auto elim!: set_dist_bindE simp: assert_def throw_no_outcome
	        split: if_splits)
  have stage_controlled:
    "controlled_ro_program (query_opening_budgets budgets ! i)
      (query_opening_stage A i raw)"
    using controlled wf i_bound
    unfolding staged_adversary_controlled_def staged_budget_wellformed_def
    by simp
	  have raw_chunk_ext: "raw_state \<le> chunk_state"
	    using controlled_ro_program_extension[OF stage_controlled] chunk_out
	    unfolding hash_extension_preserving_def
	    by blast
  have record_state_eq:
    "record_state = chunk_state\<lparr>
      PState := foldl concat (PState chunk_state) chunk,
      PTranscript := PTranscript chunk_state @ chunk\<rparr>"
    by (rule record_staged_messages_outcome[OF record_out])
  have chunk_record_ext: "chunk_state \<le> record_state"
    unfolding record_state_eq less_eq_hash_ext_def less_eq_fmap_def
    by simp
  have suffix_bound:
    "Suc i + (rounds - Suc i) \<le> length (query_opening_budgets budgets)"
    using wf i_bound unfolding staged_budget_wellformed_def by simp
  have suffix_target:
    "hash_target_program {}
      (sum_list
        (take (rounds - Suc i)
          (drop (Suc i) (query_opening_budgets budgets))) +
        (rounds - Suc i))
      (checked_staged_query_program A
        (sqp_trace_fri_roots prefix)
        (sqp_composition_fri_roots prefix)
        (Suc i) (rounds - Suc i))"
    by (rule hash_target_program_checked_staged_query_program
        [OF controlled suffix_bound])
	  have suffix_ext: "record_state \<le> attacker_state"
	    using hash_target_program_extension[OF suffix_target] suffix_out
	    unfolding hash_extension_preserving_def
	    by blast
  show ?thesis
    by (rule hash_ext_trans[OF raw_chunk_ext])
      (rule hash_ext_trans[OF chunk_record_ext suffix_ext])
qed

lemma checked_staged_after_query_prefix_receive_with_verifier_query_bad_at_imp_length_prefix_hit_or_tree_output:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and head_support:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and cont_support:
      "out \<in>
        set_dist
          (execute
            (checked_staged_after_query_prefix_receive_with_verifier A i
              ((prefix, prefix_state), raw))
            raw_state)"
    and hit:
      "staged_security_with_data_state_query_bad_hit_at i out"
  shows
    "checked_staged_query_prefix_dynamic_index_hit
      staged_query_prefix_length_committed_query_target
      (Some (((prefix, prefix_state), raw), raw_state)) \<or>
     staged_security_with_data_state_query_tree_output_hit A out"
proof (cases out)
  case None
  then show ?thesis
    using hit unfolding staged_security_with_data_state_query_bad_hit_at_def
    by simp
next
  case (Some packed)
  then obtain data attacker_state result final_state where out_eq:
    "out = Some (((data, attacker_state), result), final_state)"
    by (cases packed, auto split: prod.splits)
	  let ?s =
	    "verifier_state_from_adversary attacker_state
	      (staged_proof_transcript data)"
	  have data_out':
	    "Some (data, attacker_state) \<in>
      set_dist
        (execute
	          (checked_staged_after_query_prefix_receive A i
	            ((prefix, prefix_state), raw))
	          raw_state)"
	    by (rule
	        checked_staged_after_query_prefix_receive_with_verifier_outcome(1)
	        [OF cont_support[unfolded out_eq]])
	  have verifier:
	    "Some (result, final_state) \<in> set_dist (execute verify_monad ?s)"
	    by (rule
	        checked_staged_after_query_prefix_receive_with_verifier_outcome(2)
	        [OF cont_support[unfolded out_eq]])
  from hit[unfolded out_eq
      staged_security_with_data_state_query_bad_hit_at_def Let_def]
  have hit_at:
    "query_index_round_set_hit_at ?s query_sampling_success_space i
      (Some (result, final_state))"
    by simp
  from hit_at obtain trace_table composition_table as query_idxs where
    bound:
      "accepted_with_bound_tables ?s (Some (result, final_state))
        trace_table composition_table as query_idxs"
    and query_hit:
      "query_idxs ! i \<in>
        query_sampling_success_space trace_table composition_table as"
    unfolding query_index_round_set_hit_at_def by blast
  have transcript_decomp:
    "checked_staged_transcript_program A =
      checked_staged_query_prefix_receive_with_state A i \<bind>
        checked_staged_after_query_prefix_receive A i"
    by (rule checked_staged_transcript_program_query_prefix_receive_decomp
        [OF i_bound])
	  have builder:
	    "Some (data, attacker_state) \<in>
	      set_dist
	        (execute (checked_staged_transcript_program A)
	          adversary_initial_state)"
	    unfolding transcript_decomp
	    by (rule_tac x="((prefix, prefix_state), raw)" and t=raw_state
	        in set_dist_bindI)
	      (rule head_support, rule data_out')
  have security_decomp:
    "checked_staged_security_experiment_with_data_state A =
      checked_staged_query_prefix_receive_with_state A i \<bind>
        checked_staged_after_query_prefix_receive_with_verifier A i"
    by (rule
        checked_staged_security_experiment_with_data_state_query_prefix_receive_decomp
        [OF i_bound])
	  have support_some:
	    "Some (((data, attacker_state), result), final_state) \<in>
	      set_dist
	        (execute (checked_staged_security_experiment_with_data_state A)
	          adversary_initial_state)"
	    unfolding security_decomp out_eq[symmetric]
	    by (rule_tac x="((prefix, prefix_state), raw)" and t=raw_state
	        in set_dist_bindI)
	      (rule head_support, rule cont_support)
  have shape:
    "accepted_transcript_shape ?s (Some (result, final_state))
      as query_idxs"
    using bound
    unfolding accepted_with_bound_tables_def accepted_with_tables_def
    by simp
  from checked_staged_security_with_data_state_accepted_shape_query_keys
      [OF wf controlled support_some shape]
  obtain final_raw_idxs where
    as_eq: "as = staged_alphas data"
    and len_final_raw: "length final_raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) final_raw_idxs"
    and lookup_final:
      "\<And>j. j < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
        Some (final_raw_idxs ! j)"
    by blast
	  have prefix_support:
	    "Some ((prefix, prefix_state), prefix_state) \<in>
	      set_dist
	        (execute (checked_staged_query_prefix_with_state A i)
	          adversary_initial_state)"
	    by (rule checked_staged_query_prefix_receive_with_state_prefix_support
	        [OF head_support])
	  have recv:
	    "Some (raw, raw_state) \<in>
	      set_dist (execute receive_query_index_challenge prefix_state)"
	    by (rule checked_staged_query_prefix_receive_with_state_receive_support
	        [OF head_support])
  from checked_staged_query_prefix_with_state_alignment
      [OF wf controlled i_bound prefix_support]
  have prefix_counter: "PQueryCounter prefix_state = i"
    and prefix_state_hash:
      "PState prefix_state =
        state_after_query_chunks
          (staged_query_prefix_start_hash prefix)
          (sqp_query_chunks prefix) i"
    and prefix_len: "length (sqp_query_chunks prefix) = i"
    by blast+
  from data_out' obtain chunk chunk_state record_state suffix_chunks where
    chunk_out:
      "Some (chunk, chunk_state) \<in>
        set_dist (execute (query_opening_stage A i raw) raw_state)"
    and record_out:
      "Some ((), record_state) \<in>
        set_dist (execute (record_staged_messages chunk) chunk_state)"
    and suffix_out:
      "Some (suffix_chunks, attacker_state) \<in>
        set_dist
          (execute
            (checked_staged_query_program A
              (sqp_trace_fri_roots prefix)
              (sqp_composition_fri_roots prefix)
              (Suc i) (rounds - Suc i))
            record_state)"
    and data_eq:
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
	         staged_query_chunks =
	            sqp_query_chunks prefix @ chunk # suffix_chunks\<rparr>"
	    unfolding checked_staged_after_query_prefix_receive_def Let_def
	    by (auto elim!: set_dist_bindE simp: assert_def throw_no_outcome
	        split: if_splits)
  have match: "staged_query_prefix_matches_data i prefix data"
    unfolding staged_query_prefix_matches_data_def data_eq
    using prefix_len by simp
  have start_hash:
    "staged_query_start_hash data = staged_query_prefix_start_hash prefix"
    by (rule staged_query_start_hash_of_prefix_completion[OF match])
  have prefix_key_state:
    "PState prefix_state =
      state_after_query_chunks
        (staged_query_start_hash data) (staged_query_chunks data) i"
    using prefix_state_hash prefix_len start_hash
    unfolding data_eq
    by (simp add: state_after_query_chunks_append_prefix)
  have receive_lookup:
    "fmlookup (HashMap raw_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    using receive_query_index_challenge_outcome[OF recv]
      prefix_counter prefix_key_state
    by simp
  have raw_ext_attacker: "raw_state \<le> attacker_state"
    by (rule checked_staged_after_query_prefix_receive_extends
        [OF wf controlled i_bound data_out'])
  have attacker_ext_s: "attacker_state \<le> ?s"
  proof -
    have "attacker_state \<le> attacker_state"
      unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    then show ?thesis
      by (rule hash_extends_verifier_state_from_adversary_right)
  qed
  have s_ext_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  have raw_ext_final: "raw_state \<le> final_state"
    by (rule hash_ext_trans[OF raw_ext_attacker])
      (rule hash_ext_trans[OF attacker_ext_s s_ext_final])
  have lookup_final_raw:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule hash_extension_lookup[OF receive_lookup raw_ext_final])
  have raw_eq: "final_raw_idxs ! i = raw"
    using lookup_final[OF i_bound] lookup_final_raw by simp
  have raw_hit_actual:
    "index (to_nat raw) \<in>
      query_sampling_success_space trace_table composition_table
        (staged_alphas data)"
  proof -
    have "index (to_nat (final_raw_idxs ! i)) = query_idxs ! i"
      using query_idxs_eq len_final_raw i_bound by simp
    then show ?thesis
      using query_hit as_eq raw_eq by simp
  qed
  have prefix_ext_raw: "prefix_state \<le> raw_state"
    by (rule receive_query_index_challenge_extends[OF recv])
  have prefix_ext_final: "prefix_state \<le> final_state"
    by (rule hash_ext_trans[OF prefix_ext_raw raw_ext_final])
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
  from accepted_with_bound_tables_initial_roots_pullback_or_new_tree_output_hit
      [OF prefix_ext_final bound]
  obtain fr f_fri_roots f_final dg composition_fri_roots final rest
      trace_tree composition_tree where
    header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and trace_created:
      "created_tree trace_table trace_tree final_state"
    and trace_root: "fr = value trace_tree"
    and comp_created:
      "created_tree composition_table composition_tree final_state"
    and comp_root:
      "hd composition_fri_roots = value composition_tree"
    and split:
      "(merkle_root_binds_table fr trace_table prefix_state \<and>
        merkle_root_binds_table (hd composition_fri_roots)
          composition_table prefix_state) \<or>
       hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
    by blast
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
  have trace_len: "length trace_table = clength * scale"
    using bound unfolding accepted_with_bound_tables_def
      accepted_with_tables_def by simp
  have comp_len: "length composition_table = clength * scale"
    using bound unfolding accepted_with_bound_tables_def
      accepted_with_tables_def by simp
  from split show ?thesis
  proof
    assume binds:
      "merkle_root_binds_table fr trace_table prefix_state \<and>
       merkle_root_binds_table (hd composition_fri_roots)
        composition_table prefix_state"
    have candidate:
      "(trace_table, composition_table) \<in>
        staged_query_prefix_length_committed_table_candidates prefix
          prefix_state"
      unfolding staged_query_prefix_length_committed_table_candidates_def
      using binds comp_nonempty eqs data_eq trace_len comp_len by simp
	    have target:
	      "index (to_nat raw) \<in>
	        staged_query_prefix_length_committed_query_target prefix
	          prefix_state"
	    proof -
	      have raw_hit_prefix:
	        "index (to_nat raw) \<in>
	          query_sampling_success_space trace_table composition_table
	            (sqp_alphas prefix)"
	        using raw_hit_actual data_eq by simp
	      show ?thesis
	        by (rule staged_query_prefix_length_committed_query_targetI
	            [OF candidate raw_hit_prefix])
	    qed
    then show ?thesis
      unfolding checked_staged_query_prefix_dynamic_index_hit_def
      by simp
  next
    assume tree_hit:
      "hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
    have comp_nonempty_prefix:
      "sqp_composition_fri_roots prefix \<noteq> []"
      using comp_nonempty eqs data_eq by simp
    have trace_root_prefix:
      "sqp_trace_root prefix = value trace_tree"
      using trace_root eqs data_eq by simp
	    have comp_root_prefix:
	      "hd (sqp_composition_fri_roots prefix) = value composition_tree"
	      using comp_root eqs data_eq by simp
	    have tree_event_body:
	      "\<exists>i prefix prefix_state raw raw_state trace_table
	          composition_table as query_idxs trace_tree composition_tree.
	        i < rounds \<and>
	        Some (data, attacker_state) \<in>
	          set_dist
	            (execute (checked_staged_transcript_program A)
	              adversary_initial_state) \<and>
	        Some (result, final_state) \<in>
	          set_dist (execute verify_monad ?s) \<and>
	        accepted_with_bound_tables ?s (Some (result, final_state))
	          trace_table composition_table as query_idxs \<and>
	        fmlookup (HashMap final_state)
	          (QueryIndexChallenge i
	            (state_after_query_chunks
	              (staged_query_start_hash data)
	              (staged_query_chunks data) i)) =
	          Some raw \<and>
	        index (to_nat raw) \<in>
	          query_sampling_success_space trace_table composition_table
	            (staged_alphas data) \<and>
	        Some (((prefix, prefix_state), raw), raw_state) \<in>
	          set_dist
	            (execute
	              (checked_staged_query_prefix_receive_with_state A i)
	              adversary_initial_state) \<and>
	        sqp_composition_fri_roots prefix \<noteq> [] \<and>
	        created_tree trace_table trace_tree final_state \<and>
	        sqp_trace_root prefix = value trace_tree \<and>
	        created_tree composition_table composition_tree final_state \<and>
	        hd (sqp_composition_fri_roots prefix) =
	          value composition_tree \<and>
	        hash_map_new_output_hit
	          (set_tree trace_tree \<union> set_tree composition_tree)
	          prefix_state final_state"
	      apply (rule_tac x=i in exI)
	      apply (rule_tac x=prefix in exI)
	      apply (rule_tac x=prefix_state in exI)
	      apply (rule_tac x=raw in exI)
	      apply (rule_tac x=raw_state in exI)
	      apply (rule_tac x=trace_table in exI)
	      apply (rule_tac x=composition_table in exI)
	      apply (rule_tac x=as in exI)
	      apply (rule_tac x=query_idxs in exI)
	      apply (rule_tac x=trace_tree in exI)
	      apply (rule_tac x=composition_tree in exI)
	      using i_bound builder verifier bound lookup_final_raw raw_hit_actual
	        head_support comp_nonempty_prefix trace_created trace_root_prefix
	        comp_created comp_root_prefix tree_hit
	      by blast
	    have tree_event:
	      "staged_security_with_data_state_query_tree_output_hit A out"
	      using tree_event_body
	      unfolding out_eq
	        staged_security_with_data_state_query_tree_output_hit_def Let_def
	      by simp
	    then show ?thesis by simp
	  qed
	qed

lemma checked_staged_security_with_data_state_query_bad_hit_at_bound_by_length_prefix_and_tree:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_bad_hit_at i)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1) +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_tree_output_hit A)
        adversary_initial_state"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?Head = "checked_staged_query_prefix_receive_with_state A i"
  let ?Cont =
    "checked_staged_after_query_prefix_receive_with_verifier A i"
  let ?Prefix =
    "checked_staged_query_prefix_dynamic_index_hit
      staged_query_prefix_length_committed_query_target"
  let ?Tree = "staged_security_with_data_state_query_tree_output_hit A"
  let ?Bad = "staged_security_with_data_state_query_bad_hit_at i"
  let ?BadNoTree = "\<lambda>out. ?Bad out \<and> \<not> ?Tree out"
  have split:
    "wp_event ?M ?Bad adversary_initial_state \<le>
      wp_event ?M ?BadNoTree adversary_initial_state +
      wp_event ?M ?Tree adversary_initial_state"
  proof -
    have "wp_event ?M ?Bad adversary_initial_state \<le>
        wp_event ?M (\<lambda>out. ?BadNoTree out \<or> ?Tree out)
          adversary_initial_state"
      by (rule wp_event_mono) blast
    also have "... \<le>
        wp_event ?M ?BadNoTree adversary_initial_state +
        wp_event ?M ?Tree adversary_initial_state"
      by (rule wp_event_union_bound)
    finally show ?thesis .
  qed
	  have prefix_bound:
	    "wp_event ?Head ?Prefix adversary_initial_state \<le>
	      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
	        (staged_query_search_queries budgets i + 1)"
	    by (rule checked_staged_query_prefix_length_committed_target_hit_bound
	        [OF raw_bound wf controlled])
	      (use i_bound in simp)
  have bad_no_tree_bound:
    "wp_event ?M ?BadNoTree adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
    unfolding
      checked_staged_security_experiment_with_data_state_query_prefix_receive_decomp
        [OF i_bound]
  proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
    show "?BadNoTree None \<Longrightarrow> ?Prefix None"
      unfolding staged_security_with_data_state_query_bad_hit_at_def
        checked_staged_query_prefix_dynamic_index_hit_def
      by simp
  next
    fix x t out
    assume head:
        "Some (x, t) \<in> set_dist (execute ?Head adversary_initial_state)"
      and cont: "out \<in> set_dist (execute (?Cont x) t)"
      and bad_no_tree: "?BadNoTree out"
    show "?Prefix (Some (x, t))"
    proof (cases x)
      case x_eq: (Pair prefix_pack raw)
      then obtain prefix prefix_state where prefix_pack_eq:
        "prefix_pack = (prefix, prefix_state)"
        by (cases prefix_pack) simp
      have head':
        "Some (((prefix, prefix_state), raw), t) \<in>
          set_dist (execute ?Head adversary_initial_state)"
        using head unfolding x_eq prefix_pack_eq .
      have cont':
        "out \<in>
          set_dist
            (execute
              (checked_staged_after_query_prefix_receive_with_verifier A i
                ((prefix, prefix_state), raw))
              t)"
        using cont unfolding x_eq prefix_pack_eq .
      from checked_staged_after_query_prefix_receive_with_verifier_query_bad_at_imp_length_prefix_hit_or_tree_output
          [OF wf controlled i_bound head' cont']
      have "?Prefix (Some (((prefix, prefix_state), raw), t)) \<or>
          ?Tree out"
        using bad_no_tree by simp
      then show ?thesis
        using bad_no_tree unfolding x_eq prefix_pack_eq by simp
    qed
  qed
  have "wp_event ?M ?Bad adversary_initial_state \<le>
      (staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)) +
      wp_event ?M ?Tree adversary_initial_state"
    by (rule order_trans[OF split])
      (intro add_mono bad_no_tree_bound order_refl)
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma checked_staged_security_with_data_state_query_bad_hit_at_no_tree_bound_by_length_prefix:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_with_data_state_query_bad_hit_at i out \<and>
        \<not> staged_security_with_data_state_query_tree_output_hit A out)
      adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
proof -
  let ?Head = "checked_staged_query_prefix_receive_with_state A i"
  let ?Cont =
    "checked_staged_after_query_prefix_receive_with_verifier A i"
  let ?Prefix =
    "checked_staged_query_prefix_dynamic_index_hit
      staged_query_prefix_length_committed_query_target"
  let ?Tree = "staged_security_with_data_state_query_tree_output_hit A"
  let ?Bad = "staged_security_with_data_state_query_bad_hit_at i"
  let ?BadNoTree = "\<lambda>out. ?Bad out \<and> \<not> ?Tree out"
	  have prefix_bound:
	    "wp_event ?Head ?Prefix adversary_initial_state \<le>
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
	        (staged_query_search_queries budgets i + 1)"
	    by (rule checked_staged_query_prefix_length_committed_target_hit_bound
	        [OF raw_bound wf controlled])
	      (use i_bound in simp)
  show ?thesis
    unfolding
      checked_staged_security_experiment_with_data_state_query_prefix_receive_decomp
        [OF i_bound]
  proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
    show "?BadNoTree None \<Longrightarrow> ?Prefix None"
      unfolding staged_security_with_data_state_query_bad_hit_at_def
        checked_staged_query_prefix_dynamic_index_hit_def
      by simp
  next
    fix x t out
    assume head:
        "Some (x, t) \<in> set_dist (execute ?Head adversary_initial_state)"
      and cont: "out \<in> set_dist (execute (?Cont x) t)"
      and bad_no_tree: "?BadNoTree out"
    show "?Prefix (Some (x, t))"
    proof (cases x)
      case x_eq: (Pair prefix_pack raw)
      then obtain prefix prefix_state where prefix_pack_eq:
        "prefix_pack = (prefix, prefix_state)"
        by (cases prefix_pack) simp
      have head':
        "Some (((prefix, prefix_state), raw), t) \<in>
          set_dist (execute ?Head adversary_initial_state)"
        using head unfolding x_eq prefix_pack_eq .
      have cont':
        "out \<in>
          set_dist
            (execute
              (checked_staged_after_query_prefix_receive_with_verifier A i
                ((prefix, prefix_state), raw))
              t)"
        using cont unfolding x_eq prefix_pack_eq .
      from checked_staged_after_query_prefix_receive_with_verifier_query_bad_at_imp_length_prefix_hit_or_tree_output
          [OF wf controlled i_bound head' cont']
      have "?Prefix (Some (((prefix, prefix_state), raw), t)) \<or>
          ?Tree out"
        using bad_no_tree by simp
      then show ?thesis
        using bad_no_tree unfolding x_eq prefix_pack_eq by simp
    qed
  qed
qed

lemma checked_staged_security_with_data_state_query_bad_hit_bound_by_length_prefixes_and_tree:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound +
        hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1)) +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_tree_output_hit A)
        adversary_initial_state"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?Tree = "staged_security_with_data_state_query_tree_output_hit A"
  let ?NoTree =
    "\<lambda>i out.
      staged_security_with_data_state_query_bad_hit_at i out \<and>
      \<not> ?Tree out"
  let ?E =
    "\<lambda>i.
      staged_phase_relation_error size
        (staged_query_search_queries budgets i + 1) +
      query_error_bound +
      hash_collision_budget_value 0
        (staged_query_search_queries budgets i + 1)"
  have split:
    "wp_event ?M staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
      wp_event ?M (\<lambda>out. \<exists>i \<in> {..<rounds}. ?NoTree i out)
        adversary_initial_state +
      wp_event ?M ?Tree adversary_initial_state"
  proof -
    have "wp_event ?M staged_security_with_data_state_query_bad_hit
        adversary_initial_state \<le>
      wp_event ?M
        (\<lambda>out. (\<exists>i \<in> {..<rounds}. ?NoTree i out) \<or> ?Tree out)
        adversary_initial_state"
    proof (rule wp_event_mono)
      fix out
      assume bad: "staged_security_with_data_state_query_bad_hit out"
      from staged_security_with_data_state_query_bad_hit_imp_round_hit[OF bad]
      obtain i where i_bound: "i \<in> {..<rounds}"
        and hit: "staged_security_with_data_state_query_bad_hit_at i out"
        by blast
      show "(\<exists>i\<in>{..<rounds}. ?NoTree i out) \<or> ?Tree out"
      proof (cases "?Tree out")
        case True
        then show ?thesis by simp
      next
        case False
        then show ?thesis
          using i_bound hit by blast
      qed
    qed
    also have "... \<le>
      wp_event ?M (\<lambda>out. \<exists>i \<in> {..<rounds}. ?NoTree i out)
        adversary_initial_state +
      wp_event ?M ?Tree adversary_initial_state"
      by (rule wp_event_union_bound)
    finally show ?thesis .
  qed
	  have no_tree_bound:
	    "wp_event ?M (\<lambda>out. \<exists>i \<in> {..<rounds}. ?NoTree i out)
	      adversary_initial_state \<le> (\<Sum>i<rounds. ?E i)"
	  proof (rule wp_event_finite_union_bound)
	    show "finite {..<rounds}"
	      by simp
	  next
	    fix i
	    assume i_bound: "i \<in> {..<rounds}"
	    show "wp_event ?M (?NoTree i) adversary_initial_state \<le> ?E i"
	      by (rule
	          checked_staged_security_with_data_state_query_bad_hit_at_no_tree_bound_by_length_prefix
	          [OF raw_bound wf controlled])
	        (use i_bound in simp)
	  qed
  have "wp_event ?M staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
      (\<Sum>i<rounds. ?E i) + wp_event ?M ?Tree adversary_initial_state"
    by (rule order_trans[OF split])
      (intro add_mono no_tree_bound order_refl)
  then show ?thesis .
qed

lemma checked_staged_security_with_data_state_query_bad_hit_bound_by_length_prefixes_and_tree_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound +
        hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1)) +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_tree_output_hit A)
        adversary_initial_state"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_query_bad_hit_bound_by_length_prefixes_and_tree
        [OF raw_bound wf controlled])
qed

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_by_length_prefixes_and_tree:
  assumes raw_bound: "query_index_raw_preimage_bound"
    and wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_tree_output_hit A)
        adversary_initial_state"
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
      (\<Sum>i<rounds.
        staged_phase_relation_error size
          (staged_query_search_queries budgets i + 1) +
        query_error_bound +
        hash_collision_budget_value 0
          (staged_query_search_queries budgets i + 1)) +
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_tree_output_hit A)
        adversary_initial_state"
	    by (rule
	        checked_staged_security_with_data_state_query_bad_hit_bound_by_length_prefixes_and_tree
	        [OF raw_bound wf controlled])
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_query_bad_verifier_event_bound_by_length_prefixes_and_tree_from_budgets:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
      wp_event (checked_staged_security_experiment_with_data_state A)
        (staged_security_with_data_state_query_tree_output_hit A)
        adversary_initial_state"
proof -
  have raw_bound: "query_index_raw_preimage_bound"
    by (rule query_index_raw_preimage_bound_from_sampler_wellformed)
  show ?thesis
    by (rule
        checked_staged_security_with_data_state_query_bad_verifier_event_bound_by_length_prefixes_and_tree
        [OF raw_bound wf controlled])
qed

lemma checked_staged_transcript_query_partial_header_key_hit_at_bound_from_prefix_receive:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and i_bound: "i < rounds"
    and prefix_bound:
      "wp_event (checked_staged_query_prefix_receive_with_state A i)
        (checked_staged_query_prefix_dynamic_index_hit
          (staged_query_prefix_partial_query_target i))
        adversary_initial_state \<le> C"
  shows
    "wp_event (checked_staged_transcript_program A)
      (staged_transcript_query_partial_header_key_hit_at i)
      adversary_initial_state \<le> C"
  unfolding checked_staged_transcript_program_query_prefix_receive_decomp
    [OF i_bound]
proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
  show
    "staged_transcript_query_partial_header_key_hit_at i None \<Longrightarrow>
      checked_staged_query_prefix_dynamic_index_hit
        (staged_query_prefix_partial_query_target i) None"
    unfolding staged_transcript_query_partial_header_key_hit_at_def
      checked_staged_query_prefix_dynamic_index_hit_def
    by simp
next
  fix x t out
  assume head:
      "Some (x, t) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and cont:
      "out \<in>
        set_dist
          (execute (checked_staged_after_query_prefix_receive A i x) t)"
    and hit: "staged_transcript_query_partial_header_key_hit_at i out"
  show
    "checked_staged_query_prefix_dynamic_index_hit
      (staged_query_prefix_partial_query_target i) (Some (x, t))"
  proof (cases x)
    case x_eq: (Pair prefix_pack raw)
    then obtain prefix prefix_state where prefix_pack_eq:
      "prefix_pack = (prefix, prefix_state)"
      by (cases prefix_pack) simp
    show ?thesis
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding staged_transcript_query_partial_header_key_hit_at_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state where out_eq:
        "out = Some (data, attacker_state)"
        by (cases packed) simp
      have head':
        "Some (((prefix, prefix_state), raw), t) \<in>
          set_dist
            (execute (checked_staged_query_prefix_receive_with_state A i)
              adversary_initial_state)"
        using head unfolding x_eq prefix_pack_eq .
      have cont':
        "Some (data, attacker_state) \<in>
          set_dist
            (execute
              (checked_staged_after_query_prefix_receive A i
                ((prefix, prefix_state), raw))
              t)"
        using cont unfolding x_eq prefix_pack_eq out_eq .
      have hit':
        "staged_transcript_query_partial_header_key_hit_at i
          (Some (data, attacker_state))"
        using hit unfolding out_eq .
      have prefix_hit:
        "checked_staged_query_prefix_dynamic_index_hit
          (staged_query_prefix_partial_query_target i)
          (Some (((prefix, prefix_state), raw), t))"
        by (rule
            checked_staged_after_query_prefix_receive_partial_hit_imp_prefix_hit
            [OF wf controlled i_bound head' cont' hit'])
      show ?thesis
        using prefix_hit unfolding x_eq prefix_pack_eq .
    qed
  qed
qed

lemma checked_staged_transcript_query_bound_table_hit_at_committed_prefix_receive_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and i_bound: "i < rounds"
    and lookup_attacker:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw_hit"
    and raw_hit_target:
      "index (to_nat raw_hit) \<in>
        query_sampling_success_space trace_table composition_table
          (staged_alphas data)"
    and comp_nonempty:
      "staged_composition_fri_roots data \<noteq> []"
  shows
    "\<exists>prefix prefix_state raw raw_state.
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      (merkle_root_binds_table (sqp_trace_root prefix) trace_table
          prefix_state \<longrightarrow>
       merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
          composition_table prefix_state \<longrightarrow>
       checked_staged_query_prefix_dynamic_index_hit
        (\<lambda>prefix prefix_state.
          staged_query_prefix_committed_query_target prefix prefix_state)
        (Some (((prefix, prefix_state), raw), raw_state)))"
proof -
  from checked_staged_transcript_program_query_prefix_receive_compact_support
      [OF wf controlled i_bound outcome]
  obtain prefix prefix_state raw raw_state where
    prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and root_eq: "sqp_trace_root prefix = staged_trace_root data"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    and comp_roots_eq:
      "sqp_composition_fri_roots prefix =
        staged_composition_fri_roots data"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and raw_ext: "raw_state \<le> attacker_state"
    and lookup_raw:
      "fmlookup (HashMap raw_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    by (rule checked_staged_transcript_program_query_prefix_receive_compact_support
        [OF wf controlled i_bound outcome])
  have lookup_attacker_raw:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule hash_extension_lookup[OF lookup_raw raw_ext])
  have raw_eq: "raw = raw_hit"
    using lookup_attacker lookup_attacker_raw by simp
  have comp_nonempty_prefix:
    "sqp_composition_fri_roots prefix \<noteq> []"
    using comp_nonempty comp_roots_eq by simp
  have hit_if_bound:
    "merkle_root_binds_table (sqp_trace_root prefix) trace_table
        prefix_state \<Longrightarrow>
     merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
        composition_table prefix_state \<Longrightarrow>
     checked_staged_query_prefix_dynamic_index_hit
      (\<lambda>prefix prefix_state.
        staged_query_prefix_committed_query_target prefix prefix_state)
      (Some (((prefix, prefix_state), raw), raw_state))"
  proof -
    assume trace_bind:
      "merkle_root_binds_table (sqp_trace_root prefix) trace_table
        prefix_state"
    assume comp_bind:
      "merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
        composition_table prefix_state"
    have candidate:
      "(trace_table, composition_table) \<in>
        query_header_committed_table_candidates prefix_state
          (sqp_trace_root prefix)
          (sqp_composition_fri_roots prefix)"
      unfolding query_header_committed_table_candidates_def
      using trace_bind comp_nonempty_prefix comp_bind by simp
    have raw_target_prefix:
      "index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (sqp_alphas prefix)"
      using raw_hit_target unfolding raw_eq alphas_eq .
	    have target:
	      "index (to_nat raw) \<in>
	        staged_query_prefix_committed_query_target prefix prefix_state"
	      by (rule staged_query_prefix_committed_query_targetI
	          [OF candidate raw_target_prefix])
    show ?thesis
      unfolding checked_staged_query_prefix_dynamic_index_hit_def
      using target by simp
  qed
	  show ?thesis
	    using prefix_receive hit_if_bound by blast
qed

lemma checked_staged_transcript_query_bound_table_hit_at_length_committed_prefix_receive_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and outcome:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and i_bound: "i < rounds"
    and lookup_attacker:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw_hit"
    and raw_hit_target:
      "index (to_nat raw_hit) \<in>
        query_sampling_success_space trace_table composition_table
          (staged_alphas data)"
    and comp_nonempty:
      "staged_composition_fri_roots data \<noteq> []"
    and trace_len: "length trace_table = clength * scale"
    and comp_len: "length composition_table = clength * scale"
  shows
    "\<exists>prefix prefix_state raw raw_state.
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      (merkle_root_binds_table (sqp_trace_root prefix) trace_table
          prefix_state \<longrightarrow>
       merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
          composition_table prefix_state \<longrightarrow>
       checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_length_committed_query_target
        (Some (((prefix, prefix_state), raw), raw_state)))"
proof -
  from checked_staged_transcript_program_query_prefix_receive_compact_support
      [OF wf controlled i_bound outcome]
  obtain prefix prefix_state raw raw_state where
    prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and root_eq: "sqp_trace_root prefix = staged_trace_root data"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    and comp_roots_eq:
      "sqp_composition_fri_roots prefix =
        staged_composition_fri_roots data"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and raw_ext: "raw_state \<le> attacker_state"
    and lookup_raw:
      "fmlookup (HashMap raw_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    by (rule checked_staged_transcript_program_query_prefix_receive_compact_support
        [OF wf controlled i_bound outcome])
  have lookup_attacker_raw:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule hash_extension_lookup[OF lookup_raw raw_ext])
  have raw_eq: "raw = raw_hit"
    using lookup_attacker lookup_attacker_raw by simp
  have comp_nonempty_prefix:
    "sqp_composition_fri_roots prefix \<noteq> []"
    using comp_nonempty comp_roots_eq by simp
  have hit_if_bound:
    "merkle_root_binds_table (sqp_trace_root prefix) trace_table
        prefix_state \<Longrightarrow>
     merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
        composition_table prefix_state \<Longrightarrow>
     checked_staged_query_prefix_dynamic_index_hit
      staged_query_prefix_length_committed_query_target
      (Some (((prefix, prefix_state), raw), raw_state))"
  proof -
    assume trace_bind:
      "merkle_root_binds_table (sqp_trace_root prefix) trace_table
        prefix_state"
    assume comp_bind:
      "merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
        composition_table prefix_state"
    have candidate:
      "(trace_table, composition_table) \<in>
        staged_query_prefix_length_committed_table_candidates prefix
          prefix_state"
      unfolding staged_query_prefix_length_committed_table_candidates_def
      using trace_bind comp_nonempty_prefix comp_bind trace_len comp_len
      by simp
    have raw_target_prefix:
      "index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (sqp_alphas prefix)"
      using raw_hit_target unfolding raw_eq alphas_eq .
	    have target:
	      "index (to_nat raw) \<in>
	        staged_query_prefix_length_committed_query_target prefix
	          prefix_state"
	      by (rule staged_query_prefix_length_committed_query_targetI
	          [OF candidate raw_target_prefix])
    show ?thesis
      unfolding checked_staged_query_prefix_dynamic_index_hit_def
      using target by simp
  qed
	  show ?thesis
	    using prefix_receive hit_if_bound by blast
qed

lemma checked_staged_bound_tables_initial_roots_late_output_at_query_prefix_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
    and i_bound: "i < rounds"
    and bound:
      "accepted_with_bound_tables
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state))
        trace_table composition_table as query_idxs"
  shows
    "\<exists>prefix prefix_state raw raw_state.
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      sqp_composition_fri_roots prefix \<noteq> [] \<and>
      merkle_root_binds_table (sqp_trace_root prefix) trace_table
        final_state \<and>
      merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
        composition_table final_state \<and>
      (((\<exists>input.
          fmlookup (HashMap prefix_state) input =
            Some (sqp_trace_root prefix)) \<and>
        (\<exists>input.
          fmlookup (HashMap prefix_state) input =
            Some (hd (sqp_composition_fri_roots prefix)))) \<or>
       hash_map_new_output_hit
        {sqp_trace_root prefix, hd (sqp_composition_fri_roots prefix)}
        prefix_state final_state)"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_transcript_program_query_prefix_receive_compact_support
      [OF wf controlled i_bound outcome]
  obtain prefix prefix_state raw raw_state where
    prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and root_eq: "sqp_trace_root prefix = staged_trace_root data"
    and comp_roots_eq:
      "sqp_composition_fri_roots prefix =
        staged_composition_fri_roots data"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and raw_ext: "raw_state \<le> attacker_state"
    and lookup_raw:
      "fmlookup (HashMap raw_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    by (rule checked_staged_transcript_program_query_prefix_receive_compact_support
        [OF wf controlled i_bound outcome])
  have prefix_ext_s: "prefix_state \<le> ?s"
    by (rule hash_extends_verifier_state_from_adversary_right
        [OF prefix_ext])
  have s_ext_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  have prefix_ext_final: "prefix_state \<le> final_state"
    by (rule hash_ext_trans[OF prefix_ext_s s_ext_final])
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
        [OF wf controlled outcome])
  from accepted_with_bound_tables_initial_roots_late_output_preexisting_or_union_hit
      [OF prefix_ext_final bound]
  obtain fr f_fri_roots f_final dg composition_fri_roots final rest where
    header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and trace_bind:
      "merkle_root_binds_table fr trace_table final_state"
    and comp_bind:
      "merkle_root_binds_table (hd composition_fri_roots) composition_table
        final_state"
    and late:
      "((\<exists>input. fmlookup (HashMap prefix_state) input = Some fr) \<and>
        (\<exists>input.
          fmlookup (HashMap prefix_state) input =
            Some (hd composition_fri_roots))) \<or>
       hash_map_new_output_hit {fr, hd composition_fri_roots}
        prefix_state final_state"
    by blast
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
  have comp_nonempty_prefix: "sqp_composition_fri_roots prefix \<noteq> []"
    using comp_nonempty comp_roots_eq eqs by simp
  have trace_bind_prefix:
    "merkle_root_binds_table (sqp_trace_root prefix) trace_table
      final_state"
    using trace_bind root_eq eqs by simp
  have comp_bind_prefix:
    "merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
      composition_table final_state"
    using comp_bind comp_roots_eq eqs by simp
	  have late_prefix:
	    "((\<exists>input.
	        fmlookup (HashMap prefix_state) input =
	          Some (sqp_trace_root prefix)) \<and>
      (\<exists>input.
        fmlookup (HashMap prefix_state) input =
          Some (hd (sqp_composition_fri_roots prefix)))) \<or>
     hash_map_new_output_hit
      {sqp_trace_root prefix, hd (sqp_composition_fri_roots prefix)}
	      prefix_state final_state"
	    using late root_eq comp_roots_eq eqs by simp
	  show ?thesis
	    apply (rule_tac x=prefix in exI)
	    apply (rule_tac x=prefix_state in exI)
	    apply (rule_tac x=raw in exI)
	    apply (rule_tac x=raw_state in exI)
	    using prefix_receive comp_nonempty_prefix trace_bind_prefix
	      comp_bind_prefix late_prefix
	    by blast
qed

lemma checked_staged_bound_tables_initial_roots_pullback_at_query_prefix_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
    and i_bound: "i < rounds"
	    and bound:
	      "accepted_with_bound_tables
	        (verifier_state_from_adversary attacker_state
	          (staged_proof_transcript data))
	        (Some (result, final_state))
	        trace_table composition_table as query_idxs"
	    and query_hit:
	      "query_idxs ! i \<in>
	        query_sampling_success_space trace_table composition_table as"
	  shows
	    "\<exists>prefix prefix_state raw raw_state trace_tree composition_tree.
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      sqp_alphas prefix = staged_alphas data \<and>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw \<and>
      index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (staged_alphas data) \<and>
      sqp_composition_fri_roots prefix \<noteq> [] \<and>
      created_tree trace_table trace_tree final_state \<and>
      sqp_trace_root prefix = value trace_tree \<and>
      created_tree composition_table composition_tree final_state \<and>
      hd (sqp_composition_fri_roots prefix) = value composition_tree \<and>
      ((merkle_root_binds_table (sqp_trace_root prefix) trace_table
          prefix_state \<and>
        merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
          composition_table prefix_state) \<or>
       hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state)"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_transcript_program_query_prefix_receive_compact_support
      [OF wf controlled i_bound outcome]
  obtain prefix prefix_state raw raw_state where
    prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and root_eq: "sqp_trace_root prefix = staged_trace_root data"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    and comp_roots_eq:
      "sqp_composition_fri_roots prefix =
        staged_composition_fri_roots data"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and raw_ext: "raw_state \<le> attacker_state"
    and lookup_raw:
      "fmlookup (HashMap raw_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    by (rule checked_staged_transcript_program_query_prefix_receive_compact_support
        [OF wf controlled i_bound outcome])
  have prefix_ext_s: "prefix_state \<le> ?s"
    by (rule hash_extends_verifier_state_from_adversary_right
        [OF prefix_ext])
  have s_ext_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
	  have prefix_ext_final: "prefix_state \<le> final_state"
	    by (rule hash_ext_trans[OF prefix_ext_s s_ext_final])
	  have raw_ext_s: "raw_state \<le> ?s"
	    by (rule hash_extends_verifier_state_from_adversary_right
	        [OF raw_ext])
	  have raw_ext_final: "raw_state \<le> final_state"
	    by (rule hash_ext_trans[OF raw_ext_s s_ext_final])
	  have lookup_final_raw:
	    "fmlookup (HashMap final_state)
	      (QueryIndexChallenge i
	        (state_after_query_chunks
	          (staged_query_start_hash data) (staged_query_chunks data) i)) =
	      Some raw"
	    by (rule hash_extension_lookup[OF lookup_raw raw_ext_final])
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
        [OF wf controlled outcome])
  from accepted_with_bound_tables_initial_roots_pullback_or_new_tree_output_hit
      [OF prefix_ext_final bound]
  obtain fr f_fri_roots f_final dg composition_fri_roots final rest
      trace_tree composition_tree where
    header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and trace_created:
      "created_tree trace_table trace_tree final_state"
    and trace_root: "fr = value trace_tree"
    and comp_created:
      "created_tree composition_table composition_tree final_state"
    and comp_root:
      "hd composition_fri_roots = value composition_tree"
    and split:
      "(merkle_root_binds_table fr trace_table prefix_state \<and>
        merkle_root_binds_table (hd composition_fri_roots)
          composition_table prefix_state) \<or>
       hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
    by blast
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
	  have support_some:
	    "Some (((data, attacker_state), result), final_state) \<in>
	      set_dist
	        (execute
	          (checked_staged_security_experiment_with_data_state A)
	          adversary_initial_state)"
	    by (rule checked_staged_security_experiment_with_data_state_outcomeI
	        [OF outcome verifier])
	  have shape:
	    "accepted_transcript_shape ?s (Some (result, final_state))
	      as query_idxs"
	    using bound
	    unfolding accepted_with_bound_tables_def accepted_with_tables_def
	    by simp
	  from checked_staged_security_with_data_state_accepted_shape_query_keys
	      [OF wf controlled support_some shape]
	  obtain final_raw_idxs where
	    as_eq: "as = staged_alphas data"
	    and len_final_raw: "length final_raw_idxs = rounds"
	    and query_idxs_eq:
	      "query_idxs = map (\<lambda>raw. index (to_nat raw)) final_raw_idxs"
	    and lookup_final:
	      "\<And>j. j < rounds \<Longrightarrow>
	        fmlookup (HashMap final_state)
	          (QueryIndexChallenge j
	            (state_after_query_chunks
	              (staged_query_start_hash data)
	              (staged_query_chunks data) j)) =
	        Some (final_raw_idxs ! j)"
	    by blast
	  have raw_eq: "final_raw_idxs ! i = raw"
	    using lookup_final[OF i_bound] lookup_final_raw by simp
	  have raw_hit:
	    "index (to_nat raw) \<in>
	      query_sampling_success_space trace_table composition_table
	        (staged_alphas data)"
	  proof -
	    have "index (to_nat (final_raw_idxs ! i)) = query_idxs ! i"
	      using query_idxs_eq len_final_raw i_bound by simp
	    then show ?thesis
	      using query_hit as_eq raw_eq by simp
	  qed
	  have comp_nonempty_prefix: "sqp_composition_fri_roots prefix \<noteq> []"
	    using comp_nonempty comp_roots_eq eqs by simp
  have trace_root_prefix:
    "sqp_trace_root prefix = value trace_tree"
    using root_eq trace_root eqs by simp
  have comp_root_prefix:
    "hd (sqp_composition_fri_roots prefix) = value composition_tree"
    using comp_root comp_roots_eq eqs by simp
	  have split_prefix:
	    "((merkle_root_binds_table (sqp_trace_root prefix) trace_table
	        prefix_state \<and>
      merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
        composition_table prefix_state) \<or>
     hash_map_new_output_hit
      (set_tree trace_tree \<union> set_tree composition_tree)
	      prefix_state final_state)"
	    using split root_eq comp_roots_eq eqs by simp
	  show ?thesis
	    apply (rule_tac x=prefix in exI)
	    apply (rule_tac x=prefix_state in exI)
	    apply (rule_tac x=raw in exI)
	    apply (rule_tac x=raw_state in exI)
	    apply (rule_tac x=trace_tree in exI)
	    apply (rule_tac x=composition_tree in exI)
	    using prefix_receive alphas_eq lookup_final_raw raw_hit
	      comp_nonempty_prefix trace_created trace_root_prefix comp_created
	      comp_root_prefix split_prefix
	    by blast
qed

lemma checked_staged_transcript_query_bound_table_hit_or_tree_output_at_length_committed_prefix_receive_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
    and i_bound: "i < rounds"
	    and bound:
	      "accepted_with_bound_tables
	        (verifier_state_from_adversary attacker_state
	          (staged_proof_transcript data))
	        (Some (result, final_state))
	        trace_table composition_table as query_idxs"
	    and query_hit:
	      "query_idxs ! i \<in>
	        query_sampling_success_space trace_table composition_table as"
	  shows
	    "\<exists>prefix prefix_state raw raw_state trace_tree composition_tree.
      Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state) \<and>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw \<and>
      index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (staged_alphas data) \<and>
      sqp_composition_fri_roots prefix \<noteq> [] \<and>
      created_tree trace_table trace_tree final_state \<and>
      sqp_trace_root prefix = value trace_tree \<and>
      created_tree composition_table composition_tree final_state \<and>
      hd (sqp_composition_fri_roots prefix) = value composition_tree \<and>
      (checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_length_committed_query_target
        (Some (((prefix, prefix_state), raw), raw_state)) \<or>
       hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state)"
proof -
	  from checked_staged_bound_tables_initial_roots_pullback_at_query_prefix_support
	      [OF wf controlled outcome verifier i_bound bound query_hit]
	  obtain prefix prefix_state raw raw_state trace_tree composition_tree where
    prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    and lookup_final:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    and raw_hit:
      "index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (staged_alphas data)"
    and comp_nonempty: "sqp_composition_fri_roots prefix \<noteq> []"
    and trace_created: "created_tree trace_table trace_tree final_state"
    and trace_root: "sqp_trace_root prefix = value trace_tree"
    and comp_created:
      "created_tree composition_table composition_tree final_state"
    and comp_root:
      "hd (sqp_composition_fri_roots prefix) = value composition_tree"
    and split:
      "(merkle_root_binds_table (sqp_trace_root prefix) trace_table
          prefix_state \<and>
        merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
          composition_table prefix_state) \<or>
       hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
    by blast
  have trace_len: "length trace_table = clength * scale"
    using bound unfolding accepted_with_bound_tables_def
      accepted_with_tables_def by simp
  have comp_len: "length composition_table = clength * scale"
    using bound unfolding accepted_with_bound_tables_def
      accepted_with_tables_def by simp
  have prefix_or_tree:
    "checked_staged_query_prefix_dynamic_index_hit
      staged_query_prefix_length_committed_query_target
      (Some (((prefix, prefix_state), raw), raw_state)) \<or>
     hash_map_new_output_hit
      (set_tree trace_tree \<union> set_tree composition_tree)
      prefix_state final_state"
  proof -
    from split show ?thesis
    proof
      assume binds:
        "merkle_root_binds_table (sqp_trace_root prefix) trace_table
          prefix_state \<and>
        merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
          composition_table prefix_state"
      then have candidate:
        "(trace_table, composition_table) \<in>
          staged_query_prefix_length_committed_table_candidates prefix
            prefix_state"
        unfolding staged_query_prefix_length_committed_table_candidates_def
        using comp_nonempty trace_len comp_len by simp
	      have target:
	        "index (to_nat raw) \<in>
	          staged_query_prefix_length_committed_query_target prefix
	            prefix_state"
	      proof -
	        have raw_hit_prefix:
	          "index (to_nat raw) \<in>
	            query_sampling_success_space trace_table composition_table
	              (sqp_alphas prefix)"
	          using raw_hit alphas_eq by simp
	        show ?thesis
	          by (rule staged_query_prefix_length_committed_query_targetI
	              [OF candidate raw_hit_prefix])
	      qed
      then show ?thesis
        unfolding checked_staged_query_prefix_dynamic_index_hit_def
        by simp
    next
      assume
        "hash_map_new_output_hit
          (set_tree trace_tree \<union> set_tree composition_tree)
          prefix_state final_state"
      then show ?thesis by simp
    qed
	  qed
	  show ?thesis
	    apply (rule_tac x=prefix in exI)
	    apply (rule_tac x=prefix_state in exI)
	    apply (rule_tac x=raw in exI)
	    apply (rule_tac x=raw_state in exI)
	    apply (rule_tac x=trace_tree in exI)
	    apply (rule_tac x=composition_tree in exI)
	    using prefix_receive lookup_final raw_hit comp_nonempty trace_created
	      trace_root comp_created comp_root prefix_or_tree
	    by blast
qed

lemma checked_staged_transcript_query_bound_table_hit_or_tree_output_at_committed_prefix_receive_support:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
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
    and i_bound: "i < rounds"
    and lookup_attacker:
      "fmlookup (HashMap attacker_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw_hit"
    and raw_hit_target:
      "index (to_nat raw_hit) \<in>
        query_sampling_success_space trace_table composition_table
          (staged_alphas data)"
    and bound:
      "accepted_with_bound_tables
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))
        (Some (result, final_state))
        trace_table composition_table as query_idxs"
	  shows
	    "\<exists>prefix prefix_state raw raw_state trace_tree composition_tree.
	      Some (((prefix, prefix_state), raw), raw_state) \<in>
	        set_dist
	          (execute (checked_staged_query_prefix_receive_with_state A i)
	            adversary_initial_state) \<and>
	      fmlookup (HashMap final_state)
	        (QueryIndexChallenge i
	          (state_after_query_chunks
	            (staged_query_start_hash data) (staged_query_chunks data) i)) =
	        Some raw \<and>
	      index (to_nat raw) \<in>
	        query_sampling_success_space trace_table composition_table
	          (staged_alphas data) \<and>
	      sqp_composition_fri_roots prefix \<noteq> [] \<and>
	      created_tree trace_table trace_tree final_state \<and>
	      sqp_trace_root prefix = value trace_tree \<and>
      created_tree composition_table composition_tree final_state \<and>
      hd (sqp_composition_fri_roots prefix) = value composition_tree \<and>
      (checked_staged_query_prefix_dynamic_index_hit
        (\<lambda>prefix prefix_state.
          staged_query_prefix_committed_query_target prefix prefix_state)
        (Some (((prefix, prefix_state), raw), raw_state)) \<or>
       hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state)"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from checked_staged_transcript_program_query_prefix_receive_compact_support
      [OF wf controlled i_bound outcome]
  obtain prefix prefix_state raw raw_state where
    prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and root_eq: "sqp_trace_root prefix = staged_trace_root data"
    and alphas_eq: "sqp_alphas prefix = staged_alphas data"
    and comp_roots_eq:
      "sqp_composition_fri_roots prefix =
        staged_composition_fri_roots data"
    and prefix_ext: "prefix_state \<le> attacker_state"
    and raw_ext: "raw_state \<le> attacker_state"
    and lookup_raw:
      "fmlookup (HashMap raw_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    by (rule checked_staged_transcript_program_query_prefix_receive_compact_support
        [OF wf controlled i_bound outcome])
  have lookup_attacker_raw:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule hash_extension_lookup[OF lookup_raw raw_ext])
  have raw_eq: "raw = raw_hit"
    using lookup_attacker lookup_attacker_raw by simp
  have prefix_ext_s: "prefix_state \<le> ?s"
    by (rule hash_extends_verifier_state_from_adversary_right
        [OF prefix_ext])
  have s_ext_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  have prefix_ext_final: "prefix_state \<le> final_state"
    by (rule hash_ext_trans[OF prefix_ext_s s_ext_final])
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
        [OF wf controlled outcome])
  from accepted_with_bound_tables_initial_roots_pullback_or_new_tree_output_hit
      [OF prefix_ext_final bound]
  obtain fr f_fri_roots f_final dg composition_fri_roots final rest
      trace_tree composition_tree where
    header:
      "verifier_header_transcript ?s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and comp_nonempty: "composition_fri_roots \<noteq> []"
    and trace_created:
      "created_tree trace_table trace_tree final_state"
    and trace_root: "fr = value trace_tree"
    and comp_created:
      "created_tree composition_table composition_tree final_state"
    and comp_root:
      "hd composition_fri_roots = value composition_tree"
    and split:
      "(merkle_root_binds_table fr trace_table prefix_state \<and>
        merkle_root_binds_table (hd composition_fri_roots)
          composition_table prefix_state) \<or>
       hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
    by blast
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
  have split_prefix:
    "(merkle_root_binds_table (sqp_trace_root prefix) trace_table
        prefix_state \<and>
      merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
        composition_table prefix_state) \<or>
     hash_map_new_output_hit
      (set_tree trace_tree \<union> set_tree composition_tree)
      prefix_state final_state"
    using split root_eq comp_roots_eq eqs by simp
  have comp_nonempty_prefix:
    "sqp_composition_fri_roots prefix \<noteq> []"
    using comp_nonempty comp_roots_eq eqs by simp
  have raw_hit_actual:
    "index (to_nat raw) \<in>
      query_sampling_success_space trace_table composition_table
        (staged_alphas data)"
    using raw_hit_target unfolding raw_eq .
  have lookup_initial_raw:
    "fmlookup (HashMap ?s)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    using lookup_attacker_raw by simp
  have lookup_final_raw:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some raw"
    by (rule hash_extension_lookup[OF lookup_initial_raw s_ext_final])
  have trace_root_prefix:
    "sqp_trace_root prefix = value trace_tree"
    using root_eq trace_root eqs by simp
  have comp_root_prefix:
    "hd (sqp_composition_fri_roots prefix) = value composition_tree"
    using comp_root comp_roots_eq eqs by simp
  have conclusion:
    "checked_staged_query_prefix_dynamic_index_hit
      (\<lambda>prefix prefix_state.
        staged_query_prefix_committed_query_target prefix prefix_state)
      (Some (((prefix, prefix_state), raw), raw_state)) \<or>
     hash_map_new_output_hit
      (set_tree trace_tree \<union> set_tree composition_tree)
      prefix_state final_state"
  proof -
    from split_prefix show ?thesis
    proof
      assume prefix_binds:
        "merkle_root_binds_table (sqp_trace_root prefix) trace_table
          prefix_state \<and>
         merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
          composition_table prefix_state"
      then have trace_bind:
          "merkle_root_binds_table (sqp_trace_root prefix) trace_table
            prefix_state"
        and comp_bind:
          "merkle_root_binds_table (hd (sqp_composition_fri_roots prefix))
            composition_table prefix_state"
        by simp_all
    have candidate:
      "(trace_table, composition_table) \<in>
        query_header_committed_table_candidates prefix_state
          (sqp_trace_root prefix)
          (sqp_composition_fri_roots prefix)"
      unfolding query_header_committed_table_candidates_def
      using trace_bind comp_nonempty_prefix comp_bind by simp
    have raw_target_prefix:
      "index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (sqp_alphas prefix)"
      using raw_hit_target unfolding raw_eq alphas_eq .
	    have target:
	      "index (to_nat raw) \<in>
	        staged_query_prefix_committed_query_target prefix prefix_state"
	      by (rule staged_query_prefix_committed_query_targetI
	          [OF candidate raw_target_prefix])
    then show ?thesis
      unfolding checked_staged_query_prefix_dynamic_index_hit_def by simp
  next
      assume
        "hash_map_new_output_hit
          (set_tree trace_tree \<union> set_tree composition_tree)
          prefix_state final_state"
      then show ?thesis by simp
    qed
	  qed
	  show ?thesis
	    apply (rule_tac x=prefix in exI)
	    apply (rule_tac x=prefix_state in exI)
	    apply (rule_tac x=raw in exI)
	    apply (rule_tac x=raw_state in exI)
	    apply (rule_tac x=trace_tree in exI)
	    apply (rule_tac x=composition_tree in exI)
	    using prefix_receive lookup_final_raw raw_hit_actual
	      comp_nonempty_prefix trace_created trace_root_prefix comp_created
	      comp_root_prefix conclusion
	    by blast
qed

lemma checked_staged_security_with_data_state_query_bad_imp_committed_prefix_hit_or_tree_output_on_support:
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
    "staged_security_with_data_state_query_committed_prefix_hit A out \<or>
     staged_security_with_data_state_query_tree_output_hit A out"
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
  obtain final_raw_idxs where
    as_eq: "as = staged_alphas data"
    and len_final_raw: "length final_raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) final_raw_idxs"
    and lookup_final:
      "\<And>j. j < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
        Some (final_raw_idxs ! j)"
    by blast
  from checked_staged_transcript_program_outcome_query_lookups
      [OF wf controlled builder]
  obtain raw_idxs where
    len_raw: "length raw_idxs = rounds"
    and lookup_attacker_all:
      "\<forall>j < rounds.
        fmlookup (HashMap attacker_state)
          (QueryIndexChallenge j
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) j)) =
          Some (raw_idxs ! j)"
    by blast
  have s_ext_final: "?s \<le> final_state"
    by (rule verify_monad_hash_extends[OF verifier])
  have lookup_initial_i:
    "fmlookup (HashMap ?s)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    using lookup_attacker_all i_bound by simp
  have lookup_final_i_from_initial:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    by (rule hash_extension_lookup[OF lookup_initial_i s_ext_final])
  have raw_eq: "final_raw_idxs ! i = raw_idxs ! i"
    using lookup_final[OF i_bound] lookup_final_i_from_initial by simp
  have raw_hit_target:
    "index (to_nat (raw_idxs ! i)) \<in>
      query_sampling_success_space trace_table composition_table
        (staged_alphas data)"
  proof -
    have "index (to_nat (final_raw_idxs ! i)) = query_idxs ! i"
      using query_idxs_eq len_final_raw i_bound by simp
    then show ?thesis
      using query_hit as_eq raw_eq by simp
  qed
  have lookup_attacker_i:
    "fmlookup (HashMap attacker_state)
      (QueryIndexChallenge i
        (state_after_query_chunks
          (staged_query_start_hash data) (staged_query_chunks data) i)) =
      Some (raw_idxs ! i)"
    using lookup_attacker_all i_bound by simp
  from
    checked_staged_transcript_query_bound_table_hit_or_tree_output_at_committed_prefix_receive_support
      [OF wf controlled builder verifier i_bound lookup_attacker_i
        raw_hit_target bound]
  obtain prefix prefix_state raw raw_state trace_tree composition_tree where
    prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and lookup_final_raw:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    and raw_hit_actual:
      "index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (staged_alphas data)"
    and comp_nonempty: "sqp_composition_fri_roots prefix \<noteq> []"
    and trace_created:
      "created_tree trace_table trace_tree final_state"
    and trace_root: "sqp_trace_root prefix = value trace_tree"
    and comp_created:
      "created_tree composition_table composition_tree final_state"
    and comp_root:
      "hd (sqp_composition_fri_roots prefix) = value composition_tree"
    and split:
      "checked_staged_query_prefix_dynamic_index_hit
        (\<lambda>prefix prefix_state.
          staged_query_prefix_committed_query_target prefix prefix_state)
        (Some (((prefix, prefix_state), raw), raw_state)) \<or>
       hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
    by blast
  from split show ?thesis
	  proof
	    assume prefix_hit:
	      "checked_staged_query_prefix_dynamic_index_hit
	        (\<lambda>prefix prefix_state.
	          staged_query_prefix_committed_query_target prefix prefix_state)
	        (Some (((prefix, prefix_state), raw), raw_state))"
	    have committed_body:
	      "\<exists>i prefix prefix_state raw raw_state.
	        i < rounds \<and>
	        Some (data, attacker_state) \<in>
	          set_dist
	            (execute (checked_staged_transcript_program A)
	              adversary_initial_state) \<and>
	        Some (((prefix, prefix_state), raw), raw_state) \<in>
	          set_dist
	            (execute
	              (checked_staged_query_prefix_receive_with_state A i)
	              adversary_initial_state) \<and>
	        checked_staged_query_prefix_dynamic_index_hit
	          staged_query_prefix_committed_query_target
	          (Some (((prefix, prefix_state), raw), raw_state))"
	      apply (rule_tac x=i in exI)
	      apply (rule_tac x=prefix in exI)
	      apply (rule_tac x=prefix_state in exI)
	      apply (rule_tac x=raw in exI)
	      apply (rule_tac x=raw_state in exI)
	      using i_bound builder prefix_receive prefix_hit
	      by simp
	    then show ?thesis
	      unfolding out_eq
	        staged_security_with_data_state_query_committed_prefix_hit_def
	      by simp
	  next
	    assume tree_hit:
	      "hash_map_new_output_hit
	        (set_tree trace_tree \<union> set_tree composition_tree)
	        prefix_state final_state"
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
	              (staged_query_start_hash data)
	              (staged_query_chunks data) i)) =
	          Some raw \<and>
	        index (to_nat raw) \<in>
	          query_sampling_success_space trace_table composition_table
	            (staged_alphas data) \<and>
	        Some (((prefix, prefix_state), raw), raw_state) \<in>
	          set_dist
	            (execute
	              (checked_staged_query_prefix_receive_with_state A i)
	              adversary_initial_state) \<and>
	        sqp_composition_fri_roots prefix \<noteq> [] \<and>
	        created_tree trace_table trace_tree final_state \<and>
	        sqp_trace_root prefix = value trace_tree \<and>
	        created_tree composition_table composition_tree final_state \<and>
	        hd (sqp_composition_fri_roots prefix) =
	          value composition_tree \<and>
	        hash_map_new_output_hit
	          (set_tree trace_tree \<union> set_tree composition_tree)
	          prefix_state final_state"
	      apply (rule_tac x=i in exI)
	      apply (rule_tac x=prefix in exI)
	      apply (rule_tac x=prefix_state in exI)
	      apply (rule_tac x=raw in exI)
	      apply (rule_tac x=raw_state in exI)
	      apply (rule_tac x=trace_table in exI)
	      apply (rule_tac x=composition_table in exI)
	      apply (rule_tac x=as in exI)
	      apply (rule_tac x=query_idxs in exI)
	      apply (rule_tac x=trace_tree in exI)
	      apply (rule_tac x=composition_tree in exI)
	      using i_bound builder verifier bound lookup_final_raw raw_hit_actual
	        prefix_receive comp_nonempty trace_created trace_root comp_created
	        comp_root tree_hit
	      by blast
	    then show ?thesis
	      unfolding out_eq
	        staged_security_with_data_state_query_tree_output_hit_def Let_def
	      by simp
	  qed
	qed

lemma checked_staged_security_with_data_state_query_bad_imp_length_committed_prefix_hit_or_tree_output_on_support:
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
    "staged_security_with_data_state_query_length_committed_prefix_hit A out \<or>
     staged_security_with_data_state_query_tree_output_hit A out"
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
	  from
	    checked_staged_transcript_query_bound_table_hit_or_tree_output_at_length_committed_prefix_receive_support
	      [OF wf controlled builder verifier i_bound bound query_hit]
  obtain prefix prefix_state raw raw_state trace_tree composition_tree where
    prefix_receive:
      "Some (((prefix, prefix_state), raw), raw_state) \<in>
        set_dist
          (execute (checked_staged_query_prefix_receive_with_state A i)
            adversary_initial_state)"
    and lookup_final_raw:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge i
          (state_after_query_chunks
            (staged_query_start_hash data) (staged_query_chunks data) i)) =
        Some raw"
    and raw_hit_actual:
      "index (to_nat raw) \<in>
        query_sampling_success_space trace_table composition_table
          (staged_alphas data)"
    and comp_nonempty: "sqp_composition_fri_roots prefix \<noteq> []"
    and trace_created:
      "created_tree trace_table trace_tree final_state"
    and trace_root: "sqp_trace_root prefix = value trace_tree"
    and comp_created:
      "created_tree composition_table composition_tree final_state"
    and comp_root:
      "hd (sqp_composition_fri_roots prefix) = value composition_tree"
    and split:
      "checked_staged_query_prefix_dynamic_index_hit
        staged_query_prefix_length_committed_query_target
        (Some (((prefix, prefix_state), raw), raw_state)) \<or>
       hash_map_new_output_hit
        (set_tree trace_tree \<union> set_tree composition_tree)
        prefix_state final_state"
    by blast
  from split show ?thesis
	  proof
	    assume prefix_hit:
	      "checked_staged_query_prefix_dynamic_index_hit
	        staged_query_prefix_length_committed_query_target
	        (Some (((prefix, prefix_state), raw), raw_state))"
	    have length_body:
	      "\<exists>i prefix prefix_state raw raw_state.
	        i < rounds \<and>
	        Some (data, attacker_state) \<in>
	          set_dist
	            (execute (checked_staged_transcript_program A)
	              adversary_initial_state) \<and>
	        Some (((prefix, prefix_state), raw), raw_state) \<in>
	          set_dist
	            (execute
	              (checked_staged_query_prefix_receive_with_state A i)
	              adversary_initial_state) \<and>
	        checked_staged_query_prefix_dynamic_index_hit
	          staged_query_prefix_length_committed_query_target
	          (Some (((prefix, prefix_state), raw), raw_state))"
	      apply (rule_tac x=i in exI)
	      apply (rule_tac x=prefix in exI)
	      apply (rule_tac x=prefix_state in exI)
	      apply (rule_tac x=raw in exI)
	      apply (rule_tac x=raw_state in exI)
	      using i_bound builder prefix_receive prefix_hit
	      by simp
	    then show ?thesis
	      unfolding out_eq
	        staged_security_with_data_state_query_length_committed_prefix_hit_def
	      by simp
	  next
	    assume tree_hit:
	      "hash_map_new_output_hit
	        (set_tree trace_tree \<union> set_tree composition_tree)
	        prefix_state final_state"
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
	              (staged_query_start_hash data)
	              (staged_query_chunks data) i)) =
	          Some raw \<and>
	        index (to_nat raw) \<in>
	          query_sampling_success_space trace_table composition_table
	            (staged_alphas data) \<and>
	        Some (((prefix, prefix_state), raw), raw_state) \<in>
	          set_dist
	            (execute
	              (checked_staged_query_prefix_receive_with_state A i)
	              adversary_initial_state) \<and>
	        sqp_composition_fri_roots prefix \<noteq> [] \<and>
	        created_tree trace_table trace_tree final_state \<and>
	        sqp_trace_root prefix = value trace_tree \<and>
	        created_tree composition_table composition_tree final_state \<and>
	        hd (sqp_composition_fri_roots prefix) =
	          value composition_tree \<and>
	        hash_map_new_output_hit
	          (set_tree trace_tree \<union> set_tree composition_tree)
	          prefix_state final_state"
	      apply (rule_tac x=i in exI)
	      apply (rule_tac x=prefix in exI)
	      apply (rule_tac x=prefix_state in exI)
	      apply (rule_tac x=raw in exI)
	      apply (rule_tac x=raw_state in exI)
	      apply (rule_tac x=trace_table in exI)
	      apply (rule_tac x=composition_table in exI)
	      apply (rule_tac x=as in exI)
	      apply (rule_tac x=query_idxs in exI)
	      apply (rule_tac x=trace_tree in exI)
	      apply (rule_tac x=composition_tree in exI)
	      using i_bound builder verifier bound lookup_final_raw raw_hit_actual
	        prefix_receive comp_nonempty trace_created trace_root comp_created
	        comp_root tree_hit
	      by blast
	    then show ?thesis
	      unfolding out_eq
	        staged_security_with_data_state_query_tree_output_hit_def Let_def
	      by simp
	  qed
	qed

lemma checked_staged_security_with_data_state_query_bad_bound_from_committed_prefix_hit_or_tree_output:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_committed_prefix_hit A)
      adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_tree_output_hit A)
      adversary_initial_state"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?committed =
    "staged_security_with_data_state_query_committed_prefix_hit A"
  let ?tree = "staged_security_with_data_state_query_tree_output_hit A"
  have "wp_event ?M staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
    wp_event ?M (\<lambda>out. ?committed out \<or> ?tree out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule checked_staged_security_with_data_state_query_bad_imp_committed_prefix_hit_or_tree_output_on_support
        [OF wf controlled])
  also have "... \<le>
      wp_event ?M ?committed adversary_initial_state +
      wp_event ?M ?tree adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

lemma checked_staged_security_with_data_state_query_bad_bound_from_length_committed_prefix_hit_or_tree_output:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      staged_security_with_data_state_query_bad_hit adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_length_committed_prefix_hit A)
      adversary_initial_state +
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_query_tree_output_hit A)
      adversary_initial_state"
proof -
  let ?M = "checked_staged_security_experiment_with_data_state A"
  let ?committed =
    "staged_security_with_data_state_query_length_committed_prefix_hit A"
  let ?tree = "staged_security_with_data_state_query_tree_output_hit A"
  have "wp_event ?M staged_security_with_data_state_query_bad_hit
      adversary_initial_state \<le>
    wp_event ?M (\<lambda>out. ?committed out \<or> ?tree out)
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (rule
        checked_staged_security_with_data_state_query_bad_imp_length_committed_prefix_hit_or_tree_output_on_support
        [OF wf controlled])
  also have "... \<le>
      wp_event ?M ?committed adversary_initial_state +
      wp_event ?M ?tree adversary_initial_state"
    by (rule wp_event_union_bound)
  finally show ?thesis .
qed

end

end
