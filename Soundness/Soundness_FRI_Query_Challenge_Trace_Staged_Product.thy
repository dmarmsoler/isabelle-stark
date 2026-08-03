(*  Title:      Stark/Soundness_FRI_Query_Challenge_Trace_Staged_Product.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Query_Challenge_Trace_Staged_Product
  imports Soundness_FRI_Query_Challenge_Actual_Product
begin

text \<open>
  Trace-side staged product accounting for the challenge-fresh/query-path-fresh
  FRI pair branch.

  This theory is intentionally narrow.  The preceding layer contains the
  verifier-local actual-fresh product bounds and the raw-list path bridges.
  Here we package the trace bridge into staged fixed-challenge and finite-cover
  product bounds.
\<close>

context soundness
begin

lemma verifier_after_trace_fri_query_index_list_path_fresh_imp_actual_raw_path:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix:
      "Some ((fr, f_fl), prefix_state) \<in>
        set_dist
          (execute verifier_trace_fri_prefix
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
    and read_trace_final:
      "Some (f_final, s3) \<in> set_dist (execute read prefix_state)"
    and alpha_out:
      "Some (as, s4) \<in>
        set_dist (execute (mmap (replicate (length spec) alpha_round)) s3)"
    and read_dg: "Some (dg, s5) \<in> set_dist (execute read s4)"
    and degree_assert:
      "Some ((), s6) \<in>
        set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
    and comp_fri:
      "Some (fl, s7) \<in>
        set_dist (execute
          (ntimes receive_composition_fri_commits
            (ceil_log (to_nat dg + 1))) s6)"
    and read_final:
      "Some (final, query_state) \<in> set_dist (execute read s7)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    and hit:
      "staged_security_with_data_state_query_index_list_path_fresh Q
        (Some (((data, attacker_state), result), final_state))"
  shows "\<exists>raws \<in> query_index_raw_list_preimage Q.
    query_rounds_raw_list_path_hit query_state raws rounds
      (Some (result, final_state))"
proof -
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  from ntimes_verifier_query_rounds_outcome[OF query_out]
  obtain raw_idxs query_idxs query_chunks where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and tr_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and state_final:
      "PState final_state =
        state_after_query_chunks (PState query_state) query_chunks rounds"
    and round_chunks:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and lookups:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    by blast
  have trace_prefix_res:
    "length f_fl = ceil_log clength \<and>
     PTranscript ?s = [fr] @ map snd f_fl @ PTranscript prefix_state \<and>
     PState prefix_state =
       foldl concat (concat (PState ?s) fr) (map snd f_fl) \<and>
     PQueryCounter prefix_state = PQueryCounter ?s"
    using verifier_trace_fri_prefix_outcome[OF prefix] by simp
  from read_outcome[OF read_trace_final] obtain rest3 where
    tr_prefix: "PTranscript prefix_state = f_final # rest3"
    and tr_s3: "PTranscript s3 = rest3"
    and state_s3: "PState s3 = concat (PState prefix_state) f_final"
    and counter_s3: "PQueryCounter s3 = PQueryCounter prefix_state"
    by blast
  have alpha_res:
    "length as = length spec \<and>
     PTranscript s3 = as @ PTranscript s4 \<and>
     PState s4 = foldl concat (PState s3) as \<and>
     PQueryCounter s4 = PQueryCounter s3"
    using mmap_alpha_round_outcome[OF alpha_out] by simp
  from read_outcome[OF read_dg] obtain rest5 where
    tr_s4: "PTranscript s4 = dg # rest5"
    and tr_s5: "PTranscript s5 = rest5"
    and state_s5: "PState s5 = concat (PState s4) dg"
    and counter_s5: "PQueryCounter s5 = PQueryCounter s4"
    by blast
  have s6_eq: "s6 = s5"
    using degree_assert unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
  have comp_res:
    "length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript s6 = map snd fl @ PTranscript s7 \<and>
     PState s7 = foldl concat (PState s6) (map snd fl) \<and>
     PQueryCounter s7 = PQueryCounter s6"
    using ntimes_receive_composition_fri_commits_outcome[OF comp_fri]
    by simp
  from read_outcome[OF read_final] obtain rest_query where
    tr_s7: "PTranscript s7 = final # rest_query"
    and tr_read_query: "PTranscript query_state = rest_query"
    and state_query: "PState query_state = concat (PState s7) final"
    and counter_query_s7: "PQueryCounter query_state = PQueryCounter s7"
    by blast
  have local_counter: "PQueryCounter query_state = 0"
    using trace_prefix_res counter_s3 alpha_res counter_s5 s6_eq comp_res
      counter_query_s7
    unfolding verifier_state_from_adversary_def by simp
  have prefix_lookup:
    "\<And>i x. fmlookup (HashMap prefix_state)
        (QueryIndexChallenge i x) =
      fmlookup (HashMap ?s) (QueryIndexChallenge i x)"
    by (rule verifier_trace_fri_prefix_preserves_query_lookup[OF prefix])
  have s3_lookup:
    "HashMap s3 = HashMap prefix_state"
    by (rule read_preserves_hash_map[OF read_trace_final])
  have s4_lookup:
    "\<And>i x. fmlookup (HashMap s4) (QueryIndexChallenge i x) =
      fmlookup (HashMap s3) (QueryIndexChallenge i x)"
  proof -
    fix i x
    show "fmlookup (HashMap s4) (QueryIndexChallenge i x) =
      fmlookup (HashMap s3) (QueryIndexChallenge i x)"
    proof (rule mmap_preserves_lookup[OF _ alpha_out])
      fix m y u v
      assume m_in: "m \<in> set (replicate (length spec) alpha_round)"
        and out: "Some (y, v) \<in> set_dist (execute m u)"
      then have m_eq: "m = alpha_round"
        by simp
      show "fmlookup (HashMap v) (QueryIndexChallenge i x) =
        fmlookup (HashMap u) (QueryIndexChallenge i x)"
        using alpha_round_preserves_query_lookup[OF out[unfolded m_eq]] .
    qed
  qed
  have s5_lookup:
    "HashMap s5 = HashMap s4"
    by (rule read_preserves_hash_map[OF read_dg])
  have s7_lookup:
    "\<And>i x. fmlookup (HashMap s7) (QueryIndexChallenge i x) =
      fmlookup (HashMap s6) (QueryIndexChallenge i x)"
  proof -
    fix i x
    show "fmlookup (HashMap s7) (QueryIndexChallenge i x) =
      fmlookup (HashMap s6) (QueryIndexChallenge i x)"
    proof (rule ntimes_preserves_lookup[OF _ comp_fri])
      fix y u v
      assume out:
        "Some (y, v) \<in>
          set_dist (execute receive_composition_fri_commits u)"
      obtain b r where y_eq: "y = (b, r)"
        by (cases y) simp
      show "fmlookup (HashMap v) (QueryIndexChallenge i x) =
        fmlookup (HashMap u) (QueryIndexChallenge i x)"
        by (rule receive_composition_fri_commits_preserves_query_lookup
            [OF out[unfolded y_eq]])
    qed
  qed
  have query_lookup:
    "HashMap query_state = HashMap s7"
    by (rule read_preserves_hash_map[OF read_final])
  have header_actual:
    "verifier_header_transcript ?s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    using trace_prefix_res tr_prefix tr_s3 alpha_res tr_s4 tr_s5 s6_eq
      comp_res tr_s7 tr_read_query
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
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
  have header_unique:
    "fr = staged_trace_root data \<and>
     map snd f_fl = staged_trace_fri_roots data \<and>
     f_final = staged_trace_final data \<and>
     as = staged_alphas data \<and>
     dg = staged_degree data \<and>
     map snd fl = staged_composition_fri_roots data \<and>
     final = staged_composition_final data \<and>
     PTranscript query_state = List.concat (staged_query_chunks data)"
    using verifier_header_transcript_unique[OF header_actual staged_header]
    by simp
  have prefix_state_query:
    "PState query_state = staged_query_start_hash data"
    using trace_prefix_res state_s3 alpha_res state_s5 s6_eq comp_res
      state_query header_unique
    unfolding staged_query_start_hash_def
      staged_composition_fri_start_hash_def
      staged_trace_fri_start_hash_def
    by simp
  have chunks_eq: "query_chunks = staged_query_chunks data"
  proof -
    from checked_staged_transcript_program_query_chunks_match_verifier_lengths
        [OF builder]
    obtain staged_query_idxs where
      staged_match:
        "staged_query_chunks_match_verifier_lengths data staged_query_idxs"
      by blast
    have query_idxs_len: "length query_idxs = rounds"
      using query_idxs_eq len_raw by simp
    have staged_match_query_idxs:
      "staged_query_chunks_match_verifier_lengths data query_idxs"
      by (rule staged_query_chunks_match_verifier_lengths_transfer
          [OF staged_match query_idxs_len])
    have parser_chunk_len:
      "\<And>i. i < rounds \<Longrightarrow>
        length (query_chunks ! i) =
          verifier_query_round_transcript_length (query_idxs ! i)
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)"
    proof -
      fix i
      assume i_bound: "i < rounds"
      show
        "length (query_chunks ! i) =
          verifier_query_round_transcript_length (query_idxs ! i)
            (staged_trace_fri_roots data)
            (staged_composition_fri_roots data)"
        using verifier_query_round_chunk_length[OF round_chunks[OF i_bound]]
          header_unique
        by simp
    qed
    have concat_staged:
      "List.concat query_chunks @ PTranscript final_state =
        List.concat (staged_query_chunks data)"
      using tr_query header_unique by simp
    then show ?thesis
      using query_chunks_eq_staged_if_matching_lengths
          [OF len_chunks concat_staged parser_chunk_len
            staged_match_query_idxs]
      by simp
  qed
  from hit obtain raw_idxs_hit query_idxs_hit where
    query_hit_in: "query_idxs_hit \<in> Q"
    and len_hit: "length raw_idxs_hit = rounds"
    and query_hit_eq:
      "query_idxs_hit =
        map (\<lambda>raw. index (to_nat raw)) raw_idxs_hit"
    and lookup_hit:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        Some (raw_idxs_hit ! i)"
    and fresh_hit:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap ?s)
          (QueryIndexChallenge i
            (state_after_query_chunks
              (staged_query_start_hash data)
              (staged_query_chunks data) i)) =
        None"
    unfolding staged_security_with_data_state_query_index_list_path_fresh_def
    by auto
  have raw_eq:
    "\<And>i. i < rounds \<Longrightarrow> raw_idxs ! i = raw_idxs_hit ! i"
    using lookups lookup_hit local_counter prefix_state_query chunks_eq
    by simp
  have raw_idxs_eq: "raw_idxs = raw_idxs_hit"
    by (rule nth_equalityI)
      (use len_raw len_hit raw_eq in simp_all)
  have raw_in: "raw_idxs \<in> query_index_raw_list_preimage Q"
    unfolding query_index_raw_list_preimage_def
    using len_raw raw_idxs_eq query_hit_in query_hit_eq by blast
  have query_lookup_start:
    "\<And>i x. fmlookup (HashMap query_state) (QueryIndexChallenge i x) =
      fmlookup (HashMap ?s) (QueryIndexChallenge i x)"
    using prefix_lookup s3_lookup s4_lookup s5_lookup s6_eq
      s7_lookup query_lookup by simp
  have local_fresh:
    "query_index_list_path_fresh query_state rounds query_chunks raw_idxs"
    unfolding query_index_list_path_fresh_def
  proof (intro conjI allI impI)
    show "length raw_idxs = rounds"
      using len_raw .
  next
    show "length query_chunks = rounds"
      using len_chunks .
  next
    fix i
    assume i_bound: "i < rounds"
    let ?x =
      "state_after_query_chunks (staged_query_start_hash data)
        (staged_query_chunks data) i"
    have "fmlookup (HashMap query_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) query_chunks i)) =
      fmlookup (HashMap ?s) (QueryIndexChallenge i ?x)"
      using local_counter prefix_state_query chunks_eq
        query_lookup_start[of i ?x] by simp
    also have "... = None"
      by (rule fresh_hit[OF i_bound])
    finally show
      "fmlookup (HashMap query_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) query_chunks i)) =
        None" .
  qed
  have path:
    "query_rounds_raw_list_path_hit query_state raw_idxs rounds
      (Some (result, final_state))"
    unfolding query_rounds_raw_list_path_hit_def
    using len_raw len_chunks state_final local_fresh lookups
    by auto
  show ?thesis
    using raw_in path by blast
qed

lemma verifier_after_trace_fri_query_index_list_path_fresh_product_bound_after_prefix:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and subset: "Q \<subseteq> fri_query_index_list_space"
    and builder:
      "Some (data, attacker_state) \<in>
        set_dist
          (execute (checked_staged_transcript_program A)
            adversary_initial_state)"
    and prefix:
      "Some (header, prefix_state) \<in>
        set_dist
          (execute verifier_trace_fri_prefix
            (verifier_state_from_adversary attacker_state
              (staged_proof_transcript data)))"
  shows
    "wp_event (verifier_after_trace_fri header)
      (\<lambda>out.
        staged_security_with_data_state_query_index_list_path_fresh Q
          (case out of
            None \<Rightarrow> None
          | Some (result, final_state) \<Rightarrow>
              Some (((data, attacker_state), result), final_state)))
      prefix_state
      \<le> nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
proof -
  obtain fr f_fl where header_eq: "header = (fr, f_fl)"
    by (cases header) auto
  let ?P =
    "\<lambda>out.
      staged_security_with_data_state_query_index_list_path_fresh Q
        (case out of
          None \<Rightarrow> None
        | Some (result, final_state) \<Rightarrow>
            Some (((data, attacker_state), result), final_state))"
  let ?C =
    "nnreal (card Q) *
      (1 / nnreal (card query_sample_space)) ^ rounds"
  have prefix':
    "Some ((fr, f_fl), prefix_state) \<in>
      set_dist
        (execute verifier_trace_fri_prefix
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))"
    using prefix header_eq by simp
  have after_eq:
    "verifier_after_trace_fri header =
      (read \<bind>
        (\<lambda>f_final.
          mmap (replicate (length spec) alpha_round) \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. ntimes receive_composition_fri_commits
                (ceil_log (to_nat dg + 1)) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final.
                    ntimes
                      (verifier_query_round_program fr f_fl f_final as fl
                        final)
                      rounds)))))))"
    unfolding header_eq verifier_after_trace_fri_def by simp
  show ?thesis
    unfolding after_eq
  proof (rule wp_event_bind_bound_by_cont)
    show "\<not> ?P None"
      unfolding staged_security_with_data_state_query_index_list_path_fresh_def
      by simp
  next
    fix f_final s3
    assume read_trace_final:
      "Some (f_final, s3) \<in> set_dist (execute read prefix_state)"
    show
      "wp_event
        (mmap (replicate (length spec) alpha_round) \<bind>
          (\<lambda>as. read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. ntimes receive_composition_fri_commits
                (ceil_log (to_nat dg + 1)) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final.
                    ntimes
                      (verifier_query_round_program fr f_fl f_final as fl
                        final)
                      rounds)))))) ?P s3 \<le> ?C"
    proof (rule wp_event_bind_bound_by_cont)
      show "\<not> ?P None"
        unfolding staged_security_with_data_state_query_index_list_path_fresh_def
        by simp
    next
      fix as s4
      assume alpha_out:
        "Some (as, s4) \<in>
          set_dist
            (execute (mmap (replicate (length spec) alpha_round)) s3)"
      show
        "wp_event
          (read \<bind>
            (\<lambda>dg. assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. ntimes receive_composition_fri_commits
                (ceil_log (to_nat dg + 1)) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final.
                    ntimes
                      (verifier_query_round_program fr f_fl f_final as fl
                        final)
                      rounds))))) ?P s4 \<le> ?C"
      proof (rule wp_event_bind_bound_by_cont)
        show "\<not> ?P None"
          unfolding staged_security_with_data_state_query_index_list_path_fresh_def
          by simp
      next
        fix dg s5
        assume read_dg:
          "Some (dg, s5) \<in> set_dist (execute read s4)"
        show
          "wp_event
            (assert (to_nat dg \<le> maxDegree) \<bind>
              (\<lambda>_. ntimes receive_composition_fri_commits
                (ceil_log (to_nat dg + 1)) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final.
                    ntimes
                      (verifier_query_round_program fr f_fl f_final as fl
                        final)
                      rounds)))) ?P s5 \<le> ?C"
        proof (rule wp_event_bind_bound_by_cont)
          show "\<not> ?P None"
            unfolding staged_security_with_data_state_query_index_list_path_fresh_def
            by simp
        next
          fix unit s6
          assume degree_assert:
            "Some (unit, s6) \<in>
              set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
          show
            "wp_event
              (ntimes receive_composition_fri_commits
                (ceil_log (to_nat dg + 1)) \<bind>
                (\<lambda>fl. read \<bind>
                  (\<lambda>final.
                    ntimes
                      (verifier_query_round_program fr f_fl f_final as fl
                        final)
                      rounds))) ?P s6 \<le> ?C"
          proof (rule wp_event_bind_bound_by_cont)
            show "\<not> ?P None"
              unfolding staged_security_with_data_state_query_index_list_path_fresh_def
              by simp
          next
            fix fl s7
            assume comp_fri:
              "Some (fl, s7) \<in>
                set_dist
                  (execute
                    (ntimes receive_composition_fri_commits
                      (ceil_log (to_nat dg + 1))) s6)"
            show
              "wp_event
                (read \<bind>
                  (\<lambda>final.
                    ntimes
                      (verifier_query_round_program fr f_fl f_final as fl
                        final)
                      rounds)) ?P s7 \<le> ?C"
            proof (rule wp_event_bind_bound_by_cont)
              show "\<not> ?P None"
                unfolding staged_security_with_data_state_query_index_list_path_fresh_def
                by simp
            next
              fix final query_state
              assume read_final:
                "Some (final, query_state) \<in> set_dist (execute read s7)"
              have degree_assert_unit:
                "Some ((), s6) \<in>
                  set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
                using degree_assert by (cases unit) simp
              have mono:
                "wp_event
                  (ntimes
                    (verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)
                  ?P query_state \<le>
                 wp_event
                  (ntimes
                    (verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)
                  (\<lambda>out. \<exists>raws \<in> query_index_raw_list_preimage Q.
                    query_rounds_raw_list_path_hit query_state raws rounds out)
                  query_state"
              proof (rule wp_event_mono_on_support)
                fix out
                assume query_out:
                  "out \<in>
                    set_dist
                      (execute
                        (ntimes
                          (verifier_query_round_program fr f_fl f_final as fl
                            final)
                          rounds)
                        query_state)"
                  and hit: "?P out"
                show "\<exists>raws\<in>query_index_raw_list_preimage Q.
                  query_rounds_raw_list_path_hit query_state raws rounds out"
                proof (cases out)
                  case None
                  then show ?thesis
                    using hit
                    unfolding staged_security_with_data_state_query_index_list_path_fresh_def
                    by simp
                next
                  case (Some pair)
                  then obtain result final_state where out_eq:
                    "out = Some (result, final_state)"
                    by (cases pair) simp
                  have query_out':
                    "Some (result, final_state) \<in>
                      set_dist
                        (execute
                          (ntimes
                            (verifier_query_round_program fr f_fl f_final as fl
                              final)
                            rounds)
                          query_state)"
                    using query_out out_eq by simp
                  have hit':
                    "staged_security_with_data_state_query_index_list_path_fresh Q
                      (Some (((data, attacker_state), result), final_state))"
                    using hit out_eq by simp
                  show ?thesis
                    using
                      verifier_after_trace_fri_query_index_list_path_fresh_imp_actual_raw_path
                      [OF wf controlled builder prefix' read_trace_final
                        alpha_out read_dg degree_assert_unit comp_fri read_final
                        query_out' hit']
                    unfolding out_eq .
                qed
              qed
              also have "... \<le> ?C"
                by (rule
                    wp_ntimes_verifier_query_round_program_query_list_path_product_bound
                    [OF subset])
              finally show
                "wp_event
                  (ntimes
                    (verifier_query_round_program fr f_fl f_final as fl final)
                    rounds)
                  ?P query_state \<le> ?C" .
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma checked_staged_security_trace_fri_pair_challenge_query_path_fresh_fixed_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and challenges_space:
      "challenges \<in> fri_challenge_space (ceil_log clength)"
    and projection:
      "fst ` (P \<inter> (UNIV \<times> {challenges})) \<subseteq> Q"
    and subset: "Q \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_trace_fri_pair_challenge_query_path_fresh P
        {challenges} Q)
      adversary_initial_state \<le>
      (1 / nnreal (CARD('f) ^ ceil_log clength)) *
        (nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
proof (rule checked_staged_security_with_data_state_bound_from_data_cont)
  let ?D =
    "nnreal (card Q) *
      (1 / nnreal (card query_sample_space)) ^ rounds"
  show "\<not> staged_security_trace_fri_pair_challenge_query_path_fresh
      P {challenges} Q None"
    unfolding staged_security_trace_fri_pair_challenge_query_path_fresh_def
      staged_security_trace_fri_pair_challenge_fresh_def
      staged_security_with_data_state_verifier_event_def
    by simp
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist
        (execute (checked_staged_transcript_program A)
          adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  let ?Event =
    "\<lambda>out.
      staged_security_trace_fri_pair_challenge_query_path_fresh P
        {challenges} Q
        (case out of
          None \<Rightarrow> None
        | Some (result, final_state) \<Rightarrow>
            Some (((data, attacker_state), result), final_state))"
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl), _) \<Rightarrow>
          map fst f_fl = challenges \<and>
          trace_fri_challenge_path_fresh ?s fr (map snd f_fl)
            (length (map snd f_fl))"
  show "wp_event verify_monad ?Event ?s \<le>
      (1 / nnreal (CARD('f) ^ ceil_log clength)) *
        (nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
    unfolding verify_monad_trace_fri_decomposition
  proof (rule order_trans)
    show "wp_event
        (verifier_trace_fri_prefix \<bind> verifier_after_trace_fri)
        ?Event ?s
      \<le> wp_event verifier_trace_fri_prefix ?Head ?s *
        (nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
    proof (rule wp_event_bind_bound_by_head_and_cont)
      show "\<not> ?Event None"
        unfolding staged_security_trace_fri_pair_challenge_query_path_fresh_def
          staged_security_trace_fri_pair_challenge_fresh_def
          staged_security_with_data_state_verifier_event_def
        by simp
    next
      fix header prefix_state
      assume prefix:
        "Some (header, prefix_state) \<in>
          set_dist (execute verifier_trace_fri_prefix ?s)"
        and not_head: "\<not> ?Head (Some (header, prefix_state))"
      obtain fr f_fl where header_eq: "header = (fr, f_fl)"
        by (cases header) auto
      have not_head':
        "map fst f_fl \<noteq> challenges \<or>
          \<not> trace_fri_challenge_path_fresh ?s fr (map snd f_fl)
            (length (map snd f_fl))"
        using not_head unfolding header_eq by simp
      show "wp_event (verifier_after_trace_fri header) ?Event prefix_state =
        0"
      proof (rule antisym)
        show "wp_event (verifier_after_trace_fri header) ?Event
            prefix_state \<le> 0"
        proof (rule order_trans)
          show "wp_event (verifier_after_trace_fri header) ?Event
              prefix_state \<le>
            wp_event (verifier_after_trace_fri header)
              (\<lambda>_. False) prefix_state"
          proof (rule wp_event_mono_on_support)
            fix out
            assume suffix:
              "out \<in>
                set_dist
                  (execute (verifier_after_trace_fri header) prefix_state)"
              and hit: "?Event out"
            show False
            proof (cases out)
              case None
              then show ?thesis
                using hit
                unfolding
                  staged_security_trace_fri_pair_challenge_query_path_fresh_def
                  staged_security_trace_fri_pair_challenge_fresh_def
                  staged_security_with_data_state_verifier_event_def
                by simp
            next
              case (Some pair)
              then obtain result final_state where out_eq:
                "out = Some (result, final_state)"
                by (cases pair) simp
              from hit out_eq have fresh:
                "trace_fri_challenge_list_fresh_hit ?s {challenges}
                  (Some (result, final_state))"
                and pair_hit:
                "trace_fri_query_challenge_pair_set_hit ?s P
                  (Some (result, final_state))"
                unfolding
                  staged_security_trace_fri_pair_challenge_query_path_fresh_def
                  staged_security_trace_fri_pair_challenge_fresh_def
                  staged_security_with_data_state_verifier_event_def
                by simp_all
              have prefix':
                "Some ((fr, f_fl), prefix_state) \<in>
                  set_dist (execute verifier_trace_fri_prefix ?s)"
                using prefix header_eq by simp
              have suffix':
                "Some (result, final_state) \<in>
                  set_dist
                    (execute (verifier_after_trace_fri (fr, f_fl))
                      prefix_state)"
                using suffix header_eq out_eq by simp
              from pair_hit obtain trace_roots trace_bs trace_final fri_dg
                  composition_roots composition_bs composition_final query_idxs
                  trace_round_layers composition_round_layers where
                openings:
                  "accepted_fri_opening_transcript ?s
                    (Some (result, final_state)) trace_roots trace_bs
                    trace_final fri_dg composition_roots composition_bs
                    composition_final query_idxs trace_round_layers
                    composition_round_layers"
                unfolding trace_fri_query_challenge_pair_set_hit_def by blast
              have pair_challenges:
                "accepted_fri_challenges ?s (Some (result, final_state))
                  trace_bs fri_dg composition_bs"
                by (rule accepted_fri_opening_transcript_challenges
                    [OF openings])
              from fresh obtain trace_bs' dg' comp_bs' where
                fresh_challenges:
                  "accepted_fri_challenges ?s (Some (result, final_state))
                    trace_bs' dg' comp_bs'"
                and trace_bs'_in: "trace_bs' \<in> {challenges}"
                unfolding trace_fri_challenge_list_fresh_hit_def by blast
              have trace_bs_eq: "trace_bs = trace_bs'"
                using accepted_fri_challenges_unique
                  [OF pair_challenges fresh_challenges]
                by simp
              have prefix_trace_eq: "trace_bs = map fst f_fl"
                by (rule
                    verifier_after_trace_fri_header_agrees_with_accepted_challenges
                    [OF prefix' suffix' pair_challenges])
              have concrete_fresh:
                "trace_fri_challenge_path_fresh ?s fr (map snd f_fl)
                  (length (map snd f_fl))"
                by (rule verifier_after_trace_fri_header_roots_agree_with_fresh_hit
                    [OF prefix' suffix' fresh])
              have head_holds:
                "map fst f_fl = challenges \<and>
                  trace_fri_challenge_path_fresh ?s fr (map snd f_fl)
                    (length (map snd f_fl))"
                using prefix_trace_eq trace_bs_eq trace_bs'_in
                  concrete_fresh by simp
              show ?thesis
                using not_head' head_holds by blast
            qed
          qed
        next
          show "wp_event (verifier_after_trace_fri header)
              (\<lambda>_. False) prefix_state \<le> 0"
            unfolding wp_event_def wp_def dist_expect_def by simp
        qed
      next
        show "0 \<le> wp_event (verifier_after_trace_fri header) ?Event
          prefix_state"
          by simp
      qed
    next
      fix header prefix_state
      assume prefix:
        "Some (header, prefix_state) \<in>
          set_dist (execute verifier_trace_fri_prefix ?s)"
        and head: "?Head (Some (header, prefix_state))"
      obtain fr f_fl where header_eq: "header = (fr, f_fl)"
        by (cases header) auto
      have event_mono:
        "wp_event (verifier_after_trace_fri header) ?Event prefix_state \<le>
         wp_event (verifier_after_trace_fri header)
          (\<lambda>out.
            staged_security_with_data_state_query_index_list_path_fresh Q
              (case out of
                None \<Rightarrow> None
              | Some (result, final_state) \<Rightarrow>
                  Some (((data, attacker_state), result), final_state)))
          prefix_state"
        by (rule wp_event_mono_on_support)
          (auto simp: staged_security_trace_fri_pair_challenge_query_path_fresh_def)
      also have "... \<le>
        nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds"
        by (rule
            verifier_after_trace_fri_query_index_list_path_fresh_product_bound_after_prefix
            [OF wf controlled subset builder prefix])
      finally show "wp_event (verifier_after_trace_fri header) ?Event
          prefix_state \<le>
        nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds" .
    qed
  next
    show "wp_event verifier_trace_fri_prefix ?Head ?s *
        (nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds)
      \<le>
      (1 / nnreal (CARD('f) ^ ceil_log clength)) *
        (nnreal (card Q) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
    proof (rule mult_right_mono)
      show "wp_event verifier_trace_fri_prefix ?Head ?s \<le>
        1 / nnreal (CARD('f) ^ ceil_log clength)"
      proof -
        let ?HeadSet =
          "\<lambda>out. case out of
              None \<Rightarrow> False
            | Some ((fr, f_fl), _) \<Rightarrow>
                map fst f_fl \<in> {challenges} \<and>
                trace_fri_challenge_path_fresh ?s fr (map snd f_fl)
                  (length (map snd f_fl))"
        have mono:
          "wp_event verifier_trace_fri_prefix ?Head ?s \<le>
            wp_event verifier_trace_fri_prefix ?HeadSet ?s"
          by (rule wp_event_mono) (auto split: option.splits prod.splits)
        have set_bound:
          "wp_event verifier_trace_fri_prefix ?HeadSet ?s \<le>
            nnreal (card {challenges}) /
              nnreal (CARD('f) ^ ceil_log clength)"
          by (rule
              wp_verifier_trace_fri_prefix_challenge_list_actual_fresh_bound
              [where B = "{challenges}"])
            (use challenges_space in auto)
        show ?thesis
          using order_trans[OF mono set_bound] by simp
      qed
      show "0 \<le> nnreal (card Q) *
        (1 / nnreal (card query_sample_space)) ^ rounds"
        by simp
    qed
  qed
qed

lemma checked_staged_security_trace_fri_pair_challenge_query_path_fresh_fiber_sum:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and challenge_subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and projection:
      "\<And>challenges.
        challenges \<in> B \<Longrightarrow>
        fst ` (P \<inter> (UNIV \<times> {challenges})) \<subseteq> Q challenges"
    and subset:
      "\<And>challenges. challenges \<in> B \<Longrightarrow>
        Q challenges \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_trace_fri_pair_challenge_query_path_fresh P B
        (\<Union>challenges \<in> B. Q challenges))
      adversary_initial_state \<le>
      (\<Sum>challenges \<in> B.
        (1 / nnreal (CARD('f) ^ ceil_log clength)) *
          (nnreal (card (Q challenges)) *
            (1 / nnreal (card query_sample_space)) ^ rounds))"
proof -
  let ?Q = "(\<Union>challenges \<in> B. Q challenges)"
  let ?E =
    "\<lambda>challenges.
      staged_security_trace_fri_pair_challenge_query_path_fresh P
        {challenges} (Q challenges)"
  let ?C =
    "\<lambda>challenges.
      (1 / nnreal (CARD('f) ^ ceil_log clength)) *
        (nnreal (card (Q challenges)) *
          (1 / nnreal (card query_sample_space)) ^ rounds)"
  have split:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_trace_fri_pair_challenge_query_path_fresh P B ?Q)
      adversary_initial_state \<le>
      wp_event (checked_staged_security_experiment_with_data_state A)
        (\<lambda>out. \<exists>challenges \<in> B. ?E challenges out)
      adversary_initial_state"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support:
      "out \<in>
        set_dist
          (execute (checked_staged_security_experiment_with_data_state A)
            adversary_initial_state)"
      and hit:
      "staged_security_trace_fri_pair_challenge_query_path_fresh P B ?Q out"
    show "\<exists>challenges \<in> B. ?E challenges out"
    proof (cases out)
      case None
      then show ?thesis
        using hit
        unfolding staged_security_trace_fri_pair_challenge_query_path_fresh_def
          staged_security_trace_fri_pair_challenge_fresh_def
          staged_security_with_data_state_verifier_event_def
        by simp
    next
      case (Some packed)
      then obtain data attacker_state result final_state where out_eq:
        "out = Some (((data, attacker_state), result), final_state)"
        by (cases packed) (auto split: prod.splits)
      let ?s =
        "verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)"
      from hit out_eq have pair_hit:
        "trace_fri_query_challenge_pair_set_hit ?s P
          (Some (result, final_state))"
        and fresh:
        "trace_fri_challenge_list_fresh_hit ?s B
          (Some (result, final_state))"
        and path:
        "staged_security_with_data_state_query_index_list_path_fresh ?Q out"
        unfolding staged_security_trace_fri_pair_challenge_query_path_fresh_def
          staged_security_trace_fri_pair_challenge_fresh_def
          staged_security_with_data_state_verifier_event_def
        by simp_all
      from fresh obtain trace_bs dg comp_bs fr trace_roots trace_final as
          composition_roots final rest where
        accepted:
          "accepted_fri_challenges ?s (Some (result, final_state))
            trace_bs dg comp_bs"
        and trace_bs_in: "trace_bs \<in> B"
        and header:
          "verifier_header_transcript ?s fr trace_roots trace_final as dg
            composition_roots final rest"
        and fresh_path:
          "trace_fri_challenge_path_fresh ?s fr trace_roots
            (length trace_roots)"
        unfolding trace_fri_challenge_list_fresh_hit_def by blast
      from pair_hit obtain trace_roots' trace_bs' trace_final' fri_dg
          composition_roots' composition_bs' composition_final' query_idxs
          trace_round_layers composition_round_layers where
        openings:
          "accepted_fri_opening_transcript ?s
            (Some (result, final_state)) trace_roots' trace_bs'
            trace_final' fri_dg composition_roots' composition_bs'
            composition_final' query_idxs trace_round_layers
            composition_round_layers"
        and pair: "(query_idxs, trace_bs') \<in> P"
        unfolding trace_fri_query_challenge_pair_set_hit_def by blast
      have pair_challenges:
        "accepted_fri_challenges ?s (Some (result, final_state))
          trace_bs' fri_dg composition_bs'"
        by (rule accepted_fri_opening_transcript_challenges[OF openings])
      have trace_eq: "trace_bs' = trace_bs"
        using accepted_fri_challenges_unique[OF pair_challenges accepted]
        by simp
      have query_in: "query_idxs \<in> Q trace_bs"
      proof -
        have "query_idxs \<in> fst ` (P \<inter> (UNIV \<times> {trace_bs}))"
          using pair trace_eq by force
        then show ?thesis
          using projection[OF trace_bs_in] by blast
      qed
      from path out_eq obtain raw_idxs query_idxs_path where
        len_raw: "length raw_idxs = rounds"
        and query_path_in: "query_idxs_path \<in> ?Q"
        and query_path_eq:
          "query_idxs_path =
            map (\<lambda>raw. index (to_nat raw)) raw_idxs"
        and lookup:
          "\<And>i. i < rounds \<Longrightarrow>
            fmlookup (HashMap final_state)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
            Some (raw_idxs ! i)"
        and fresh_lookup:
          "\<And>i. i < rounds \<Longrightarrow>
            fmlookup (HashMap ?s)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
            None"
        unfolding staged_security_with_data_state_query_index_list_path_fresh_def
        by auto
      from accepted_fri_opening_transcript_imp_accepted_transcript_shape[OF openings]
      obtain as_shape where shape:
        "accepted_transcript_shape ?s (Some (result, final_state))
          as_shape query_idxs"
        by blast
      from checked_staged_security_with_data_state_accepted_shape_query_keys
          [OF wf controlled support[unfolded out_eq] shape]
      obtain raw_idxs_pair where
        len_raw_pair: "length raw_idxs_pair = rounds"
        and query_idxs_eq:
          "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs_pair"
        and lookup_pair:
          "\<And>i. i < rounds \<Longrightarrow>
            fmlookup (HashMap final_state)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
            Some (raw_idxs_pair ! i)"
        by blast
      have raw_eq:
        "\<And>i. i < rounds \<Longrightarrow> raw_idxs ! i = raw_idxs_pair ! i"
        using lookup lookup_pair by simp
      have raw_idxs_eq: "raw_idxs = raw_idxs_pair"
        by (rule nth_equalityI)
          (use len_raw len_raw_pair raw_eq in simp_all)
      have path_witness:
        "length raw_idxs = rounds \<and>
          query_idxs \<in> Q trace_bs \<and>
          query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
          (\<forall>i < rounds.
            fmlookup (HashMap final_state)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
              Some (raw_idxs ! i) \<and>
            fmlookup (HashMap ?s)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
              None)"
        using len_raw raw_idxs_eq query_in query_idxs_eq lookup
          fresh_lookup by auto
      have path_body:
        "\<exists>raw_idxs query_idxs.
          length raw_idxs = rounds \<and>
          query_idxs \<in> Q trace_bs \<and>
          query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
          (\<forall>i < rounds.
            fmlookup (HashMap final_state)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
              Some (raw_idxs ! i) \<and>
            fmlookup (HashMap ?s)
              (QueryIndexChallenge i
                (state_after_query_chunks
                  (staged_query_start_hash data)
                  (staged_query_chunks data) i)) =
              None)"
        using path_witness by blast
      have path_single:
        "staged_security_with_data_state_query_index_list_path_fresh
          (Q trace_bs) out"
        unfolding out_eq
          staged_security_with_data_state_query_index_list_path_fresh_def
        using path_body by simp
      have fresh_single:
        "trace_fri_challenge_list_fresh_hit ?s {trace_bs}
          (Some (result, final_state))"
      proof -
        have witness:
          "accepted_fri_challenges ?s (Some (result, final_state))
              trace_bs dg comp_bs \<and>
            verifier_header_transcript ?s fr trace_roots trace_final as dg
              composition_roots final rest \<and>
            trace_bs \<in> {trace_bs} \<and>
            trace_fri_challenge_path_fresh ?s fr trace_roots
              (length trace_roots)"
          using accepted header fresh_path by simp
        show ?thesis
          unfolding trace_fri_challenge_list_fresh_hit_def
          using witness by blast
      qed
      have singleton:
        "?E trace_bs out"
        unfolding out_eq
          staged_security_trace_fri_pair_challenge_query_path_fresh_def
          staged_security_trace_fri_pair_challenge_fresh_def
          staged_security_with_data_state_verifier_event_def
        using pair_hit fresh_single path_single out_eq by simp
      show ?thesis
        using singleton trace_bs_in by blast
    qed
  qed
  also have "... \<le> (\<Sum>challenges \<in> B. ?C challenges)"
  proof (rule wp_event_finite_union_bound_fri_exact)
    show "finite B"
      using challenge_subset by (rule finite_subset)
        (rule finite_fri_challenge_space)
  next
    fix challenges
    assume challenges_in: "challenges \<in> B"
    have challenges_space:
      "challenges \<in> fri_challenge_space (ceil_log clength)"
      using challenge_subset challenges_in by blast
    show "wp_event (checked_staged_security_experiment_with_data_state A)
        (?E challenges) adversary_initial_state \<le> ?C challenges"
      by (rule
          checked_staged_security_trace_fri_pair_challenge_query_path_fresh_fixed_bound
          [OF wf controlled challenges_space
            projection[OF challenges_in] subset[OF challenges_in]])
  qed
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_query_challenge_pair_set_hit_challenge_weighted_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and challenge_subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and challenge_projection: "snd ` P \<subseteq> B"
    and query_projection:
      "\<And>challenges.
        challenges \<in> B \<Longrightarrow>
        fst ` (P \<inter> (UNIV \<times> {challenges})) \<subseteq> Q challenges"
    and subset:
      "\<And>challenges. challenges \<in> B \<Longrightarrow>
        Q challenges \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      (\<Sum>challenges \<in> B.
        (1 / nnreal (CARD('f) ^ ceil_log clength)) *
          (nnreal (card (Q challenges)) *
            (1 / nnreal (card query_sample_space)) ^ rounds)) +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (\<Union>challenges \<in> B. Q challenges))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      hash_relation_budget_value (card B * ceil_log clength)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  let ?Q = "(\<Union>challenges \<in> B. Q challenges)"
  let ?Path =
    "(\<Sum>challenges \<in> B.
      (1 / nnreal (CARD('f) ^ ceil_log clength)) *
        (nnreal (card (Q challenges)) *
          (1 / nnreal (card query_sample_space)) ^ rounds))"
  let ?QueryPre =
    "hash_relation_budget_value
      (query_index_raw_list_relation_fiber_bound ?Q)
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget)"
  let ?ChallengePre =
    "hash_relation_budget_value (card B * ceil_log clength)
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget)"
  have finite_B: "finite B"
    using challenge_subset by (rule finite_subset)
      (rule finite_fri_challenge_space)
  have fst_projection: "fst ` P \<subseteq> ?Q"
  proof
    fix q
    assume q_in: "q \<in> fst ` P"
    then obtain c where pair: "(q, c) \<in> P"
      by auto
    have c_in: "c \<in> B"
      using challenge_projection pair by force
    have "q \<in> fst ` (P \<inter> (UNIV \<times> {c}))"
      using pair by force
    then have "q \<in> Q c"
      using query_projection[OF c_in] by blast
    then show "q \<in> ?Q"
      using c_in by blast
  qed
  have path_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_trace_fri_pair_challenge_query_path_fresh P B ?Q)
      adversary_initial_state \<le> ?Path"
    by (rule
        checked_staged_security_trace_fri_pair_challenge_query_path_fresh_fiber_sum
        [OF wf controlled challenge_subset query_projection subset])
  have fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_trace_fri_pair_challenge_fresh P B)
      adversary_initial_state \<le> ?Path + ?QueryPre"
    by (rule
        checked_staged_security_trace_fri_pair_challenge_fresh_bound_from_query_path_fresh
        [OF wf controlled fst_projection path_bound])
  have pair_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      (?Path + ?QueryPre) + ?ChallengePre"
    by (rule
        checked_staged_security_trace_fri_query_challenge_pair_set_hit_bound_from_challenge_fresh
        [OF wf controlled finite_B challenge_projection fresh_bound])
  then show ?thesis
    by (simp add: add.assoc)
qed

lemma checked_staged_security_composition_fri_query_challenge_pair_set_hit_challenge_weighted_bound:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and challenge_subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and challenge_projection: "\<And>dg. snd ` P dg \<subseteq> B dg"
    and query_projection:
      "\<And>dg challenges.
        challenges \<in> B dg \<Longrightarrow>
        fst ` (P dg \<inter> (UNIV \<times> {challenges})) \<subseteq>
          Q dg challenges"
    and subset:
      "\<And>dg challenges. challenges \<in> B dg \<Longrightarrow>
        Q dg challenges \<subseteq> fri_query_index_list_space"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      (\<Sum>dg \<in> UNIV.
        \<Sum>challenges \<in> B dg.
          (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
            (nnreal (card (Q dg challenges)) *
              (1 / nnreal (card query_sample_space)) ^ rounds)) +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (\<Union>dg \<in> UNIV. \<Union>challenges \<in> B dg.
            Q dg challenges))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (B dg) * ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  let ?Q =
    "(\<Union>dg \<in> UNIV. \<Union>challenges \<in> B dg. Q dg challenges)"
  let ?Path =
    "(\<Sum>dg \<in> UNIV.
      \<Sum>challenges \<in> B dg.
        (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
          (nnreal (card (Q dg challenges)) *
            (1 / nnreal (card query_sample_space)) ^ rounds))"
  let ?QueryPre =
    "hash_relation_budget_value
      (query_index_raw_list_relation_fiber_bound ?Q)
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget)"
  let ?ChallengePre =
    "hash_relation_budget_value
      (\<Sum>dg \<in> (UNIV :: 'f set).
        card (B dg) * ceil_log (maxDegree + 1))
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget)"
  have finite_B: "\<And>dg. finite (B dg)"
    by (rule finite_subset[OF challenge_subset])
      (rule finite_fri_challenge_space)
  have fst_projection: "\<And>dg. fst ` P dg \<subseteq> ?Q"
  proof
    fix dg q
    assume q_in: "q \<in> fst ` P dg"
    then obtain c where pair: "(q, c) \<in> P dg"
      by auto
    have c_in: "c \<in> B dg"
      using challenge_projection[of dg] pair by force
    have "q \<in> fst ` (P dg \<inter> (UNIV \<times> {c}))"
      using pair by force
    then have "q \<in> Q dg c"
      using query_projection[OF c_in] by blast
    then show "q \<in> ?Q"
      using c_in by blast
  qed
  have path_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_composition_fri_pair_challenge_query_path_fresh P
        B ?Q)
      adversary_initial_state \<le> ?Path"
    by (rule
        checked_staged_security_composition_fri_pair_challenge_query_path_fresh_fiber_sum
        [OF wf controlled challenge_subset query_projection subset])
  have fresh_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_composition_fri_pair_challenge_fresh P B)
      adversary_initial_state \<le> ?Path + ?QueryPre"
    by (rule
        checked_staged_security_composition_fri_pair_challenge_fresh_bound_from_query_path_fresh
        [OF wf controlled fst_projection path_bound])
  have pair_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s P))
      adversary_initial_state \<le>
      (?Path + ?QueryPre) + ?ChallengePre"
    by (rule
        checked_staged_security_composition_fri_query_challenge_pair_set_hit_bound_from_challenge_fresh
        [OF wf controlled finite_B challenge_projection fresh_bound])
  then show ?thesis
    by (simp add: add.assoc)
qed

lemma checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_pair_fraction_challenge_weighted:
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fraction:
      "generic_fri_sampled_query_pair_fraction_bound trace_table_low_degree
        (Not \<circ> trace_table_low_degree) (clength - 1) C"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      C +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (\<Union>challenges \<in> fri_challenge_space (ceil_log clength).
            generic_fri_sampled_query_query_fiber trace_table_low_degree
              (Not \<circ> trace_table_low_degree) (clength - 1) challenges))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      hash_relation_budget_value
        (card (fri_challenge_space (ceil_log clength)) * ceil_log clength)
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  let ?P =
    "trace_fri_sampled_query_bad_pair_union \<inter>
      (fri_query_index_list_space \<times> UNIV)"
  let ?B = "fri_challenge_space (ceil_log clength)"
  let ?Q =
    "\<lambda>challenges.
      generic_fri_sampled_query_query_fiber trace_table_low_degree
        (Not \<circ> trace_table_low_degree) (clength - 1) challenges"
  let ?Path =
    "(\<Sum>challenges \<in> ?B.
      (1 / nnreal (CARD('f) ^ ceil_log clength)) *
        (nnreal (card (?Q challenges)) *
          (1 / nnreal (card query_sample_space)) ^ rounds))"
  let ?QueryPre =
    "hash_relation_budget_value
      (query_index_raw_list_relation_fiber_bound
        (\<Union>challenges \<in> ?B. ?Q challenges))
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget)"
  let ?ChallengePre =
    "hash_relation_budget_value
      (card ?B * ceil_log clength)
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget)"
  have sampled_to_pair:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_query_challenge_pair_set_hit s ?P))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          trace_fri_sampled_query_bad_candidate_imp_restricted_query_challenge_pair_union_hit
        split: option.splits prod.splits)
  also have "... \<le> ?Path + ?QueryPre + ?ChallengePre"
  proof -
    have challenge_subset:
      "?B \<subseteq> fri_challenge_space (ceil_log clength)"
      by simp
    have challenge_projection: "snd ` ?P \<subseteq> ?B"
      by (rule trace_fri_restricted_sampled_query_bad_pair_union_challenge_projection)
    have query_projection:
      "\<And>challenges. challenges \<in> ?B \<Longrightarrow>
        fst ` (?P \<inter> (UNIV \<times> {challenges})) \<subseteq> ?Q challenges"
      by (auto
        intro: generic_fri_sampled_query_query_fiber_subset
        simp: generic_fri_sampled_query_query_fiber_def
          generic_fri_sampled_query_restricted_bad_pairs_def
          fri_query_challenge_pair_query_fiber_def
          trace_fri_sampled_query_bad_pair_union_def)
    have subset_Q:
      "\<And>challenges. challenges \<in> ?B \<Longrightarrow>
        ?Q challenges \<subseteq> fri_query_index_list_space"
      by (rule generic_fri_sampled_query_query_fiber_subset)
    show ?thesis
      by (rule
          checked_staged_security_trace_fri_query_challenge_pair_set_hit_challenge_weighted_bound
          [OF wf controlled challenge_subset challenge_projection
            query_projection subset_Q])
  qed
  also have "... \<le> C + ?QueryPre + ?ChallengePre"
  proof -
    have round_eq:
      "fri_round_count_for_degree_bound (clength - Suc 0) = ceil_log clength"
      unfolding fri_round_count_for_degree_bound_def
      by (simp add: clength_pos)
    have fiber_fraction:
      "nnreal
        (\<Sum>challenges \<in> ?B. card (?Q challenges)) /
        (nnreal (CARD('f) ^ ceil_log clength) *
          nnreal query_sample_space_size ^ rounds)
        \<le> C"
      using fraction
      unfolding trace_fri_sampled_query_pair_fraction_bound_iff_fiber_sum
      by (simp add: round_eq card_fri_query_index_list_space
          query_sample_space_size_pos algebra_simps)
    have prob_eq:
      "?Path =
       nnreal
        (\<Sum>challenges \<in> ?B. card (?Q challenges)) /
        (nnreal (CARD('f) ^ ceil_log clength) *
          nnreal query_sample_space_size ^ rounds)"
      using weighted_query_fiber_sum_eq
        [where I = ?B
          and f = "\<lambda>challenges. card (?Q challenges)"
          and A = "CARD('f) ^ ceil_log clength"
          and B = query_sample_space_size]
      by (simp add: finite_fri_challenge_space query_sample_space_size_pos
          card_query_sample_space algebra_simps)
    have "?Path \<le> C"
      using fiber_fraction unfolding prob_eq .
    then show ?thesis
      by (simp add: add_mono)
  qed
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_pair_fraction_challenge_weighted:
  fixes C :: "'f \<Rightarrow> prob"
  assumes wf: "staged_budget_wellformed budgets"
    and controlled: "staged_adversary_controlled budgets A"
    and fraction:
      "\<And>dg. generic_fri_sampled_query_pair_fraction_bound
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree) (to_nat dg) (C dg)"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
      (\<Sum>dg \<in> UNIV. C dg) +
      hash_relation_budget_value
        (query_index_raw_list_relation_fiber_bound
          (\<Union>dg \<in> UNIV.
            \<Union>challenges \<in> fri_challenge_space (ceil_log (to_nat dg + 1)).
              generic_fri_sampled_query_query_fiber
                (composition_table_low_degree (to_nat dg))
                (Not \<circ> composition_table_low_degree maxDegree)
                (to_nat dg) challenges))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget) +
      hash_relation_budget_value
        (\<Sum>dg \<in> (UNIV :: 'f set).
          card (fri_challenge_space (ceil_log (to_nat dg + 1))) *
            ceil_log (maxDegree + 1))
        (staged_attacker_query_budget budgets +
          staged_challenge_query_budget)"
proof -
  let ?P =
    "\<lambda>dg. composition_fri_sampled_query_bad_pair_union dg \<inter>
      (fri_query_index_list_space \<times> UNIV)"
  let ?B =
    "\<lambda>dg. fri_challenge_space (ceil_log (to_nat dg + 1))"
  let ?Q =
    "\<lambda>dg challenges.
      generic_fri_sampled_query_query_fiber
        (composition_table_low_degree (to_nat dg))
        (Not \<circ> composition_table_low_degree maxDegree)
        (to_nat dg) challenges"
  let ?Path =
    "(\<Sum>dg \<in> UNIV.
      \<Sum>challenges \<in> ?B dg.
        (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
          (nnreal (card (?Q dg challenges)) *
            (1 / nnreal (card query_sample_space)) ^ rounds))"
  let ?QueryPre =
    "hash_relation_budget_value
      (query_index_raw_list_relation_fiber_bound
        (\<Union>dg \<in> UNIV. \<Union>challenges \<in> ?B dg. ?Q dg challenges))
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget)"
  let ?ChallengePre =
    "hash_relation_budget_value
      (\<Sum>dg \<in> (UNIV :: 'f set). card (?B dg) * ceil_log (maxDegree + 1))
      (staged_attacker_query_budget budgets +
        staged_challenge_query_budget)"
  have sampled_to_pair:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
     wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_query_challenge_pair_set_hit s ?P))
      adversary_initial_state"
    by (rule wp_event_mono_on_support)
      (auto simp: staged_security_with_data_state_verifier_event_def
        intro:
          composition_fri_sampled_query_bad_candidate_imp_restricted_query_challenge_pair_union_hit
        split: option.splits prod.splits)
  also have "... \<le> ?Path + ?QueryPre + ?ChallengePre"
  proof -
    have challenge_subset:
      "\<And>dg. ?B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
      by simp
    have challenge_projection: "\<And>dg. snd ` ?P dg \<subseteq> ?B dg"
      by (rule
          composition_fri_restricted_sampled_query_bad_pair_union_challenge_projection)
    have query_projection:
      "\<And>dg challenges. challenges \<in> ?B dg \<Longrightarrow>
        fst ` (?P dg \<inter> (UNIV \<times> {challenges})) \<subseteq>
          ?Q dg challenges"
      by (auto
        intro: generic_fri_sampled_query_query_fiber_subset
        simp: generic_fri_sampled_query_query_fiber_def
          generic_fri_sampled_query_restricted_bad_pairs_def
          fri_query_challenge_pair_query_fiber_def
          composition_fri_sampled_query_bad_pair_union_def)
    have subset_Q:
      "\<And>dg challenges. challenges \<in> ?B dg \<Longrightarrow>
        ?Q dg challenges \<subseteq> fri_query_index_list_space"
      by (rule generic_fri_sampled_query_query_fiber_subset)
    show ?thesis
      by (rule
          checked_staged_security_composition_fri_query_challenge_pair_set_hit_challenge_weighted_bound
          [OF wf controlled challenge_subset challenge_projection
            query_projection subset_Q])
  qed
  also have "... \<le> (\<Sum>dg \<in> UNIV. C dg) + ?QueryPre + ?ChallengePre"
  proof -
    have path_le:
      "?Path \<le> (\<Sum>dg \<in> UNIV. C dg)"
    proof (rule sum_mono)
      fix dg :: 'f
      assume "dg \<in> UNIV"
      let ?I = "?B dg"
      have round_eq:
        "fri_round_count_for_degree_bound (to_nat dg) =
          ceil_log (to_nat dg + 1)"
        unfolding fri_round_count_for_degree_bound_def by simp
      have fiber_fraction:
        "nnreal
          (\<Sum>challenges \<in> ?I. card (?Q dg challenges)) /
          (nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) *
            nnreal query_sample_space_size ^ rounds)
          \<le> C dg"
        using fraction[of dg]
        unfolding composition_fri_sampled_query_pair_fraction_bound_iff_fiber_sum
        by (simp add: round_eq card_fri_query_index_list_space
            query_sample_space_size_pos algebra_simps)
      have prob_eq:
        "(\<Sum>challenges \<in> ?I.
          (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
            (nnreal (card (?Q dg challenges)) *
              (1 / nnreal (card query_sample_space)) ^ rounds)) =
        nnreal
          (\<Sum>challenges \<in> ?I. card (?Q dg challenges)) /
        (nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) *
          nnreal query_sample_space_size ^ rounds)"
        using weighted_query_fiber_sum_eq
          [where I = ?I
            and f = "\<lambda>challenges. card (?Q dg challenges)"
            and A = "CARD('f) ^ ceil_log (to_nat dg + 1)"
            and B = query_sample_space_size]
        by (simp add: finite_fri_challenge_space query_sample_space_size_pos
            card_query_sample_space algebra_simps)
      show
        "(\<Sum>challenges \<in> ?I.
          (1 / nnreal (CARD('f) ^ ceil_log (to_nat dg + 1))) *
            (nnreal (card (?Q dg challenges)) *
              (1 / nnreal (card query_sample_space)) ^ rounds))
         \<le> C dg"
        using fiber_fraction unfolding prob_eq .
    qed
    then show ?thesis
      by (simp add: add_mono)
  qed
  finally show ?thesis .
qed

end

end
