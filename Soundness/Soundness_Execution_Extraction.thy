(*  Title:      Stark/Soundness_Execution_Extraction.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Execution_Extraction
  imports Soundness_Execution_Prefix
begin

text \<open>Accepted verifier execution transcript extraction and witness lemmas.\<close>

context soundness
begin

lemma verify_monad_hash_extends:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
  shows "s \<le> final_state"
proof -
  from outcome[unfolded verify_monad_composition_fri_decomposition]
  obtain header prefix_state where
    prefix:
      "Some (header, prefix_state) \<in>
        set_dist (execute verifier_composition_fri_prefix s)"
    and suffix:
      "Some (result, final_state) \<in>
        set_dist
          (execute (verifier_after_composition_fri header) prefix_state)"
    by (auto elim!: set_dist_bindE)
  obtain fr f_fl f_final as dg fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg, fl)"
    by (cases header) auto
  have ext_prefix: "s \<le> prefix_state"
    using verifier_composition_fri_prefix_outcome
      [OF prefix[unfolded header_eq]]
    by simp
  from suffix[unfolded header_eq verifier_after_composition_fri_def]
  obtain final query_state where
    read_final:
      "Some (final, query_state) \<in> set_dist (execute read prefix_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    by (auto elim!: set_dist_bindE)
  have ext_query: "prefix_state \<le> query_state"
    using read_outcome[OF read_final] by blast
  have ext_final: "query_state \<le> final_state"
    using ntimes_verifier_query_rounds_outcome[OF query_out] by blast
  show ?thesis
    using ext_prefix ext_query ext_final by (meson hash_ext_trans)
qed

lemma alpha_header_supported_trace_table_candidate_state_hash_extends:
  assumes
    "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
      f_final trace_table final_state"
  shows "s \<le> final_state"
proof -
  from assms obtain result composition_table as query_idxs dg
      composition_fri_roots final rest where
    outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    unfolding alpha_header_supported_trace_table_candidate_state_def
    by blast
  show ?thesis
    by (rule verify_monad_hash_extends[OF outcome])
qed

lemma alpha_header_supported_pairwise_merkle_bad_extends_initial:
  assumes bad:
    "alpha_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final"
  obtains trace_table final_state trace_table' final_state'
  where
    "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
      f_final trace_table final_state"
    "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
      f_final trace_table' final_state'"
    "trace_table \<noteq> trace_table'"
    "merkle_hash_value_conflict final_state final_state' \<or>
      hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
    "s \<le> final_state"
    "s \<le> final_state'"
proof -
  from bad obtain trace_table final_state trace_table' final_state' where
    candidate:
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
    and candidate':
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table' final_state'"
    and distinct: "trace_table \<noteq> trace_table'"
    and pair_bad:
      "merkle_hash_value_conflict final_state final_state' \<or>
        hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
    unfolding alpha_header_supported_pairwise_merkle_bad_def by blast
  have ext: "s \<le> final_state"
    by (rule alpha_header_supported_trace_table_candidate_state_hash_extends
        [OF candidate])
  have ext': "s \<le> final_state'"
    by (rule alpha_header_supported_trace_table_candidate_state_hash_extends
        [OF candidate'])
  show ?thesis
    by (rule that[OF candidate candidate' distinct pair_bad ext ext'])
qed

definition alpha_header_supported_pairwise_coupling_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "alpha_header_supported_pairwise_coupling_bad s fr f_fri_roots f_final
      \<longleftrightarrow>
      (\<exists>trace_table final_state trace_table' final_state'.
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table final_state \<and>
        alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table' final_state' \<and>
        trace_table \<noteq> trace_table' \<and>
        merkle_hash_pairwise_coupling_bad final_state final_state')"

definition alpha_supported_pairwise_coupling_bad
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "alpha_supported_pairwise_coupling_bad s \<longleftrightarrow>
      (\<exists>fr f_fri_roots f_final.
        alpha_header_supported_pairwise_coupling_bad s fr f_fri_roots
          f_final)"

lemma alpha_header_supported_pairwise_merkle_bad_imp_local_collision_or_coupling_bad:
  assumes bad:
    "alpha_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final"
  shows
    "(\<exists>trace_table final_state trace_table' final_state'.
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state \<and>
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table' final_state' \<and>
      trace_table \<noteq> trace_table' \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')) \<or>
     alpha_header_supported_pairwise_coupling_bad s fr f_fri_roots f_final"
proof -
  from bad obtain trace_table final_state trace_table' final_state'
    where candidate:
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state"
    and candidate':
      "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table' final_state'"
    and distinct: "trace_table \<noteq> trace_table'"
    and pair_bad:
      "merkle_hash_value_conflict final_state final_state' \<or>
        hash_map_output_collision
          (merkle_hash_state_merge final_state final_state')"
    unfolding alpha_header_supported_pairwise_merkle_bad_def by blast
  have decomp:
    "hash_map_output_collision final_state \<or>
     hash_map_output_collision final_state' \<or>
     merkle_hash_pairwise_coupling_bad final_state final_state'"
    by (rule merkle_hash_pairwise_bad_imp_local_collision_or_coupling_bad
        [OF pair_bad])
  show ?thesis
    using candidate candidate' distinct decomp
    unfolding alpha_header_supported_pairwise_coupling_bad_def by blast
qed

lemma alpha_supported_pairwise_merkle_bad_imp_local_collision_or_coupling_bad:
  assumes bad: "alpha_supported_pairwise_merkle_bad s"
  shows
    "(\<exists>fr f_fri_roots f_final trace_table final_state trace_table'
        final_state'.
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state \<and>
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table' final_state' \<and>
      trace_table \<noteq> trace_table' \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')) \<or>
     alpha_supported_pairwise_coupling_bad s"
proof -
  from bad obtain fr f_fri_roots f_final where header_bad:
    "alpha_header_supported_pairwise_merkle_bad s fr f_fri_roots f_final"
    unfolding alpha_supported_pairwise_merkle_bad_def by blast
  from
    alpha_header_supported_pairwise_merkle_bad_imp_local_collision_or_coupling_bad
      [OF header_bad]
  show ?thesis
    unfolding alpha_supported_pairwise_coupling_bad_def by blast
qed

lemma alpha_supported_pairwise_merkle_bad_imp_supported_hash_collision_possible_or_coupling_bad:
  assumes bad: "alpha_supported_pairwise_merkle_bad s"
  shows
    "supported_hash_output_collision_possible s \<or>
     alpha_supported_pairwise_coupling_bad s"
proof -
  have decomp:
    "(\<exists>fr f_fri_roots f_final trace_table final_state trace_table'
        final_state'.
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state \<and>
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table' final_state' \<and>
      trace_table \<noteq> trace_table' \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')) \<or>
     alpha_supported_pairwise_coupling_bad s"
    by (rule
        alpha_supported_pairwise_merkle_bad_imp_local_collision_or_coupling_bad
        [OF bad])
  then show ?thesis
  proof
    assume local:
      "\<exists>fr f_fri_roots f_final trace_table final_state trace_table'
        final_state'.
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table final_state \<and>
      alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
        f_final trace_table' final_state' \<and>
      trace_table \<noteq> trace_table' \<and>
      (hash_map_output_collision final_state \<or>
       hash_map_output_collision final_state')"
    then obtain fr f_fri_roots f_final trace_table final_state trace_table'
        final_state' where
      candidate:
        "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table final_state"
      and candidate':
        "alpha_header_supported_trace_table_candidate_state s fr f_fri_roots
          f_final trace_table' final_state'"
      and collision:
        "hash_map_output_collision final_state \<or>
         hash_map_output_collision final_state'"
      by blast
    from collision show ?thesis
    proof
      assume collision: "hash_map_output_collision final_state"
      from candidate obtain result composition_table as query_idxs dg
          composition_fri_roots final rest where
        outcome:
          "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
        and bound:
          "accepted_with_bound_tables s (Some (result, final_state))
            trace_table composition_table as query_idxs"
        unfolding alpha_header_supported_trace_table_candidate_state_def
        by blast
      have "supported_hash_output_collision_possible s"
        by (rule
            accepted_with_bound_tables_hash_collision_imp_supported_hash_output_collision_possible
            [OF outcome bound collision])
      then show ?thesis by simp
    next
      assume collision': "hash_map_output_collision final_state'"
      from candidate' obtain result' composition_table' as' query_idxs' dg'
          composition_fri_roots' final' rest' where
        outcome':
          "Some (result', final_state') \<in> set_dist (execute verify_monad s)"
        and bound':
          "accepted_with_bound_tables s (Some (result', final_state'))
            trace_table' composition_table' as' query_idxs'"
        unfolding alpha_header_supported_trace_table_candidate_state_def
        by blast
      have "supported_hash_output_collision_possible s"
        by (rule
            accepted_with_bound_tables_hash_collision_imp_supported_hash_output_collision_possible
            [OF outcome' bound' collision'])
      then show ?thesis by simp
    qed
  next
    assume "alpha_supported_pairwise_coupling_bad s"
    then show ?thesis by simp
  qed
qed

lemma verifier_composition_fri_prefix_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some (header, t) \<in>
        set_dist (execute verifier_composition_fri_prefix s)"
  shows "query_future_fresh t"
proof -
  obtain fr f_fl f_final as dg fl where header_eq:
    "header = (fr, f_fl, f_final, as, dg, fl)"
    by (cases header) auto
  from outcome[unfolded header_eq] obtain s1 s2 s3 s4 s5 s6 where
    read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
    and trace_fri:
      "Some (f_fl, s2) \<in>
        set_dist (execute
          (ntimes receive_trace_fri_commits (ceil_log clength)) s1)"
    and read_f_final:
      "Some (f_final, s3) \<in> set_dist (execute read s2)"
    and alpha_out:
      "Some (as, s4) \<in>
        set_dist (execute (mmap (replicate (length spec) alpha_round)) s3)"
    and read_dg: "Some (dg, s5) \<in> set_dist (execute read s4)"
    and degree_assert:
      "Some ((), s6) \<in>
        set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
    and comp_fri:
      "Some (fl, t) \<in>
        set_dist (execute
          (ntimes receive_composition_fri_commits
            (ceil_log (to_nat dg + 1))) s6)"
    unfolding verifier_composition_fri_prefix_def
    by (auto elim!: set_dist_bindE)
  have future_s1: "query_future_fresh s1"
    by (rule read_preserves_query_future_fresh[OF future read_fr])
  have future_s2: "query_future_fresh s2"
    by (rule ntimes_receive_trace_fri_commits_preserves_query_future_fresh
        [OF trace_fri future_s1])
  have future_s3: "query_future_fresh s3"
    by (rule read_preserves_query_future_fresh[OF future_s2 read_f_final])
  have future_s4: "query_future_fresh s4"
    by (rule mmap_alpha_round_preserves_query_future_fresh
        [OF future_s3 alpha_out])
  have future_s5: "query_future_fresh s5"
    by (rule read_preserves_query_future_fresh[OF future_s4 read_dg])
  have s6_eq: "s6 = s5"
    using degree_assert unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree")
      (auto simp: throw_no_outcome)
  have future_s6: "query_future_fresh s6"
    using future_s5 unfolding s6_eq .
  show ?thesis
    by (rule ntimes_receive_composition_fri_commits_preserves_query_future_fresh
        [OF comp_fri future_s6])
qed

lemma verify_monad_header_extraction:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
  obtains fr f_fl f_final as dg fl final query_state
  where
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    and "PState query_state =
      verifier_header_state s fr (map snd f_fl) f_final as dg (map snd fl) final"
    and "Some (result, final_state) \<in>
      set_dist (execute
        (ntimes (verifier_query_round_program fr f_fl f_final as fl final) rounds)
        query_state)"
    and "PQueryCounter query_state = PQueryCounter s"
    and "length f_fl = ceil_log clength"
    and "length as = length spec"
    and "length fl = ceil_log (to_nat dg + 1)"
proof -
  let ?alpha =
    "do {
      a0 \<leftarrow> receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  from outcome obtain fr s1 f_fl s2 f_final s3 as s4 dg s5 s6 fl s7 final query_state
    where read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
      and trace_fri:
        "Some (f_fl, s2) \<in>
          set_dist (execute
            (ntimes receive_trace_fri_commits (ceil_log clength)) s1)"
      and read_f_final: "Some (f_final, s3) \<in> set_dist (execute read s2)"
      and alpha_out:
        "Some (as, s4) \<in>
          set_dist (execute (mmap (replicate (length spec) ?alpha)) s3)"
      and read_dg: "Some (dg, s5) \<in> set_dist (execute read s4)"
      and degree_assert:
        "Some ((), s6) \<in> set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
      and comp_fri:
        "Some (fl, s7) \<in>
          set_dist (execute
            (ntimes receive_composition_fri_commits
              (ceil_log (to_nat dg + 1))) s6)"
      and read_final: "Some (final, query_state) \<in> set_dist (execute read s7)"
      and query_out:
        "Some (result, final_state) \<in>
          set_dist (execute
            (ntimes (verifier_query_round_program fr f_fl f_final as fl final) rounds)
            query_state)"
    unfolding verify_monad_def verifier_query_round_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  from read_outcome[OF read_fr] obtain rest1 where
    tr_s: "PTranscript s = fr # rest1"
    and st_s1: "PState s1 = concat (PState s) fr"
    and tr_s1: "PTranscript s1 = rest1"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  have trace_fri_res:
    "length f_fl = ceil_log clength \<and>
     PTranscript s1 = map snd f_fl @ PTranscript s2 \<and>
     PState s2 = foldl concat (PState s1) (map snd f_fl)"
    using ntimes_receive_trace_fri_commits_outcome[OF trace_fri] by simp
  have query_count_s2: "PQueryCounter s2 = PQueryCounter s1"
    using ntimes_receive_trace_fri_commits_outcome[OF trace_fri] by simp
  from read_outcome[OF read_f_final] obtain rest3 where
    tr_s2: "PTranscript s2 = f_final # rest3"
    and st_s3: "PState s3 = concat (PState s2) f_final"
    and tr_s3: "PTranscript s3 = rest3"
    and query_count_s3: "PQueryCounter s3 = PQueryCounter s2"
    by blast
  have alpha_out':
    "Some (as, s4) \<in>
      set_dist (execute (mmap (replicate (length spec) alpha_round)) s3)"
    using alpha_out by (simp add: alpha_round_def)
  have alpha_res:
    "length as = length spec \<and>
     PTranscript s3 = as @ PTranscript s4 \<and>
     PState s4 = foldl concat (PState s3) as"
    using mmap_alpha_round_outcome[OF alpha_out'] by simp
  have query_count_s4: "PQueryCounter s4 = PQueryCounter s3"
    using mmap_alpha_round_outcome[OF alpha_out'] by simp
  from read_outcome[OF read_dg] obtain rest5 where
    tr_s4: "PTranscript s4 = dg # rest5"
    and st_s5: "PState s5 = concat (PState s4) dg"
    and tr_s5: "PTranscript s5 = rest5"
    and query_count_s5: "PQueryCounter s5 = PQueryCounter s4"
    by blast
  have s6_eq: "s6 = s5"
    using degree_assert unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
  have comp_fri_res:
    "length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript s6 = map snd fl @ PTranscript s7 \<and>
     PState s7 = foldl concat (PState s6) (map snd fl)"
    using ntimes_receive_composition_fri_commits_outcome[OF comp_fri]
    by simp
  have query_count_s7: "PQueryCounter s7 = PQueryCounter s6"
    using ntimes_receive_composition_fri_commits_outcome[OF comp_fri]
    by simp
  from read_outcome[OF read_final] obtain rest_query where
    tr_s7: "PTranscript s7 = final # rest_query"
    and st_query: "PState query_state = concat (PState s7) final"
    and tr_query: "PTranscript query_state = rest_query"
    and query_count_query: "PQueryCounter query_state = PQueryCounter s7"
    by blast
  have header_tr:
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    using tr_s tr_s1 trace_fri_res tr_s2 tr_s3 alpha_res tr_s4 tr_s5
      s6_eq comp_fri_res tr_s7 tr_query
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
  have header_state:
    "PState query_state =
      verifier_header_state s fr (map snd f_fl) f_final as dg (map snd fl) final"
    using st_s1 trace_fri_res st_s3 alpha_res st_s5 s6_eq comp_fri_res st_query
    unfolding verifier_header_state_def verifier_header_messages_def
    by simp
  have query_count_header:
    "PQueryCounter query_state = PQueryCounter s"
    using query_count_s1 query_count_s2 query_count_s3 query_count_s4
      query_count_s5 s6_eq query_count_s7 query_count_query
    by simp
  show ?thesis
    by (rule that[OF header_tr header_state query_out query_count_header])
      (use trace_fri_res alpha_res comp_fri_res in simp_all)
qed

lemma verify_monad_header_query_extraction:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
  obtains fr f_fl f_final as dg fl final query_state
  where
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    and "Some (result, final_state) \<in>
      set_dist (execute
        (ntimes
          (verifier_query_round_program fr f_fl f_final as fl final) rounds)
        query_state)"
proof (rule verify_monad_header_extraction[OF outcome])
  fix fr f_fl f_final as dg fl final query_state
  assume header:
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
  show ?thesis
    by (rule that[OF header query_out])
qed

lemma verify_monad_header_random_oracle_replay:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
  obtains fr f_fl f_final as dg fl final query_state
  where
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    and "PState query_state =
      verifier_header_state s fr (map snd f_fl) f_final as dg (map snd fl) final"
    and "Some (result, final_state) \<in>
      set_dist (execute
        (ntimes (verifier_query_round_program fr f_fl f_final as fl final) rounds)
        query_state)"
    and "PQueryCounter query_state = PQueryCounter s"
    and "s \<le> query_state"
    and "\<And>i. i < length f_fl \<Longrightarrow>
      fmlookup (HashMap query_state)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr) (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))"
    and "\<And>i. i < length as \<Longrightarrow>
      fmlookup (HashMap query_state)
        (AlphaChallenge (PAlphaCounter s + i) (foldl concat
          (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
          (take i as))) =
        Some (as ! i)"
    and "\<And>i. i < length fl \<Longrightarrow>
      fmlookup (HashMap query_state)
        (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
              as)
            dg)
          (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i))"
    and "to_nat dg \<le> maxDegree"
proof -
  let ?alpha =
    "do {
      a0 \<leftarrow> receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  from outcome obtain fr s1 f_fl s2 f_final s3 as s4 dg s5 s6 fl s7 final query_state
    where read_fr: "Some (fr, s1) \<in> set_dist (execute read s)"
      and trace_fri:
        "Some (f_fl, s2) \<in>
          set_dist (execute
            (ntimes receive_trace_fri_commits (ceil_log clength)) s1)"
      and read_f_final: "Some (f_final, s3) \<in> set_dist (execute read s2)"
      and alpha_out:
        "Some (as, s4) \<in>
          set_dist (execute (mmap (replicate (length spec) ?alpha)) s3)"
      and read_dg: "Some (dg, s5) \<in> set_dist (execute read s4)"
      and degree_assert:
        "Some ((), s6) \<in> set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
      and comp_fri:
        "Some (fl, s7) \<in>
          set_dist (execute
            (ntimes receive_composition_fri_commits
              (ceil_log (to_nat dg + 1))) s6)"
      and read_final: "Some (final, query_state) \<in> set_dist (execute read s7)"
      and query_out:
        "Some (result, final_state) \<in>
          set_dist (execute
            (ntimes (verifier_query_round_program fr f_fl f_final as fl final) rounds)
            query_state)"
    unfolding verify_monad_def verifier_query_round_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  from read_outcome[OF read_fr] obtain rest1 where
    tr_s: "PTranscript s = fr # rest1"
    and st_s1: "PState s1 = concat (PState s) fr"
    and tr_s1: "PTranscript s1 = rest1"
    and ext_s_s1: "s \<le> s1"
    and trace_count_s1: "PTraceFriCounter s1 = PTraceFriCounter s"
    and comp_count_s1: "PCompositionFriCounter s1 = PCompositionFriCounter s"
    and alpha_count_s1: "PAlphaCounter s1 = PAlphaCounter s"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  have trace_fri_res:
    "length f_fl = ceil_log clength \<and>
     PTranscript s1 = map snd f_fl @ PTranscript s2 \<and>
     PState s2 = foldl concat (PState s1) (map snd f_fl) \<and>
     s1 \<le> s2 \<and>
     PTraceFriCounter s2 = PTraceFriCounter s1 + ceil_log clength \<and>
     PCompositionFriCounter s2 = PCompositionFriCounter s1 \<and>
     PAlphaCounter s2 = PAlphaCounter s1 \<and>
     PQueryCounter s2 = PQueryCounter s1 \<and>
     (\<forall>i < ceil_log clength.
        fmlookup (HashMap s2)
          (TraceFriChallenge (PTraceFriCounter s1 + i)
            (foldl concat (PState s1) (take (Suc i) (map snd f_fl)))) =
          Some (fst (f_fl ! i)))"
    using ntimes_receive_trace_fri_commits_outcome[OF trace_fri] by simp
  from read_outcome[OF read_f_final] obtain rest3 where
    tr_s2: "PTranscript s2 = f_final # rest3"
    and st_s3: "PState s3 = concat (PState s2) f_final"
    and tr_s3: "PTranscript s3 = rest3"
    and ext_s2_s3: "s2 \<le> s3"
    and trace_count_s3: "PTraceFriCounter s3 = PTraceFriCounter s2"
    and comp_count_s3: "PCompositionFriCounter s3 = PCompositionFriCounter s2"
    and alpha_count_s3: "PAlphaCounter s3 = PAlphaCounter s2"
    and query_count_s3: "PQueryCounter s3 = PQueryCounter s2"
    by blast
  have alpha_out':
    "Some (as, s4) \<in>
      set_dist (execute (mmap (replicate (length spec) alpha_round)) s3)"
    using alpha_out by (simp add: alpha_round_def)
  have alpha_res:
    "length as = length spec \<and>
     PTranscript s3 = as @ PTranscript s4 \<and>
     PState s4 = foldl concat (PState s3) as \<and>
     s3 \<le> s4 \<and>
     PTraceFriCounter s4 = PTraceFriCounter s3 \<and>
     PCompositionFriCounter s4 = PCompositionFriCounter s3 \<and>
     PAlphaCounter s4 = PAlphaCounter s3 + length spec \<and>
     PQueryCounter s4 = PQueryCounter s3 \<and>
     (\<forall>i < length spec.
        fmlookup (HashMap s4)
          (AlphaChallenge (PAlphaCounter s3 + i)
            (foldl concat (PState s3) (take i as))) =
        Some (as ! i))"
    using mmap_alpha_round_outcome[OF alpha_out'] by simp
  from read_outcome[OF read_dg] obtain rest5 where
    tr_s4: "PTranscript s4 = dg # rest5"
    and st_s5: "PState s5 = concat (PState s4) dg"
    and tr_s5: "PTranscript s5 = rest5"
    and ext_s4_s5: "s4 \<le> s5"
    and trace_count_s5: "PTraceFriCounter s5 = PTraceFriCounter s4"
    and comp_count_s5: "PCompositionFriCounter s5 = PCompositionFriCounter s4"
    and alpha_count_s5: "PAlphaCounter s5 = PAlphaCounter s4"
    and query_count_s5: "PQueryCounter s5 = PQueryCounter s4"
    by blast
  have s6_eq: "s6 = s5"
    using degree_assert unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
  have degree_bound: "to_nat dg \<le> maxDegree"
    using degree_assert unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
  have ext_s5_s6: "s5 \<le> s6"
    unfolding s6_eq by (rule hash_ext_refl)
  have comp_fri_res:
    "length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript s6 = map snd fl @ PTranscript s7 \<and>
     PState s7 = foldl concat (PState s6) (map snd fl) \<and>
     s6 \<le> s7 \<and>
     PTraceFriCounter s7 = PTraceFriCounter s6 \<and>
     PCompositionFriCounter s7 = PCompositionFriCounter s6 + ceil_log (to_nat dg + 1) \<and>
     PAlphaCounter s7 = PAlphaCounter s6 \<and>
     PQueryCounter s7 = PQueryCounter s6 \<and>
     (\<forall>i < ceil_log (to_nat dg + 1).
        fmlookup (HashMap s7)
          (CompositionFriChallenge (PCompositionFriCounter s6 + i)
            (foldl concat (PState s6) (take (Suc i) (map snd fl)))) =
          Some (fst (fl ! i)))"
    using ntimes_receive_composition_fri_commits_outcome[OF comp_fri]
    by simp
  from read_outcome[OF read_final] obtain rest_query where
    tr_s7: "PTranscript s7 = final # rest_query"
    and st_query: "PState query_state = concat (PState s7) final"
    and tr_query: "PTranscript query_state = rest_query"
    and ext_s7_query: "s7 \<le> query_state"
    and query_count_query: "PQueryCounter query_state = PQueryCounter s7"
    by blast
  have ext_s2_query: "s2 \<le> query_state"
    using ext_s2_s3 alpha_res ext_s4_s5 ext_s5_s6 comp_fri_res ext_s7_query
    by (meson hash_ext_trans)
  have ext_s4_query: "s4 \<le> query_state"
    using ext_s4_s5 ext_s5_s6 comp_fri_res ext_s7_query
    by (meson hash_ext_trans)
  have ext_s7_query': "s7 \<le> query_state"
    using ext_s7_query .
  have ext_s1_s2: "s1 \<le> s2"
    using trace_fri_res by simp
  have ext_s3_s4: "s3 \<le> s4"
    using alpha_res by simp
  have ext_s6_s7: "s6 \<le> s7"
    using comp_fri_res by simp
  have ext_s_s2: "s \<le> s2"
    by (rule hash_ext_trans[OF ext_s_s1 ext_s1_s2])
  have ext_s_s3: "s \<le> s3"
    by (rule hash_ext_trans[OF ext_s_s2 ext_s2_s3])
  have ext_s_s4: "s \<le> s4"
    by (rule hash_ext_trans[OF ext_s_s3 ext_s3_s4])
  have ext_s_s5: "s \<le> s5"
    by (rule hash_ext_trans[OF ext_s_s4 ext_s4_s5])
  have ext_s_s6: "s \<le> s6"
    by (rule hash_ext_trans[OF ext_s_s5 ext_s5_s6])
  have ext_s_s7: "s \<le> s7"
    by (rule hash_ext_trans[OF ext_s_s6 ext_s6_s7])
  have ext_s_query: "s \<le> query_state"
    by (rule hash_ext_trans[OF ext_s_s7 ext_s7_query])
  have header_tr:
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    using tr_s tr_s1 trace_fri_res tr_s2 tr_s3 alpha_res tr_s4 tr_s5
      s6_eq comp_fri_res tr_s7 tr_query
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
  have header_state:
    "PState query_state =
      verifier_header_state s fr (map snd f_fl) f_final as dg (map snd fl) final"
    using st_s1 trace_fri_res st_s3 alpha_res st_s5 s6_eq comp_fri_res st_query
    unfolding verifier_header_state_def verifier_header_messages_def
    by simp
  have trace_lookup:
    "\<And>i. i < length f_fl \<Longrightarrow>
      fmlookup (HashMap query_state)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr) (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))"
  proof -
    fix i
    assume i_bound: "i < length f_fl"
    have lookup_s2:
      "fmlookup (HashMap s2)
        (TraceFriChallenge (PTraceFriCounter s1 + i)
          (foldl concat (PState s1) (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))"
      using trace_fri_res i_bound by simp
    show "fmlookup (HashMap query_state)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr) (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))"
      using hash_extension_lookup[OF lookup_s2 ext_s2_query] st_s1
        trace_count_s1
      by simp
  qed
  have alpha_lookup:
    "\<And>i. i < length as \<Longrightarrow>
      fmlookup (HashMap query_state)
        (AlphaChallenge (PAlphaCounter s + i) (foldl concat
          (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
          (take i as))) =
        Some (as ! i)"
  proof -
    fix i
    assume i_bound: "i < length as"
    have lookup_s4:
      "fmlookup (HashMap s4)
        (AlphaChallenge (PAlphaCounter s3 + i)
          (foldl concat (PState s3) (take i as))) =
        Some (as ! i)"
      using alpha_res i_bound by simp
    show "fmlookup (HashMap query_state)
        (AlphaChallenge (PAlphaCounter s + i) (foldl concat
          (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
          (take i as))) =
        Some (as ! i)"
      using hash_extension_lookup[OF lookup_s4 ext_s4_query]
        st_s1 trace_fri_res st_s3 alpha_count_s1 alpha_count_s3
      by simp
  qed
  have comp_lookup:
    "\<And>i. i < length fl \<Longrightarrow>
      fmlookup (HashMap query_state)
        (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
              as)
            dg)
          (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i))"
  proof -
    fix i
    assume i_bound: "i < length fl"
    have lookup_s7:
      "fmlookup (HashMap s7)
        (CompositionFriChallenge (PCompositionFriCounter s6 + i)
          (foldl concat (PState s6) (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i))"
      using comp_fri_res i_bound by simp
    show "fmlookup (HashMap query_state)
        (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
              as)
            dg)
          (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i))"
      using hash_extension_lookup[OF lookup_s7 ext_s7_query']
        st_s1 trace_fri_res st_s3 alpha_res st_s5 s6_eq
        comp_count_s1 comp_count_s3 comp_count_s5
      by simp
  qed
  have query_count_header:
    "PQueryCounter query_state = PQueryCounter s"
    using query_count_s1 trace_fri_res query_count_s3 alpha_res query_count_s5
      s6_eq comp_fri_res query_count_query
    by simp
  show ?thesis
    by (rule that[OF header_tr header_state query_out query_count_header
        ext_s_query trace_lookup alpha_lookup comp_lookup degree_bound])
qed

lemma verify_monad_random_oracle_key_extraction:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
  obtains fr :: 'f
      and f_fl :: "('f \<times> 'f) list"
      and f_final :: 'f
      and as :: "'f list"
      and dg :: 'f
      and fl :: "('f \<times> 'f) list"
      and final :: 'f
      and query_state :: "('f, 'a) protocol_channel_scheme"
      and raw_idxs :: "'f list"
      and query_idxs :: "nat list"
      and query_chunks :: "'f list list"
  where
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    and "PState query_state =
      verifier_header_state s fr (map snd f_fl) f_final as dg (map snd fl) final"
    and "length raw_idxs = rounds"
    and "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and "length query_chunks = rounds"
    and "PTranscript query_state =
      List.concat query_chunks @ PTranscript final_state"
    and "\<And>i. i < length f_fl \<Longrightarrow>
      fmlookup (HashMap query_state)
        (TraceFriChallenge
          (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))"
    and "\<And>i. i < length as \<Longrightarrow>
      fmlookup (HashMap query_state)
        (AlphaChallenge (PAlphaCounter s + i) (foldl concat
          (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
          (take i as))) =
        Some (as ! i)"
    and "\<And>i. i < length fl \<Longrightarrow>
      fmlookup (HashMap query_state)
        (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
              as)
            dg)
          (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i))"
    and "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (query_idxs ! i)
        (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge
          (PQueryCounter query_state + i) (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    and "\<And>idx. idx \<in> set query_idxs \<Longrightarrow> idx < clength * scale"
proof -
  from verify_monad_header_random_oracle_replay[OF outcome]
  obtain fr f_fl f_final as dg fl final query_state where
    header:
      "verifier_header_transcript s fr (map snd f_fl) f_final as dg
        (map snd fl) final (PTranscript query_state)"
    and header_state:
      "PState query_state =
        verifier_header_state s fr (map snd f_fl) f_final as dg
          (map snd fl) final"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist (execute
          (ntimes (verifier_query_round_program fr f_fl f_final as fl final) rounds)
          query_state)"
    and query_count_header:
      "PQueryCounter query_state = PQueryCounter s"
    and ext_s_query_header: "s \<le> query_state"
    and trace_lookup:
      "\<And>i. i < length f_fl \<Longrightarrow>
        fmlookup (HashMap query_state)
          (TraceFriChallenge
            (PTraceFriCounter s + i) (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
          Some (fst (f_fl ! i))"
    and alpha_lookup:
      "\<And>i. i < length as \<Longrightarrow>
        fmlookup (HashMap query_state)
          (AlphaChallenge (PAlphaCounter s + i) (foldl concat
            (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
            (take i as))) =
          Some (as ! i)"
    and comp_lookup:
      "\<And>i. i < length fl \<Longrightarrow>
        fmlookup (HashMap query_state)
          (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
            (concat
              (foldl concat
                (concat
                  (foldl concat (concat (PState s) fr) (map snd f_fl))
                  f_final)
                as)
              dg)
            (take (Suc i) (map snd fl)))) =
          Some (fst (fl ! i))"
    and degree_bound: "to_nat dg \<le> maxDegree"
    by blast
  from ntimes_verifier_query_rounds_outcome[OF query_out]
  obtain raw_idxs query_idxs query_chunks where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_def: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and tr_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and round_chunks:
      "\<forall>i < rounds.
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and query_lookup:
      "\<forall>i < rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge
            (PQueryCounter query_state + i) (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    and idx_bounds: "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by blast
  show ?thesis
  proof (rule that[of fr f_fl f_final as dg fl final query_state
        raw_idxs query_idxs query_chunks])
    show "verifier_header_transcript s fr (map snd f_fl) f_final as dg
        (map snd fl) final (PTranscript query_state)"
      by (rule header)
  next
    show "PState query_state =
        verifier_header_state s fr (map snd f_fl) f_final as dg
          (map snd fl) final"
      by (rule header_state)
  next
    show "length raw_idxs = rounds"
      by (rule len_raw)
  next
    show "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
      by (rule query_idxs_def)
  next
    show "length query_chunks = rounds"
      by (rule len_chunks)
  next
    show "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
      by (rule tr_query)
  next
    fix i
    assume "i < length f_fl"
    then show "fmlookup (HashMap query_state)
        (TraceFriChallenge
          (PTraceFriCounter s + i)
          (foldl concat (concat (PState s) fr)
            (take (Suc i) (map snd f_fl)))) =
        Some (fst (f_fl ! i))"
      by (rule trace_lookup)
  next
    fix i
    assume "i < length as"
    then show "fmlookup (HashMap query_state)
        (AlphaChallenge (PAlphaCounter s + i) (foldl concat
          (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
          (take i as))) =
        Some (as ! i)"
      by (rule alpha_lookup)
  next
    fix i
    assume "i < length fl"
    then show "fmlookup (HashMap query_state)
        (CompositionFriChallenge (PCompositionFriCounter s + i) (foldl concat
          (concat
            (foldl concat
              (concat (foldl concat (concat (PState s) fr) (map snd f_fl)) f_final)
              as)
            dg)
          (take (Suc i) (map snd fl)))) =
        Some (fst (fl ! i))"
      by (rule comp_lookup)
  next
    fix i
    assume "i < rounds"
    then show "verifier_query_round_chunk (query_idxs ! i)
        (map snd f_fl) (map snd fl) (query_chunks ! i)"
      using round_chunks by blast
  next
    fix i
    assume "i < rounds"
    then show "fmlookup (HashMap final_state)
        (QueryIndexChallenge
          (PQueryCounter query_state + i) (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
      using query_lookup by blast
  next
    fix idx
    assume "idx \<in> set query_idxs"
    then show "idx < clength * scale"
      using idx_bounds by blast
  qed
qed

lemma verify_monad_accepted_transcript_shape:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
  shows "\<exists>alphas query_idxs.
    accepted_transcript_shape s (Some (result, final_state)) alphas query_idxs"
proof -
  from verify_monad_header_extraction[OF outcome]
  obtain fr f_fl f_final as dg fl final query_state where
    header:
      "verifier_header_transcript s fr (map snd f_fl) f_final as dg
        (map snd fl) final (PTranscript query_state)"
    and header_state:
      "PState query_state =
        verifier_header_state s fr (map snd f_fl) f_final as dg (map snd fl) final"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist (execute
          (ntimes (verifier_query_round_program fr f_fl f_final as fl final) rounds)
          query_state)"
    and query_count_header:
      "PQueryCounter query_state = PQueryCounter s"
    and len_f_fl: "length f_fl = ceil_log clength"
    and len_as: "length as = length spec"
    and len_fl: "length fl = ceil_log (to_nat dg + 1)"
    by blast
  from ntimes_verifier_query_rounds_outcome[OF query_out]
  obtain raw_idxs query_idxs query_chunks where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_def: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and tr_query:
      "PTranscript query_state = List.concat query_chunks @ PTranscript final_state"
    and round_chunks:
      "\<forall>i < rounds.
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and lookups:
      "\<forall>i < rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i) (state_after_query_chunks (PState query_state) query_chunks i)) =
          Some (raw_idxs ! i)"
    and idx_bounds: "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by auto
  have derived:
    "verifier_query_indices_derived s (Some (result, final_state))
      (verifier_header_state s fr (map snd f_fl) f_final as dg (map snd fl) final)
      (PTranscript query_state) (map snd f_fl) (map snd fl) query_idxs"
  proof -
    have tr_query':
      "List.concat query_chunks @ PTranscript final_state = PTranscript query_state"
      using tr_query by simp
    have lookups':
      "\<forall>i<rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter s + i) (state_after_query_chunks
            (verifier_header_state s fr (map snd f_fl) f_final as dg (map snd fl) final)
            query_chunks i)) =
        Some (raw_idxs ! i)"
      using lookups header_state query_count_header by simp
    show ?thesis
      unfolding verifier_query_indices_derived_def
      apply (rule exI[where x=result])
      apply (rule exI[where x=final_state])
      apply (rule exI[where x=raw_idxs])
      apply (rule exI[where x=query_chunks])
      apply (rule exI[where x="PTranscript final_state"])
      apply (intro conjI)
              apply simp
             apply (rule len_raw)
           apply (rule query_idxs_def)
          apply (rule len_chunks)
         apply (rule tr_query')
        apply (rule round_chunks)
       apply (rule lookups')
      apply (rule idx_bounds)
      done
  qed
  have shape:
    "accepted_transcript_shape s (Some (result, final_state)) as query_idxs"
    unfolding accepted_transcript_shape_def
    apply (rule exI[where x=result])
    apply (rule exI[where x=final_state])
    apply (rule exI[where x=fr])
    apply (rule exI[where x="map snd f_fl"])
    apply (rule exI[where x=f_final])
    apply (rule exI[where x=dg])
    apply (rule exI[where x="map snd fl"])
    apply (rule exI[where x=final])
    apply (rule exI[where x="PTranscript query_state"])
    apply (intro conjI)
      apply simp
     apply (rule header)
    apply (rule derived)
    done
  show ?thesis
    using shape by blast
qed

lemma verify_monad_supplied_header_transcript_shape:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header0:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  obtains query_idxs raw_idxs query_chunks where
    "accepted_transcript_shape s (Some (result, final_state)) as query_idxs"
    "length raw_idxs = rounds"
    "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    "length query_chunks = rounds"
    "List.concat query_chunks @ PTranscript final_state = rest"
    "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (query_idxs ! i)
        f_fri_roots composition_fri_roots (query_chunks ! i)"
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter s + i)
          (state_after_query_chunks
            (verifier_header_state s fr f_fri_roots f_final as dg
              composition_fri_roots final)
            query_chunks i)) =
      Some (raw_idxs ! i)"
proof -
  from verify_monad_header_extraction[OF outcome]
  obtain fr' f_fl f_final' as' dg' fl final' query_state where
    header:
      "verifier_header_transcript s fr' (map snd f_fl) f_final' as' dg'
        (map snd fl) final' (PTranscript query_state)"
    and header_state:
      "PState query_state =
        verifier_header_state s fr' (map snd f_fl) f_final' as' dg'
          (map snd fl) final'"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr' f_fl f_final' as' fl
                final') rounds)
            query_state)"
    and query_count_header:
      "PQueryCounter query_state = PQueryCounter s"
    by metis
  have eqs:
    "fr' = fr \<and>
     map snd f_fl = f_fri_roots \<and>
     f_final' = f_final \<and>
     as' = as \<and>
     dg' = dg \<and>
     map snd fl = composition_fri_roots \<and>
     final' = final \<and>
     PTranscript query_state = rest"
    using verifier_header_transcript_unique[OF header header0] by simp
  from ntimes_verifier_query_rounds_outcome[OF query_out]
  obtain raw_idxs query_idxs query_chunks where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and tr_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and chunks:
      "\<forall>i < rounds.
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and lookups:
      "\<forall>i < rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    and idx_bounds: "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by blast
  have tr_query':
    "List.concat query_chunks @ PTranscript final_state = rest"
    using tr_query eqs by simp
  have chunks':
    "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (query_idxs ! i)
        f_fri_roots composition_fri_roots (query_chunks ! i)"
    using chunks eqs by simp
  have lookups':
    "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter s + i)
          (state_after_query_chunks
            (verifier_header_state s fr f_fri_roots f_final as dg
              composition_fri_roots final)
            query_chunks i)) =
      Some (raw_idxs ! i)"
    using lookups header_state query_count_header eqs by simp
  have derived:
    "verifier_query_indices_derived s (Some (result, final_state))
      (verifier_header_state s fr f_fri_roots f_final as dg
        composition_fri_roots final)
      rest f_fri_roots composition_fri_roots query_idxs"
    unfolding verifier_query_indices_derived_def
    by (intro exI[of _ result] exI[of _ final_state]
        exI[of _ raw_idxs] exI[of _ query_chunks]
        exI[of _ "PTranscript final_state"] conjI)
      (use len_raw query_idxs_eq len_chunks tr_query' chunks' lookups'
        idx_bounds in auto)
  have shape:
    "accepted_transcript_shape s (Some (result, final_state)) as query_idxs"
    unfolding accepted_transcript_shape_def
    by (intro exI[of _ result] exI[of _ final_state] exI[of _ fr]
        exI[of _ f_fri_roots] exI[of _ f_final] exI[of _ dg]
        exI[of _ composition_fri_roots] exI[of _ final]
        exI[of _ rest] conjI)
      (use header0 derived in simp_all)
  show ?thesis
    by (rule that[OF shape len_raw query_idxs_eq len_chunks tr_query'
          chunks' lookups'])
qed

lemma verify_monad_supplied_header_query_rounds:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header0:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
  obtains f_fl fl query_state where
    "map snd f_fl = f_fri_roots"
    "map snd fl = composition_fri_roots"
    "PTranscript query_state = rest"
    "PState query_state =
      verifier_header_state s fr f_fri_roots f_final as dg
        composition_fri_roots final"
    "PQueryCounter query_state = PQueryCounter s"
    "Some (result, final_state) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          query_state)"
proof -
  from verify_monad_header_extraction[OF outcome]
  obtain fr' f_fl f_final' as' dg' fl final' query_state where
    header:
      "verifier_header_transcript s fr' (map snd f_fl) f_final' as' dg'
        (map snd fl) final' (PTranscript query_state)"
    and header_state:
      "PState query_state =
        verifier_header_state s fr' (map snd f_fl) f_final' as' dg'
          (map snd fl) final'"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr' f_fl f_final' as' fl
                final') rounds)
            query_state)"
    and query_count_header:
      "PQueryCounter query_state = PQueryCounter s"
    by metis
  have eqs:
    "fr' = fr \<and>
     map snd f_fl = f_fri_roots \<and>
     f_final' = f_final \<and>
     as' = as \<and>
     dg' = dg \<and>
     map snd fl = composition_fri_roots \<and>
     final' = final \<and>
     PTranscript query_state = rest"
    using verifier_header_transcript_unique[OF header header0] by simp
  show ?thesis
    by (rule that[of f_fl fl query_state])
      (use eqs header_state query_count_header query_out in simp_all)
qed

lemma verify_monad_supplied_empty_header_query_rounds:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header0:
      "verifier_header_transcript s fr f_fri_roots f_final as dg []
        final rest"
  obtains f_fl query_state where
    "map snd f_fl = f_fri_roots"
    "PTranscript query_state = rest"
    "PState query_state =
      verifier_header_state s fr f_fri_roots f_final as dg [] final"
    "PQueryCounter query_state = PQueryCounter s"
    "Some (result, final_state) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as [] final)
            rounds)
          query_state)"
proof -
  from verify_monad_supplied_header_query_rounds[OF outcome header0]
  obtain f_fl fl query_state where f_roots:
      "map snd f_fl = f_fri_roots"
    and fl_roots: "map snd fl = []"
    and tr: "PTranscript query_state = rest"
    and st:
      "PState query_state =
        verifier_header_state s fr f_fri_roots f_final as dg [] final"
    and qc: "PQueryCounter query_state = PQueryCounter s"
    and out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    by blast
  have fl_empty: "fl = []"
    using fl_roots by (cases fl) simp_all
  show ?thesis
    by (rule that[of f_fl query_state])
      (use f_roots tr st qc out fl_empty in simp_all)
qed

lemma verifier_after_alpha_accepted_transcript_shape:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((fr, f_fl, f_final, as), prefix_state) \<in>
      set_dist (execute verifier_alpha_prefix s)"
    and suffix:
      "Some (result, final_state) \<in>
        set_dist
          (execute (verifier_after_alpha (fr, f_fl, f_final, as))
            prefix_state)"
  shows "\<exists>query_idxs.
    accepted_transcript_shape s (Some (result, final_state)) as query_idxs"
proof -
  have prefix_res:
    "length f_fl = ceil_log clength \<and>
     length as = length spec \<and>
     PTranscript s =
       [fr] @ map snd f_fl @ [f_final] @ as @ PTranscript prefix_state \<and>
     PState prefix_state =
       foldl concat
        (concat (foldl concat (concat (PState s) fr) (map snd f_fl))
          f_final)
        as \<and>
     PQueryCounter prefix_state = PQueryCounter s"
    by (rule verifier_alpha_prefix_outcome[OF prefix])
  from suffix obtain dg s5 s6 fl s7 final query_state where
    read_dg: "Some (dg, s5) \<in> set_dist (execute read prefix_state)"
    and degree_assert:
      "Some ((), s6) \<in>
        set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
    and comp_fri:
      "Some (fl, s7) \<in>
        set_dist (execute
          (ntimes receive_composition_fri_commits
            (ceil_log (to_nat dg + 1))) s6)"
    and read_final: "Some (final, query_state) \<in> set_dist (execute read s7)"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist (execute
          (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
            rounds)
          query_state)"
    unfolding verifier_after_alpha_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_dg] obtain rest5 where
    tr_prefix: "PTranscript prefix_state = dg # rest5"
    and st_s5: "PState s5 = concat (PState prefix_state) dg"
    and tr_s5: "PTranscript s5 = rest5"
    and query_count_s5: "PQueryCounter s5 = PQueryCounter prefix_state"
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
    and st_query: "PState query_state = concat (PState s7) final"
    and tr_query: "PTranscript query_state = rest_query"
    and query_count_query: "PQueryCounter query_state = PQueryCounter s7"
    by blast
  have header:
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    using prefix_res tr_prefix tr_s5 s6_eq comp_res tr_s7 tr_query
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
  have header_state:
    "PState query_state =
      verifier_header_state s fr (map snd f_fl) f_final as dg
        (map snd fl) final"
    using prefix_res st_s5 s6_eq comp_res st_query
    unfolding verifier_header_state_def verifier_header_messages_def
    by simp
  have query_count_header:
    "PQueryCounter query_state = PQueryCounter s"
    using prefix_res query_count_s5 s6_eq comp_res query_count_query
    by simp
  from ntimes_verifier_query_rounds_outcome[OF query_out]
  obtain raw_idxs query_idxs query_chunks where
    len_raw: "length raw_idxs = rounds"
    and query_idxs_def: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length query_chunks = rounds"
    and tr_query_rounds:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and round_chunks:
      "\<forall>i < rounds.
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and lookups:
      "\<forall>i < rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
          Some (raw_idxs ! i)"
    and idx_bounds: "\<forall>idx \<in> set query_idxs. idx < clength * scale"
    by blast
  have derived:
    "verifier_query_indices_derived s (Some (result, final_state))
      (verifier_header_state s fr (map snd f_fl) f_final as dg
        (map snd fl) final)
      (PTranscript query_state) (map snd f_fl) (map snd fl) query_idxs"
  proof -
    have tr_query_rounds':
      "List.concat query_chunks @ PTranscript final_state =
        PTranscript query_state"
      using tr_query_rounds by simp
    have lookups':
      "\<forall>i<rounds.
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks
              (verifier_header_state s fr (map snd f_fl) f_final as dg
                (map snd fl) final)
              query_chunks i)) =
          Some (raw_idxs ! i)"
      using lookups header_state query_count_header by simp
    show ?thesis
      unfolding verifier_query_indices_derived_def
      apply (rule exI[where x=result])
      apply (rule exI[where x=final_state])
      apply (rule exI[where x=raw_idxs])
      apply (rule exI[where x=query_chunks])
      apply (rule exI[where x="PTranscript final_state"])
      apply (intro conjI)
              apply simp
             apply (rule len_raw)
            apply (rule query_idxs_def)
           apply (rule len_chunks)
          apply (rule tr_query_rounds')
         apply (rule round_chunks)
        apply (rule lookups')
       apply (rule idx_bounds)
      done
  qed
  have shape:
    "accepted_transcript_shape s (Some (result, final_state)) as query_idxs"
    unfolding accepted_transcript_shape_def
    apply (rule exI[where x=result])
    apply (rule exI[where x=final_state])
    apply (rule exI[where x=fr])
    apply (rule exI[where x="map snd f_fl"])
    apply (rule exI[where x=f_final])
    apply (rule exI[where x=dg])
    apply (rule exI[where x="map snd fl"])
    apply (rule exI[where x=final])
    apply (rule exI[where x="PTranscript query_state"])
    apply (intro conjI)
      apply simp
     apply (rule header)
    apply (rule derived)
    done
  show ?thesis
    using shape by blast
qed

lemma verifier_after_alpha_accepted_transcript_header:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes prefix:
    "Some ((fr, f_fl, f_final, as), prefix_state) \<in>
      set_dist (execute verifier_alpha_prefix s)"
    and suffix:
      "Some (result, final_state) \<in>
        set_dist
          (execute (verifier_after_alpha (fr, f_fl, f_final, as))
            prefix_state)"
  obtains dg composition_fri_roots final rest query_idxs
  where
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      composition_fri_roots final rest"
    and "accepted_transcript_shape s (Some (result, final_state))
      as query_idxs"
proof -
  have prefix_res:
    "length f_fl = ceil_log clength \<and>
     length as = length spec \<and>
     PTranscript s =
       [fr] @ map snd f_fl @ [f_final] @ as @ PTranscript prefix_state"
    using verifier_alpha_prefix_outcome[OF prefix] by simp
  from suffix obtain dg s5 s6 fl s7 final query_state where
    read_dg: "Some (dg, s5) \<in> set_dist (execute read prefix_state)"
    and degree_assert:
      "Some ((), s6) \<in>
        set_dist (execute (assert (to_nat dg \<le> maxDegree)) s5)"
    and comp_fri:
      "Some (fl, s7) \<in>
        set_dist (execute
          (ntimes receive_composition_fri_commits
            (ceil_log (to_nat dg + 1))) s6)"
    and read_final: "Some (final, query_state) \<in> set_dist (execute read s7)"
    unfolding verifier_after_alpha_def
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_dg] obtain rest5 where
    tr_prefix: "PTranscript prefix_state = dg # rest5"
    and tr_s5: "PTranscript s5 = rest5"
    by blast
  have s6_eq: "s6 = s5"
    using degree_assert unfolding assert_def
    by (cases "to_nat dg \<le> maxDegree") (auto simp: throw_no_outcome)
  have comp_res:
    "length fl = ceil_log (to_nat dg + 1) \<and>
     PTranscript s6 = map snd fl @ PTranscript s7"
    using ntimes_receive_composition_fri_commits_outcome[OF comp_fri]
    by simp
  from read_outcome[OF read_final] obtain rest_query where
    tr_s7: "PTranscript s7 = final # rest_query"
    and tr_query: "PTranscript query_state = rest_query"
    by blast
  have header:
    "verifier_header_transcript s fr (map snd f_fl) f_final as dg
      (map snd fl) final (PTranscript query_state)"
    using prefix_res tr_prefix tr_s5 s6_eq comp_res tr_s7 tr_query
    unfolding verifier_header_transcript_def verifier_header_messages_def
    by simp
  from verifier_after_alpha_accepted_transcript_shape[OF prefix suffix]
  obtain query_idxs where shape:
    "accepted_transcript_shape s (Some (result, final_state)) as query_idxs"
    by blast
  show ?thesis
    by (rule that[of dg "map snd fl" final "PTranscript query_state" query_idxs,
          OF header shape])
qed

lemma verify_monad_merkle_bound_witnesses:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes bind: "initial_merkle_binding_no_bad s"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
  shows "\<exists>trace_table composition_table alphas query_idxs.
    accepted_with_bound_tables s (Some (result, final_state))
      trace_table composition_table alphas query_idxs"
proof -
  from verify_monad_accepted_transcript_shape[OF outcome]
  obtain alphas query_idxs where
    shape:
      "accepted_transcript_shape s (Some (result, final_state)) alphas query_idxs"
    by blast
  from initial_merkle_binding_no_badE[OF bind outcome shape]
  obtain trace_table composition_table where
    bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table alphas query_idxs"
    by blast
  show ?thesis
    using bound by blast
qed

lemma verify_monad_merkle_bound_tables:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes bind: "initial_merkle_binding_no_bad s"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
  obtains trace_table composition_table alphas query_idxs
  where
    "accepted_with_bound_tables s (Some (result, final_state))
      trace_table composition_table alphas query_idxs"
    and "accepted_with_tables s (Some (result, final_state))
      trace_table composition_table alphas query_idxs"
    and "\<And>idx. idx \<in> set query_idxs \<Longrightarrow>
      query_consistent_at trace_table composition_table alphas idx"
    and "\<exists>fr composition_root.
      merkle_root_binds_table fr trace_table final_state \<and>
      merkle_root_binds_table composition_root composition_table final_state"
proof -
  from verify_monad_merkle_bound_witnesses[OF bind outcome]
  obtain trace_table composition_table alphas query_idxs where
    bound:
      "accepted_with_bound_tables s (Some (result, final_state))
        trace_table composition_table alphas query_idxs"
    by blast
  have tables:
    "accepted_with_tables s (Some (result, final_state))
      trace_table composition_table alphas query_idxs"
    by (rule accepted_with_bound_tables_imp_accepted_with_tables[OF bound])
  have query_cons:
    "\<And>idx. idx \<in> set query_idxs \<Longrightarrow>
      query_consistent_at trace_table composition_table alphas idx"
    by (rule accepted_with_bound_tables_query_consistency[OF bound])
  have roots:
    "\<exists>fr composition_root.
      merkle_root_binds_table fr trace_table final_state \<and>
      merkle_root_binds_table composition_root composition_table final_state"
    using accepted_with_bound_tables_bound_roots[OF bound] by blast
  show ?thesis
    by (rule that[OF bound tables query_cons roots])
qed

lemma verifier_query_indices_derivedE:
  assumes "verifier_query_indices_derived s out query_start_state rest
    f_fri_roots composition_fri_roots query_idxs"
  obtains result final_state raw_idxs query_chunks trailing
  where "out = Some (result, final_state)"
    and "length raw_idxs = rounds"
    and "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and "length query_chunks = rounds"
    and "List.concat query_chunks @ trailing = rest"
    and "\<And>i. i < rounds \<Longrightarrow>
      verifier_query_round_chunk (query_idxs ! i)
        f_fri_roots composition_fri_roots (query_chunks ! i)"
    and "\<And>i. i < rounds \<Longrightarrow>
      fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter s + i)
          (state_after_query_chunks query_start_state query_chunks i)) =
        Some (raw_idxs ! i)"
    and "\<And>idx. idx \<in> set query_idxs \<Longrightarrow> idx < clength * scale"
  using assms unfolding verifier_query_indices_derived_def by blast

lemma accepted_transcript_shape_header_query_extraction:
  assumes "accepted_transcript_shape s out alphas query_idxs"
  obtains result final_state fr f_fri_roots f_final dg composition_fri_roots final rest
  where "out = Some (result, final_state)"
    and "verifier_header_transcript s fr f_fri_roots f_final alphas dg
      composition_fri_roots final rest"
    and "verifier_query_indices_derived s out
      (verifier_header_state s fr f_fri_roots f_final alphas dg composition_fri_roots final)
      rest f_fri_roots composition_fri_roots query_idxs"
  using assms unfolding accepted_transcript_shape_def by blast

lemma accepted_transcript_shape_alphas_unique:
  assumes shape1: "accepted_transcript_shape s out alphas query_idxs"
    and shape2: "accepted_transcript_shape s out alphas' query_idxs'"
  shows "alphas' = alphas"
proof -
  from shape1 obtain result final_state fr f_fri_roots f_final dg
      composition_fri_roots final rest where
    out1: "out = Some (result, final_state)"
    and header1:
      "verifier_header_transcript s fr f_fri_roots f_final alphas dg
        composition_fri_roots final rest"
    by (elim accepted_transcript_shape_header_query_extraction)
  from shape2 obtain result' final_state' fr' f_fri_roots' f_final' dg'
      composition_fri_roots' final' rest' where
    out2: "out = Some (result', final_state')"
    and header2:
      "verifier_header_transcript s fr' f_fri_roots' f_final' alphas' dg'
        composition_fri_roots' final' rest'"
    by (elim accepted_transcript_shape_header_query_extraction)
  show ?thesis
    using verifier_header_transcript_unique[OF header1 header2] by simp
qed

lemma accepted_with_bound_tables_alphas_unique:
  assumes bound1:
      "accepted_with_bound_tables s out trace_table composition_table
        alphas query_idxs"
    and bound2:
      "accepted_with_bound_tables s out trace_table' composition_table'
        alphas' query_idxs'"
  shows "alphas' = alphas"
proof -
  have shape1: "accepted_transcript_shape s out alphas query_idxs"
    using bound1 unfolding accepted_with_bound_tables_def
      accepted_with_tables_def by simp
  have shape2: "accepted_transcript_shape s out alphas' query_idxs'"
    using bound2 unfolding accepted_with_bound_tables_def
      accepted_with_tables_def by simp
  show ?thesis
    by (rule accepted_transcript_shape_alphas_unique[OF shape1 shape2])
qed

lemma wp_verify_monad_alpha_list_set_bound:
  assumes future: "alpha_future_fresh s"
    and subset: "B \<subseteq> alpha_space"
  shows
    "wp_event verify_monad (alpha_list_set_hit s B) s \<le>
      nnreal (card B) / nnreal (card alpha_space)"
proof -
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((_, _, _, as), _) \<Rightarrow> as \<in> B"
  have prefix_bound:
    "wp_event verifier_alpha_prefix ?Head s \<le>
      nnreal (card B) / nnreal (card alpha_space)"
    by (rule wp_verifier_alpha_prefix_alpha_space_set_bound
        [OF future subset])
  show ?thesis
    unfolding verify_monad_alpha_decomposition
  proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
    show "alpha_list_set_hit s B None \<Longrightarrow> ?Head None"
      unfolding alpha_list_set_hit_def accepted_transcript_shape_def by blast
  next
    fix header prefix_state out
    assume prefix:
      "Some (header, prefix_state) \<in>
        set_dist (execute verifier_alpha_prefix s)"
      and suffix:
        "out \<in>
          set_dist (execute (verifier_after_alpha header) prefix_state)"
      and hit: "alpha_list_set_hit s B out"
    obtain fr f_fl f_final as where header_eq:
      "header = (fr, f_fl, f_final, as)"
      by (cases header) auto
    from hit obtain as' query_idxs where
      shape_hit: "accepted_transcript_shape s out as' query_idxs"
      and as'_B: "as' \<in> B"
      unfolding alpha_list_set_hit_def by blast
    from shape_hit obtain result final_state where out_eq:
      "out = Some (result, final_state)"
      unfolding accepted_transcript_shape_def by blast
    have prefix':
      "Some ((fr, f_fl, f_final, as), prefix_state) \<in>
        set_dist (execute verifier_alpha_prefix s)"
      using prefix header_eq by simp
    have suffix':
      "Some (result, final_state) \<in>
        set_dist
          (execute (verifier_after_alpha (fr, f_fl, f_final, as))
            prefix_state)"
      using suffix header_eq out_eq by simp
    from verifier_after_alpha_accepted_transcript_shape[OF prefix' suffix']
    obtain query_idxs' where
      shape_prefix:
        "accepted_transcript_shape s (Some (result, final_state))
          as query_idxs'"
      by blast
    have "as' = as"
      by (rule accepted_transcript_shape_alphas_unique
          [OF shape_prefix shape_hit[unfolded out_eq]])
    then show "?Head (Some (header, prefix_state))"
      using as'_B header_eq by simp
  qed
qed

lemma wp_verify_monad_alpha_header_list_set_bound:
  fixes C :: prob
  assumes future: "alpha_future_fresh s"
    and subset:
      "\<And>fr f_fri_roots f_final.
        B fr f_fri_roots f_final \<subseteq> alpha_space"
    and bound:
      "\<And>fr f_fri_roots f_final.
        nnreal (card (B fr f_fri_roots f_final)) /
          nnreal (card alpha_space) \<le> C"
  shows
    "wp_event verify_monad (alpha_header_list_set_hit s B) s \<le> C"
proof -
  let ?Head =
    "\<lambda>out. case out of
        None \<Rightarrow> False
      | Some ((fr, f_fl, f_final, as), _) \<Rightarrow>
          as \<in> B fr (map snd f_fl) f_final"
  have prefix_bound:
    "wp_event verifier_alpha_prefix ?Head s \<le> C"
    by (rule wp_verifier_alpha_prefix_dependent_alpha_space_set_bound
        [OF future])
      (use subset bound in simp_all)
  show ?thesis
    unfolding verify_monad_alpha_decomposition
  proof (rule wp_event_bind_bound_by_head_event[OF prefix_bound])
    show "alpha_header_list_set_hit s B None \<Longrightarrow> ?Head None"
      unfolding alpha_header_list_set_hit_def
        accepted_transcript_shape_def by blast
  next
    fix header prefix_state out
    assume prefix:
      "Some (header, prefix_state) \<in>
        set_dist (execute verifier_alpha_prefix s)"
      and suffix:
        "out \<in>
          set_dist (execute (verifier_after_alpha header) prefix_state)"
      and hit: "alpha_header_list_set_hit s B out"
    obtain fr f_fl f_final as where header_eq:
      "header = (fr, f_fl, f_final, as)"
      by (cases header) auto
    from hit obtain as' query_idxs result final_state fr' f_fri_roots'
        f_final' dg' composition_fri_roots' final' rest' where
      shape_hit:
        "accepted_transcript_shape s out as' query_idxs"
      and out_eq: "out = Some (result, final_state)"
      and header_hit:
        "verifier_header_transcript s fr' f_fri_roots' f_final' as' dg'
          composition_fri_roots' final' rest'"
      and as'_B: "as' \<in> B fr' f_fri_roots' f_final'"
      unfolding alpha_header_list_set_hit_def by blast
    have prefix':
      "Some ((fr, f_fl, f_final, as), prefix_state) \<in>
        set_dist (execute verifier_alpha_prefix s)"
      using prefix header_eq by simp
    have suffix':
      "Some (result, final_state) \<in>
        set_dist
          (execute (verifier_after_alpha (fr, f_fl, f_final, as))
            prefix_state)"
      using suffix header_eq out_eq by simp
    from verifier_after_alpha_accepted_transcript_header[OF prefix' suffix']
    obtain dg composition_fri_roots final rest query_idxs' where
      header_prefix:
        "verifier_header_transcript s fr (map snd f_fl) f_final as dg
          composition_fri_roots final rest"
      and shape_prefix:
        "accepted_transcript_shape s (Some (result, final_state))
          as query_idxs'"
      by metis
    have unique_header:
      "fr' = fr \<and>
       f_fri_roots' = map snd f_fl \<and>
       f_final' = f_final \<and>
       as' = as"
      using verifier_header_transcript_unique[OF header_prefix header_hit]
      by simp
    then show "?Head (Some (header, prefix_state))"
      using as'_B header_eq by simp
  qed
qed

lemma wp_alpha_bad_set_hit_bound_via_header_union:
  fixes C :: prob
  assumes future: "alpha_future_fresh s"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and union_bound:
      "\<And>fr f_fri_roots f_final.
        nnreal
          (card
            (alpha_header_union_bad_sets s bad_sets fr f_fri_roots f_final)) /
          nnreal (card alpha_space) \<le> C"
  shows "wp_event verify_monad (alpha_bad_set_hit s bad_sets) s \<le> C"
proof -
  have header_bound:
    "wp_event verify_monad
      (alpha_header_list_set_hit s
        (alpha_header_union_bad_sets s bad_sets)) s \<le> C"
    by (rule wp_verify_monad_alpha_header_list_set_bound[OF future])
      (use alpha_header_union_bad_sets_subset_alpha_space union_bound in
        simp_all)
  have "wp_event verify_monad (alpha_bad_set_hit s bad_sets) s \<le>
      wp_event verify_monad
        (alpha_header_list_set_hit s
          (alpha_header_union_bad_sets s bad_sets)) s"
    by (rule wp_event_mono)
      (rule alpha_bad_set_hit_imp_alpha_header_union_bad_set_hit[OF _ subset])
  also have "... \<le> C"
    by (rule header_bound)
  finally show ?thesis .
qed

lemma wp_alpha_bad_set_hit_bound_via_supported_header_union:
  fixes C :: prob
  assumes future: "alpha_future_fresh s"
    and subset: "\<And>trace_table. bad_sets trace_table \<subseteq> alpha_space"
    and union_bound:
      "\<And>fr f_fri_roots f_final.
        nnreal
          (card
            (alpha_header_supported_union_bad_sets s bad_sets fr f_fri_roots
              f_final)) /
          nnreal (card alpha_space) \<le> C"
  shows "wp_event verify_monad (alpha_bad_set_hit s bad_sets) s \<le> C"
proof -
  have header_bound:
    "wp_event verify_monad
      (alpha_header_list_set_hit s
        (alpha_header_supported_union_bad_sets s bad_sets)) s \<le> C"
    by (rule wp_verify_monad_alpha_header_list_set_bound[OF future])
      (use alpha_header_supported_union_bad_sets_subset_alpha_space
        union_bound in simp_all)
  have "wp_event verify_monad (alpha_bad_set_hit s bad_sets) s \<le>
      wp_event verify_monad
        (alpha_header_list_set_hit s
          (alpha_header_supported_union_bad_sets s bad_sets)) s"
    by (rule wp_event_mono_on_support)
      (rule alpha_bad_set_hit_imp_alpha_header_supported_union_bad_set_hit
        [OF _ _ subset])
  also have "... \<le> C"
    by (rule header_bound)
  finally show ?thesis .
qed

lemma accepted_with_tables_header_query_extraction:
  assumes "accepted_with_tables s out trace_table composition_table alphas query_idxs"
  obtains result final_state fr f_fri_roots f_final dg composition_fri_roots final rest
  where "out = Some (result, final_state)"
    and "verifier_header_transcript s fr f_fri_roots f_final alphas dg
      composition_fri_roots final rest"
    and "verifier_query_indices_derived s out
      (verifier_header_state s fr f_fri_roots f_final alphas dg composition_fri_roots final)
      rest f_fri_roots composition_fri_roots query_idxs"
    and "\<And>idx. idx \<in> set query_idxs \<Longrightarrow>
      query_consistent_at trace_table composition_table alphas idx"
    and "length trace_table = clength * scale"
    and "length composition_table = clength * scale"
    and "length alphas = length spec"
  using assms
  unfolding accepted_with_tables_def accepted_transcript_shape_def
  by blast

lemma accepted_with_tables_existential_witnesses:
  assumes "accepted_with_tables s out trace_table composition_table alphas query_idxs"
  shows "\<exists>trace_table composition_table as query_idxs.
    accepted_with_tables s out trace_table composition_table as query_idxs"
  using assms by blast

lemma accepted_transcript_shape_header_extraction:
  assumes shape: "accepted_transcript_shape s (Some (result, final_state)) alphas query_idxs"
  shows "\<exists>fr f_fri_roots f_final as dg composition_fri_roots final rest.
    verifier_header_transcript s fr f_fri_roots f_final as dg
      composition_fri_roots final rest"
  using shape unfolding accepted_transcript_shape_def by blast

lemma accepted_transcript_shape_query_indices_extraction:
  assumes shape: "accepted_transcript_shape s (Some (result, final_state)) alphas query_idxs"
  shows "\<exists>fr f_fri_roots f_final dg composition_fri_roots final rest.
    verifier_query_indices_derived s (Some (result, final_state))
      (verifier_header_state s fr f_fri_roots f_final alphas dg
        composition_fri_roots final)
      rest f_fri_roots composition_fri_roots query_idxs"
  using shape unfolding accepted_transcript_shape_def by blast

lemma accepted_with_tables_has_witnesses:
  assumes tables: "accepted_with_tables s (Some (result, final_state))
    trace_table composition_table alphas query_idxs"
  shows "\<exists>trace_table composition_table as query_idxs.
    accepted_with_tables s (Some (result, final_state))
      trace_table composition_table as query_idxs"
  using tables by blast

end

end
