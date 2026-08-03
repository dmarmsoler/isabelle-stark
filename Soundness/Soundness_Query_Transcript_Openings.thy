(*  Title:      Stark/Soundness_Query_Transcript_Openings.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Query_Transcript_Openings
  imports Soundness_Query_Opening_Consistency
begin

text \<open>
  Combined query-round extraction lemmas.

  The existing execution layer extracts transcript chunks and authenticated
  Merkle openings separately.  This layer keeps the witnesses coupled to the
  same verifier query-round execution, so downstream transcript-indexed
  reductions can use verifier-derived query indices.
\<close>

context soundness
begin

lemma verifier_query_round_program_outcome_with_authenticated_trace_openings:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some ((), t) \<in>
      set_dist
        (execute
          (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx chunk openings where
    "idx = index (to_nat raw)"
    "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    "PTranscript s = chunk @ PTranscript t"
    "PState t = foldl concat (PState s) chunk"
    "s \<le> t"
    "PQueryCounter t = Suc (PQueryCounter s)"
    "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) =
      Some raw"
    "length openings = length (powers_scaled idx)"
    "map opening_index openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) openings t"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    rand:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  let ?idx = "index (to_nat raw)"
  from tail obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s0)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold
            (?idx, cp_eval as fv (h ^ ?idx * shift), clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have rand_res:
    "s \<le> s0 \<and>
     PState s0 = PState s \<and>
     PTranscript s0 = PTranscript s \<and>
     fmlookup (HashMap s0)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF rand] .
  have rand_counter:
    "PQueryCounter s0 = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF rand] by simp
  from check_decommit_on_query_outcome[OF query_decommit]
  obtain query_paths query_chunk where
    query_chunk_shape:
      "query_decommitment_transcript ?idx fv query_paths query_chunk"
    and tr_s0: "PTranscript s0 = query_chunk @ PTranscript s1"
    and st_s1: "PState s1 = foldl concat (PState s0) query_chunk"
    and ext_s0_s1: "s0 \<le> s1"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s0"
    by blast
  from receive_query_commits_layers_outcome[OF trace_fri]
  obtain trace_layer_chunks trace_fri_chunk where
    trace_layers:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layer_chunks trace_fri_chunk"
    and tr_s1: "PTranscript s1 = trace_fri_chunk @ PTranscript s2"
    and st_s2: "PState s2 = foldl concat (PState s1) trace_fri_chunk"
    and ext_s1_s2: "s1 \<le> s2"
    and query_count_s2: "PQueryCounter s2 = PQueryCounter s1"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  from receive_query_commits_layers_outcome[OF comp_fri]
  obtain comp_layer_chunks comp_fri_chunk where
    comp_layers:
      "fri_layers_transcript (length fl) (clength * scale)
        comp_layer_chunks comp_fri_chunk"
    and tr_s3: "PTranscript s3 = comp_fri_chunk @ PTranscript s4"
    and st_s4: "PState s4 = foldl concat (PState s3) comp_fri_chunk"
    and ext_s3_s4: "s3 \<le> s4"
    and query_count_s4: "PQueryCounter s4 = PQueryCounter s3"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  let ?chunk = "query_chunk @ trace_fri_chunk @ comp_fri_chunk"
  have round_chunk:
    "verifier_query_round_chunk ?idx (map snd f_fl) (map snd fl) ?chunk"
    unfolding verifier_query_round_chunk_def
    apply (rule exI[where x=query_chunk])
    apply (rule exI[where x=trace_fri_chunk])
    apply (rule exI[where x=comp_fri_chunk])
    apply (rule exI[where x=fv])
    apply (rule exI[where x=query_paths])
    apply (rule exI[where x=trace_layer_chunks])
    apply (rule exI[where x=comp_layer_chunks])
    using query_chunk_shape trace_layers comp_layers
    by simp
  have tr_t: "PTranscript s = ?chunk @ PTranscript t"
    using rand_res tr_s0 tr_s1 tr_s3 s3_eq t_eq by simp
  have st_t: "PState t = foldl concat (PState s) ?chunk"
    using rand_res st_s1 st_s2 st_s4 s3_eq t_eq by simp
  have ext_s0_t: "s0 \<le> t"
    using ext_s0_s1 ext_s1_s2 ext_s3_s4 t_eq unfolding s3_eq
    by (meson hash_ext_trans)
  have ext_s_t: "s \<le> t"
    using rand_res ext_s0_t by (meson hash_ext_trans)
  have query_count_t: "PQueryCounter t = Suc (PQueryCounter s)"
    using rand_counter query_count_s1 query_count_s2 query_count_s4
    unfolding s3_eq t_eq by simp
  have lookup_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
  proof -
    let ?key = "QueryIndexChallenge (PQueryCounter s) (PState s)"
    have "fmlookup (HashMap s0) ?key = fmlookup (HashMap t) ?key"
      using ext_s0_t rand_res
      unfolding less_eq_hash_ext_def less_eq_fmap_def
      by (metis option.distinct(1))
    then show ?thesis
      using rand_res by simp
  qed
  from verifier_query_round_after_index_authenticated_trace_openings[OF tail]
  obtain idx' leaves openings where
    idx'_eq: "idx' = ?idx"
    and len_openings: "length openings = length (powers_scaled idx')"
    and idx_openings: "map opening_index openings = powers_scaled idx'"
    and table_t:
      "partial_authenticated_table fr (scale * clength) openings t"
    by blast
  show ?thesis
  proof (rule that)
    show "?idx = index (to_nat raw)"
      by simp
    show "verifier_query_round_chunk ?idx (map snd f_fl) (map snd fl)
        ?chunk"
      by (rule round_chunk)
    show "PTranscript s = ?chunk @ PTranscript t"
      by (rule tr_t)
    show "PState t = foldl concat (PState s) ?chunk"
      by (rule st_t)
    show "s \<le> t"
      by (rule ext_s_t)
    show "PQueryCounter t = Suc (PQueryCounter s)"
      by (rule query_count_t)
    show "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
      by (rule lookup_t)
    show "length openings = length (powers_scaled ?idx)"
      using idx'_eq len_openings by simp
    show "map opening_index openings = powers_scaled ?idx"
      using idx'_eq idx_openings by simp
    show "partial_authenticated_table fr (scale * clength) openings t"
      by (rule table_t)
  qed
qed

lemma ntimes_verifier_query_rounds_selected_trace_openings_aligned_with_replay_at:
  fixes query_state final_state :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              rounds)
            query_state)"
    and i_bound: "i < rounds"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
  obtains openings where
    "map opening_index openings = powers_scaled (query_idxs ! i)"
    "partial_authenticated_table fr (scale * clength) openings final_state"
proof -
  let ?round = "verifier_query_round_program fr f_fl f_final as fl final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix x suffix s_i s_suc where
    prefix:
      "Some (prefix, s_i) \<in>
        set_dist (execute (ntimes ?round i) query_state)"
    and round:
      "Some (x, s_suc) \<in> set_dist (execute ?round s_i)"
    and suffix:
      "Some (suffix, final_state) \<in>
        set_dist (execute (ntimes ?round (rounds - Suc i)) s_suc)"
    by blast
  have x_eq: "x = ()"
    by (cases x) simp
  show ?thesis
  proof (rule query_opening_ntimes_prefix_transcript_state_alignment
      [OF prefix])
    fix prefix_query_idxs prefix_chunks
    assume len_prefix_chunks: "length prefix_chunks = i"
      and transcript_prefix:
        "PTranscript query_state =
          List.concat prefix_chunks @ PTranscript s_i"
      and state_i:
        "PState s_i =
          state_after_query_chunks (PState query_state) prefix_chunks i"
      and counter_i: "PQueryCounter s_i = PQueryCounter query_state + i"
      and prefix_rounds:
        "\<And>k. k < i \<Longrightarrow>
          verifier_query_round_chunk (prefix_query_idxs ! k)
            (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    show ?thesis
    proof (rule
        verifier_query_round_program_outcome_with_authenticated_trace_openings
        [OF round[unfolded x_eq]])
      fix raw idx chunk openings
      assume idx_eq: "idx = index (to_nat raw)"
        and chunk_shape:
          "verifier_query_round_chunk idx (map snd f_fl) (map snd fl)
            chunk"
        and transcript_round: "PTranscript s_i = chunk @ PTranscript s_suc"
        and lookup_suc:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
            Some raw"
        and opening_indices: "map opening_index openings = powers_scaled idx"
        and auth_table_suc:
          "partial_authenticated_table fr (scale * clength) openings s_suc"
      show ?thesis
      proof (rule query_opening_ntimes_suffix_transcript_state_alignment
          [OF suffix])
        fix suffix_query_idxs suffix_chunks
        assume len_suffix_chunks:
            "length suffix_chunks = rounds - Suc i"
          and transcript_suffix:
            "PTranscript s_suc =
              List.concat suffix_chunks @ PTranscript final_state"
          and suffix_ext: "s_suc \<le> final_state"
          and suffix_rounds:
            "\<And>k. k < rounds - Suc i \<Longrightarrow>
              verifier_query_round_chunk (suffix_query_idxs ! k)
                (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
        let ?selected_chunks = "prefix_chunks @ chunk # suffix_chunks"
        have len_selected_chunks: "length ?selected_chunks = rounds"
          using len_prefix_chunks len_suffix_chunks i_bound by simp
        have selected_chunk_lens:
          "\<And>k. k < rounds \<Longrightarrow>
            length (?selected_chunks ! k) =
              verifier_query_round_transcript_length (query_idxs ! k)
                (map snd f_fl) (map snd fl)"
        proof -
          fix k
          assume k_bound: "k < rounds"
          show
            "length (?selected_chunks ! k) =
              verifier_query_round_transcript_length (query_idxs ! k)
                (map snd f_fl) (map snd fl)"
          proof (cases "k < i")
            case True
            have nth_eq: "?selected_chunks ! k = prefix_chunks ! k"
              using True len_prefix_chunks by (simp add: nth_append)
            have
              "length (prefix_chunks ! k) =
                verifier_query_round_transcript_length
                  (prefix_query_idxs ! k) (map snd f_fl) (map snd fl)"
              by (rule verifier_query_round_chunk_length
                  [OF prefix_rounds[OF True]])
            then show ?thesis
              using nth_eq
              by (simp add:
                  verifier_query_round_transcript_length_index_irrelevant)
          next
            case False
            show ?thesis
            proof (cases "k = i")
              case True
              have nth_eq: "?selected_chunks ! k = chunk"
                using True len_prefix_chunks by (simp add: nth_append)
              have
                "length chunk =
                  verifier_query_round_transcript_length idx
                    (map snd f_fl) (map snd fl)"
                by (rule verifier_query_round_chunk_length[OF chunk_shape])
              then show ?thesis
                using nth_eq
                by (simp add:
                    verifier_query_round_transcript_length_index_irrelevant)
            next
              case False
              let ?k = "k - Suc i"
              have ge: "Suc i \<le> k"
                using \<open>\<not> k < i\<close> False by linarith
              have k_bound': "?k < rounds - Suc i"
                using ge k_bound by linarith
              have nth_eq: "?selected_chunks ! k = suffix_chunks ! ?k"
                using ge len_prefix_chunks by (simp add: nth_append)
              have
                "length (suffix_chunks ! ?k) =
                  verifier_query_round_transcript_length
                    (suffix_query_idxs ! ?k) (map snd f_fl) (map snd fl)"
                by (rule verifier_query_round_chunk_length
                    [OF suffix_rounds[OF k_bound']])
              then show ?thesis
                using nth_eq
                by (simp add:
                    verifier_query_round_transcript_length_index_irrelevant)
            qed
          qed
        qed
        have query_chunk_lens:
          "\<And>k. k < rounds \<Longrightarrow>
            length (query_chunks ! k) =
              verifier_query_round_transcript_length (query_idxs ! k)
                (map snd f_fl) (map snd fl)"
          using query_chunk verifier_query_round_chunk_length by blast
        have transcript_all:
          "PTranscript query_state =
            List.concat ?selected_chunks @ PTranscript final_state"
          using transcript_prefix transcript_round transcript_suffix by simp
        have concat_eq:
          "List.concat ?selected_chunks = List.concat query_chunks"
          using transcript_all transcript_query by simp
        have chunks_eq: "?selected_chunks = query_chunks"
        proof -
          have same_lens:
            "\<And>k. k < length ?selected_chunks \<Longrightarrow>
              length (?selected_chunks ! k) = length (query_chunks ! k)"
            using selected_chunk_lens query_chunk_lens len_selected_chunks
            by simp
          have concat_eq_empty:
            "List.concat ?selected_chunks @ [] = List.concat query_chunks"
            using concat_eq by simp
          have len_eq: "length ?selected_chunks = length query_chunks"
            using len_selected_chunks len_query_chunks by simp
          have "?selected_chunks = query_chunks \<and> ([] :: 'f list) = []"
            by (rule concat_append_eq_concat_same_chunk_lengths
                [OF len_eq same_lens concat_eq_empty])
          then show ?thesis
            by simp
        qed
        have prefix_state_eq:
          "state_after_query_chunks (PState query_state) prefix_chunks i =
            state_after_query_chunks (PState query_state) query_chunks i"
        proof -
          have
            "state_after_query_chunks (PState query_state)
              ?selected_chunks i =
              state_after_query_chunks (PState query_state)
                prefix_chunks i"
            by (rule state_after_query_chunks_append_prefix
                [OF len_prefix_chunks])
          then show ?thesis
            using chunks_eq by simp
        qed
        have lookup_final:
          "fmlookup (HashMap final_state)
            (QueryIndexChallenge (PQueryCounter query_state + i)
              (state_after_query_chunks
                (PState query_state) query_chunks i)) =
            Some raw"
          using hash_extension_lookup[OF lookup_suc suffix_ext]
          unfolding counter_i state_i prefix_state_eq .
        have raw_eq: "raw = raw_idxs ! i"
          using lookup_final replay_lookup[OF i_bound] by simp
        have idx_eq_query: "idx = query_idxs ! i"
          using idx_eq raw_eq query_idxs_eq len_raw i_bound by simp
        have auth_table_final:
          "partial_authenticated_table fr (scale * clength) openings
            final_state"
          by (rule partial_authenticated_table_mono
              [OF auth_table_suc suffix_ext])
        show ?thesis
          by (rule that[OF _ auth_table_final])
            (use opening_indices idx_eq_query in simp)
      qed
    qed
  qed
qed

lemma verifier_query_round_program_outcome_with_zero_trace_final_opening:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes f_fl_empty: "f_fl = []"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx chunk openings where
    "idx = index (to_nat raw)"
    "verifier_query_round_chunk idx [] (map snd fl) chunk"
    "PTranscript s = chunk @ PTranscript t"
    "PState t = foldl concat (PState s) chunk"
    "s \<le> t"
    "PQueryCounter t = Suc (PQueryCounter s)"
    "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) =
      Some raw"
    "map opening_index openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) openings t"
    "opening_value (hd openings) = f_final"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where
    rand:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  let ?idx = "index (to_nat raw)"
  from tail obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s0)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (?idx, hd fv, clength * scale, 1)
            (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold
            (?idx, cp_eval as fv (h ^ ?idx * shift), clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have rand_res:
    "s \<le> s0 \<and>
     PState s0 = PState s \<and>
     PTranscript s0 = PTranscript s \<and>
     fmlookup (HashMap s0)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF rand] .
  have rand_counter:
    "PQueryCounter s0 = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF rand] by simp
  from check_decommit_on_query_outcome[OF query_decommit]
  obtain query_paths query_chunk where
    query_chunk_shape:
      "query_decommitment_transcript ?idx fv query_paths query_chunk"
    and tr_s0: "PTranscript s0 = query_chunk @ PTranscript s1"
    and st_s1: "PState s1 = foldl concat (PState s0) query_chunk"
    and ext_s0_s1: "s0 \<le> s1"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s0"
    by blast
  have trace_out:
    "f_out = (?idx, hd fv, clength * scale, 1)"
    and s2_eq: "s2 = s1"
    using trace_fri f_fl_empty
    unfolding receive_query_commits_def by simp_all
  have hd_fv: "hd fv = f_final"
    using assert_trace unfolding assert_def trace_out
    by (cases "hd fv = f_final") (auto simp: throw_no_outcome)
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def trace_out hd_fv by simp
  from receive_query_commits_layers_outcome[OF comp_fri]
  obtain comp_layer_chunks comp_fri_chunk where
    comp_layers:
      "fri_layers_transcript (length fl) (clength * scale)
        comp_layer_chunks comp_fri_chunk"
    and tr_s3: "PTranscript s3 = comp_fri_chunk @ PTranscript s4"
    and st_s4: "PState s4 = foldl concat (PState s3) comp_fri_chunk"
    and ext_s3_s4: "s3 \<le> s4"
    and query_count_s4: "PQueryCounter s4 = PQueryCounter s3"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  have trace_layers_empty:
    "fri_layers_transcript 0 (clength * scale) [] []"
    unfolding fri_layers_transcript_def by simp
  let ?chunk = "query_chunk @ [] @ comp_fri_chunk"
  have round_chunk:
    "verifier_query_round_chunk ?idx [] (map snd fl) ?chunk"
    unfolding verifier_query_round_chunk_def
    apply (rule exI[where x=query_chunk])
    apply (rule exI[where x="[]"])
    apply (rule exI[where x=comp_fri_chunk])
    apply (rule exI[where x=fv])
    apply (rule exI[where x=query_paths])
    apply (rule exI[where x="[]"])
    apply (rule exI[where x=comp_layer_chunks])
    using query_chunk_shape trace_layers_empty comp_layers
    by simp
  have tr_t: "PTranscript s = ?chunk @ PTranscript t"
    using rand_res tr_s0 tr_s3 s3_eq s2_eq t_eq by simp
  have st_t: "PState t = foldl concat (PState s) ?chunk"
    using rand_res st_s1 st_s4 s3_eq s2_eq t_eq by simp
  have ext_s0_t: "s0 \<le> t"
    using ext_s0_s1 ext_s3_s4 t_eq unfolding s3_eq s2_eq
    by (meson hash_ext_trans)
  have ext_s_t: "s \<le> t"
    using rand_res ext_s0_t by (meson hash_ext_trans)
  have query_count_t: "PQueryCounter t = Suc (PQueryCounter s)"
    using rand_counter query_count_s1 query_count_s4
    unfolding s3_eq s2_eq t_eq by simp
  have lookup_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using hash_extension_lookup[OF conjunct2[OF conjunct2[OF conjunct2[OF rand_res]]] ext_s0_t]
      rand_res
    by simp
  have idx_in: "?idx \<in> query_sample_space"
    using index_less_query_sample_space
    unfolding query_sample_space_def by simp
  from check_decommit_on_query_authenticated_openings
      [OF idx_in query_decommit]
  obtain openings where values_openings:
      "map opening_value openings = fv"
    and idx_openings: "map opening_index openings = powers_scaled ?idx"
    and table_s1:
      "partial_authenticated_table fr (scale * clength) openings s1"
    by blast
  have s1_t: "s1 \<le> t"
    using ext_s3_s4 unfolding s3_eq s2_eq t_eq .
  have table_t:
    "partial_authenticated_table fr (scale * clength) openings t"
    by (rule partial_authenticated_table_mono[OF table_s1 s1_t])
  have openings_nonempty: "openings \<noteq> []"
  proof -
    have "map opening_index openings \<noteq> []"
      using idx_openings powers_pos unfolding powers_scaled_def by simp
    then show ?thesis by auto
  qed
  have hd_value: "opening_value (hd openings) = hd fv"
    using values_openings openings_nonempty
    by (cases openings; cases fv) simp_all
  show ?thesis
  proof (rule that)
    show "?idx = index (to_nat raw)"
      by simp
    show "verifier_query_round_chunk ?idx [] (map snd fl) ?chunk"
      by (rule round_chunk)
    show "PTranscript s = ?chunk @ PTranscript t"
      by (rule tr_t)
    show "PState t = foldl concat (PState s) ?chunk"
      by (rule st_t)
    show "s \<le> t"
      by (rule ext_s_t)
    show "PQueryCounter t = Suc (PQueryCounter s)"
      by (rule query_count_t)
    show "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
      by (rule lookup_t)
    show "map opening_index openings = powers_scaled ?idx"
      by (rule idx_openings)
    show "partial_authenticated_table fr (scale * clength) openings t"
      by (rule table_t)
    show "opening_value (hd openings) = f_final"
      using hd_value hd_fv by simp
  qed
qed

lemma ntimes_verifier_query_rounds_selected_empty_trace_chunks_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_empty: "fl = []"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
    and i_bound: "i < n"
  obtains raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
      suffix_chunks trace_openings where
    "idx = index (to_nat raw)"
    "length prefix_query_idxs = i"
    "length prefix_chunks = i"
    "length suffix_query_idxs = n - Suc i"
    "length suffix_chunks = n - Suc i"
    "verifier_query_round_chunk idx (map snd f_fl) [] chunk"
    "\<And>j. j < i \<Longrightarrow>
      verifier_query_round_chunk (prefix_query_idxs ! j)
        (map snd f_fl) [] (prefix_chunks ! j)"
    "\<And>j. j < n - Suc i \<Longrightarrow>
      verifier_query_round_chunk (suffix_query_idxs ! j)
        (map snd f_fl) [] (suffix_chunks ! j)"
    "PTranscript s =
      List.concat (prefix_chunks @ chunk # suffix_chunks) @ PTranscript t"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s + i)
        (state_after_query_chunks (PState s) prefix_chunks i)) = Some raw"
proof -
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix round suffix s_i s_suc where
    prefix:
      "Some (prefix, s_i) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) i)
            s)"
    and round:
      "Some (round, s_suc) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s_i)"
    and suffix:
      "Some (suffix, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final)
              (n - Suc i))
            s_suc)"
    by blast
  have round_unit: "round = ()"
    by (cases round) simp
  show ?thesis
  proof (rule query_opening_ntimes_prefix_transcript_state_alignment
      [OF prefix])
    fix prefix_query_idxs prefix_chunks
    assume len_prefix: "length prefix_query_idxs = i"
      and len_prefix_chunks: "length prefix_chunks = i"
      and transcript_prefix:
        "PTranscript s = List.concat prefix_chunks @ PTranscript s_i"
      and state_i:
        "PState s_i =
          state_after_query_chunks (PState s) prefix_chunks i"
      and counter_i: "PQueryCounter s_i = PQueryCounter s + i"
      and prefix_ext: "s \<le> s_i"
      and prefix_rounds:
        "\<And>j. j < i \<Longrightarrow>
          verifier_query_round_chunk (prefix_query_idxs ! j)
            (map snd f_fl) (map snd fl) (prefix_chunks ! j)"
    show ?thesis
    proof (rule
        verifier_query_round_program_outcome_with_authenticated_trace_openings
          [OF round[unfolded round_unit]])
      fix raw idx chunk trace_openings
      assume idx_eq: "idx = index (to_nat raw)"
        and chunk_shape:
          "verifier_query_round_chunk idx (map snd f_fl) (map snd fl)
            chunk"
        and transcript_round:
          "PTranscript s_i = chunk @ PTranscript s_suc"
        and state_suc:
          "PState s_suc = foldl concat (PState s_i) chunk"
        and round_ext: "s_i \<le> s_suc"
        and counter_suc: "PQueryCounter s_suc = Suc (PQueryCounter s_i)"
        and lookup_suc:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
            Some raw"
        and len_trace:
          "length trace_openings = length (powers_scaled idx)"
        and trace_indices:
          "map opening_index trace_openings = powers_scaled idx"
        and trace_table_suc:
          "partial_authenticated_table fr (scale * clength)
            trace_openings s_suc"
      show ?thesis
      proof (rule query_opening_ntimes_suffix_transcript_state_alignment
          [OF suffix])
        fix suffix_query_idxs suffix_chunks
        assume len_suffix_idxs:
            "length suffix_query_idxs = n - Suc i"
          and len_suffix_chunks:
            "length suffix_chunks = n - Suc i"
          and transcript_suffix:
            "PTranscript s_suc =
              List.concat suffix_chunks @ PTranscript t"
          and suffix_state:
            "PState t =
              state_after_query_chunks (PState s_suc) suffix_chunks
                (n - Suc i)"
          and suffix_counter:
            "PQueryCounter t = PQueryCounter s_suc + (n - Suc i)"
          and suffix_ext: "s_suc \<le> t"
          and suffix_rounds:
            "\<And>j. j < n - Suc i \<Longrightarrow>
              verifier_query_round_chunk (suffix_query_idxs ! j)
                (map snd f_fl) (map snd fl) (suffix_chunks ! j)"
        have transcript_all:
          "PTranscript s =
            List.concat (prefix_chunks @ chunk # suffix_chunks) @
              PTranscript t"
          using transcript_prefix transcript_round transcript_suffix
          by simp
        have trace_table_t:
          "partial_authenticated_table fr (scale * clength)
            trace_openings t"
          by (rule partial_authenticated_table_mono
              [OF trace_table_suc suffix_ext])
        have lookup_t:
          "fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s + i)
              (state_after_query_chunks (PState s) prefix_chunks i)) =
            Some raw"
          using hash_extension_lookup[OF lookup_suc suffix_ext]
          unfolding counter_i state_i .
        show ?thesis
          by (rule that[OF idx_eq len_prefix len_prefix_chunks
                len_suffix_idxs len_suffix_chunks _ _ _ transcript_all
                trace_indices trace_table_t lookup_t])
            (use chunk_shape prefix_rounds suffix_rounds fl_empty in simp_all)
      qed
    qed
  qed
qed

lemma ntimes_verifier_query_rounds_selected_empty_trace_chunks_aligned_with_replay_at:
  assumes outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as [] final)
              rounds)
            query_state)"
    and i_bound: "i < rounds"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) [] (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
  obtains trace_openings where
    "map opening_index trace_openings = powers_scaled (query_idxs ! i)"
    "partial_authenticated_table fr (scale * clength) trace_openings
      final_state"
proof (rule ntimes_verifier_query_rounds_selected_empty_trace_chunks_at
    [OF refl outcome i_bound])
  fix raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
      suffix_chunks trace_openings
  assume selected_idx: "idx = index (to_nat raw)"
    and len_prefix_chunks: "length prefix_chunks = i"
    and len_suffix_chunks: "length suffix_chunks = rounds - Suc i"
    and chunk_shape:
      "verifier_query_round_chunk idx (map snd f_fl) [] chunk"
    and prefix_rounds:
      "\<And>j. j < i \<Longrightarrow>
        verifier_query_round_chunk (prefix_query_idxs ! j)
          (map snd f_fl) [] (prefix_chunks ! j)"
    and suffix_rounds:
      "\<And>j. j < rounds - Suc i \<Longrightarrow>
        verifier_query_round_chunk (suffix_query_idxs ! j)
          (map snd f_fl) [] (suffix_chunks ! j)"
    and selected_transcript:
      "PTranscript query_state =
        List.concat (prefix_chunks @ chunk # suffix_chunks) @
          PTranscript final_state"
    and trace_indices:
      "map opening_index trace_openings = powers_scaled idx"
    and trace_table:
      "partial_authenticated_table fr (scale * clength) trace_openings
        final_state"
    and selected_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) prefix_chunks i)) =
        Some raw"
  let ?selected_chunks = "prefix_chunks @ chunk # suffix_chunks"
  have len_selected_chunks: "length ?selected_chunks = rounds"
    using len_prefix_chunks len_suffix_chunks i_bound by simp
  have selected_chunk_lens:
    "\<And>j. j < rounds \<Longrightarrow>
      length (?selected_chunks ! j) =
        verifier_query_round_transcript_length (query_idxs ! j)
          (map snd f_fl) []"
  proof -
    fix j
    assume j_bound: "j < rounds"
    show
      "length (?selected_chunks ! j) =
        verifier_query_round_transcript_length (query_idxs ! j)
          (map snd f_fl) []"
    proof (cases "j < i")
      case True
      have nth_eq: "?selected_chunks ! j = prefix_chunks ! j"
        using True len_prefix_chunks by (simp add: nth_append)
      have
        "length (prefix_chunks ! j) =
          verifier_query_round_transcript_length
            (prefix_query_idxs ! j) (map snd f_fl) []"
        by (rule verifier_query_round_chunk_length[OF prefix_rounds[OF True]])
      then show ?thesis
        using nth_eq
        by (simp add: verifier_query_round_transcript_length_index_irrelevant)
    next
      case False
      show ?thesis
      proof (cases "j = i")
        case True
        have nth_eq: "?selected_chunks ! j = chunk"
          using True len_prefix_chunks by (simp add: nth_append)
        have
          "length chunk =
            verifier_query_round_transcript_length idx (map snd f_fl) []"
          by (rule verifier_query_round_chunk_length[OF chunk_shape])
        then show ?thesis
          using nth_eq
          by (simp add:
              verifier_query_round_transcript_length_index_irrelevant)
      next
        case False
        let ?k = "j - Suc i"
        have ge: "Suc i \<le> j"
          using \<open>\<not> j < i\<close> False by linarith
        have k_bound: "?k < rounds - Suc i"
          using ge j_bound by linarith
        have nth_eq: "?selected_chunks ! j = suffix_chunks ! ?k"
          using ge len_prefix_chunks by (simp add: nth_append)
        have
          "length (suffix_chunks ! ?k) =
            verifier_query_round_transcript_length
              (suffix_query_idxs ! ?k) (map snd f_fl) []"
          by (rule verifier_query_round_chunk_length
              [OF suffix_rounds[OF k_bound]])
        then show ?thesis
          using nth_eq
          by (simp add:
              verifier_query_round_transcript_length_index_irrelevant)
      qed
    qed
  qed
  have query_chunk_lens:
    "\<And>j. j < rounds \<Longrightarrow>
      length (query_chunks ! j) =
        verifier_query_round_transcript_length (query_idxs ! j)
          (map snd f_fl) []"
    using query_chunk verifier_query_round_chunk_length by blast
  have concat_eq: "List.concat ?selected_chunks = List.concat query_chunks"
    using selected_transcript transcript_query by simp
  have chunks_eq: "?selected_chunks = query_chunks"
  proof -
    have same_lens:
      "\<And>j. j < length ?selected_chunks \<Longrightarrow>
        length (?selected_chunks ! j) = length (query_chunks ! j)"
      using selected_chunk_lens query_chunk_lens len_selected_chunks by simp
    have concat_eq_empty:
      "List.concat ?selected_chunks @ [] = List.concat query_chunks"
      using concat_eq by simp
    have len_eq: "length ?selected_chunks = length query_chunks"
      using len_selected_chunks len_query_chunks by simp
    have "?selected_chunks = query_chunks \<and> ([] :: 'f list) = []"
      by (rule concat_append_eq_concat_same_chunk_lengths
          [OF len_eq same_lens concat_eq_empty])
    then show ?thesis
      by simp
  qed
  have prefix_state_eq:
    "state_after_query_chunks (PState query_state) prefix_chunks i =
      state_after_query_chunks (PState query_state) query_chunks i"
  proof -
    have
      "state_after_query_chunks (PState query_state) ?selected_chunks i =
        state_after_query_chunks (PState query_state) prefix_chunks i"
      by (rule state_after_query_chunks_append_prefix[OF len_prefix_chunks])
    then show ?thesis
      using chunks_eq by simp
  qed
  have selected_lookup_global:
    "fmlookup (HashMap final_state)
      (QueryIndexChallenge (PQueryCounter query_state + i)
        (state_after_query_chunks (PState query_state) query_chunks i)) =
      Some raw"
    using selected_lookup prefix_state_eq by simp
  have raw_eq: "raw = raw_idxs ! i"
    using selected_lookup_global replay_lookup[OF i_bound] by simp
  have idx_eq: "idx = query_idxs ! i"
    using selected_idx raw_eq query_idxs_eq len_raw i_bound by simp
  show ?thesis
    by (rule that)
      (use idx_eq trace_indices trace_table in simp_all)
qed

lemma ntimes_verifier_query_rounds_empty_trace_openings_aligned_with_replay:
  assumes outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as [] final)
              rounds)
            query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) [] (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
  obtains trace_openings where
    "length trace_openings = rounds"
    "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
    "\<And>i. i < rounds \<Longrightarrow>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
proof -
  let ?P =
    "\<lambda>i openings.
      map opening_index openings = powers_scaled (query_idxs ! i) \<and>
      partial_authenticated_table fr (scale * clength) openings final_state"
  have ex_round: "\<And>i. i < rounds \<Longrightarrow> \<exists>openings. ?P i openings"
  proof -
    fix i
    assume i_bound: "i < rounds"
    show "\<exists>openings. ?P i openings"
    proof (rule
        ntimes_verifier_query_rounds_selected_empty_trace_chunks_aligned_with_replay_at
        [OF outcome i_bound len_raw query_idxs_eq len_query_chunks
          transcript_query query_chunk replay_lookup])
      fix trace_openings
      assume
        "map opening_index trace_openings =
          powers_scaled (query_idxs ! i)"
        "partial_authenticated_table fr (scale * clength)
          trace_openings final_state"
      then show ?thesis
        by blast
    qed
  qed
  let ?w = "\<lambda>i. SOME openings. ?P i openings"
  let ?trace_openings = "map ?w [0..<rounds]"
  have len_trace: "length ?trace_openings = rounds"
    by simp
  have props:
    "\<And>i. i < rounds \<Longrightarrow> ?P i (?trace_openings ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have "?P i (?w i)"
      by (rule someI_ex[OF ex_round[OF i_bound]])
    then show "?P i (?trace_openings ! i)"
      using i_bound by simp
  qed
  show ?thesis
    by (rule that[OF len_trace])
      (use props in simp_all)
qed

lemma ntimes_verifier_query_rounds_selected_zero_trace_final_opening_at:
  assumes outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr [] f_final as fl final)
              rounds)
            query_state)"
    and i_bound: "i < rounds"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          [] (map snd fl) (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
  obtains trace_openings where
    "map opening_index trace_openings = powers_scaled (query_idxs ! i)"
    "partial_authenticated_table fr (scale * clength) trace_openings
      final_state"
    "opening_value (hd trace_openings) = f_final"
proof -
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix round suffix s_i s_suc where
    prefix:
      "Some (prefix, s_i) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr [] f_final as fl final) i)
            query_state)"
    and round:
      "Some (round, s_suc) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr [] f_final as fl final) s_i)"
    and suffix:
      "Some (suffix, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr [] f_final as fl final)
              (rounds - Suc i))
            s_suc)"
    by blast
  have round_unit: "round = ()"
    by (cases round) simp
  show ?thesis
  proof (rule query_opening_ntimes_prefix_transcript_state_alignment
      [OF prefix])
    fix prefix_query_idxs prefix_chunks
    assume len_prefix: "length prefix_query_idxs = i"
      and len_prefix_chunks: "length prefix_chunks = i"
      and transcript_prefix:
        "PTranscript query_state = List.concat prefix_chunks @ PTranscript s_i"
      and state_i:
        "PState s_i =
          state_after_query_chunks (PState query_state) prefix_chunks i"
      and counter_i: "PQueryCounter s_i = PQueryCounter query_state + i"
      and prefix_ext: "query_state \<le> s_i"
      and prefix_rounds:
        "\<And>j. j < i \<Longrightarrow>
          verifier_query_round_chunk (prefix_query_idxs ! j)
            (map snd []) (map snd fl) (prefix_chunks ! j)"
    show ?thesis
    proof (rule
        verifier_query_round_program_outcome_with_zero_trace_final_opening
          [OF refl round[unfolded round_unit]])
      fix raw idx chunk trace_openings
      assume selected_idx: "idx = index (to_nat raw)"
        and chunk_shape:
          "verifier_query_round_chunk idx [] (map snd fl) chunk"
        and transcript_round:
          "PTranscript s_i = chunk @ PTranscript s_suc"
        and state_suc:
          "PState s_suc = foldl concat (PState s_i) chunk"
        and round_ext: "s_i \<le> s_suc"
        and counter_suc: "PQueryCounter s_suc = Suc (PQueryCounter s_i)"
        and lookup_suc:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
            Some raw"
        and trace_indices:
          "map opening_index trace_openings = powers_scaled idx"
        and trace_table_suc:
          "partial_authenticated_table fr (scale * clength)
            trace_openings s_suc"
        and trace_value:
          "opening_value (hd trace_openings) = f_final"
      show ?thesis
      proof (rule query_opening_ntimes_suffix_transcript_state_alignment
          [OF suffix])
        fix suffix_query_idxs suffix_chunks
        assume len_suffix_idxs:
            "length suffix_query_idxs = rounds - Suc i"
          and len_suffix_chunks:
            "length suffix_chunks = rounds - Suc i"
          and transcript_suffix:
            "PTranscript s_suc =
              List.concat suffix_chunks @ PTranscript final_state"
          and suffix_state:
            "PState final_state =
              state_after_query_chunks (PState s_suc) suffix_chunks
                (rounds - Suc i)"
          and suffix_counter:
            "PQueryCounter final_state =
              PQueryCounter s_suc + (rounds - Suc i)"
          and suffix_ext: "s_suc \<le> final_state"
          and suffix_rounds:
            "\<And>j. j < rounds - Suc i \<Longrightarrow>
              verifier_query_round_chunk (suffix_query_idxs ! j)
                (map snd []) (map snd fl) (suffix_chunks ! j)"
        let ?selected_chunks = "prefix_chunks @ chunk # suffix_chunks"
        have selected_transcript:
          "PTranscript query_state =
            List.concat ?selected_chunks @ PTranscript final_state"
          using transcript_prefix transcript_round transcript_suffix
          by simp
        have len_selected_chunks: "length ?selected_chunks = rounds"
          using len_prefix_chunks len_suffix_chunks i_bound by simp
        have selected_chunk_lens:
          "\<And>j. j < rounds \<Longrightarrow>
            length (?selected_chunks ! j) =
              verifier_query_round_transcript_length (query_idxs ! j)
                [] (map snd fl)"
        proof -
          fix j
          assume j_bound: "j < rounds"
          show
            "length (?selected_chunks ! j) =
              verifier_query_round_transcript_length (query_idxs ! j)
                [] (map snd fl)"
          proof (cases "j < i")
            case True
            have nth_eq: "?selected_chunks ! j = prefix_chunks ! j"
              using True len_prefix_chunks by (simp add: nth_append)
            have
              "length (prefix_chunks ! j) =
                verifier_query_round_transcript_length
                  (prefix_query_idxs ! j) [] (map snd fl)"
              using verifier_query_round_chunk_length
                  [OF prefix_rounds[OF True]]
              by simp
            then show ?thesis
              using nth_eq
              by (simp add:
                  verifier_query_round_transcript_length_index_irrelevant)
          next
            case False
            show ?thesis
            proof (cases "j = i")
              case True
              have nth_eq: "?selected_chunks ! j = chunk"
                using True len_prefix_chunks by (simp add: nth_append)
              have
                "length chunk =
                  verifier_query_round_transcript_length idx [] (map snd fl)"
                by (rule verifier_query_round_chunk_length[OF chunk_shape])
              then show ?thesis
                using nth_eq
                by (simp add:
                    verifier_query_round_transcript_length_index_irrelevant)
            next
              case False
              let ?k = "j - Suc i"
              have ge: "Suc i \<le> j"
                using \<open>\<not> j < i\<close> False by linarith
              have k_bound: "?k < rounds - Suc i"
                using ge j_bound by linarith
              have nth_eq: "?selected_chunks ! j = suffix_chunks ! ?k"
                using ge len_prefix_chunks by (simp add: nth_append)
              have
                "length (suffix_chunks ! ?k) =
                  verifier_query_round_transcript_length
                    (suffix_query_idxs ! ?k) [] (map snd fl)"
                using verifier_query_round_chunk_length
                    [OF suffix_rounds[OF k_bound]]
                by simp
              then show ?thesis
                using nth_eq
                by (simp add:
                    verifier_query_round_transcript_length_index_irrelevant)
            qed
          qed
        qed
        have query_chunk_lens:
          "\<And>j. j < rounds \<Longrightarrow>
            length (query_chunks ! j) =
              verifier_query_round_transcript_length (query_idxs ! j)
                [] (map snd fl)"
          using query_chunk verifier_query_round_chunk_length by blast
        have concat_eq:
          "List.concat ?selected_chunks = List.concat query_chunks"
          using selected_transcript transcript_query by simp
        have chunks_eq: "?selected_chunks = query_chunks"
        proof -
          have same_lens:
            "\<And>j. j < length ?selected_chunks \<Longrightarrow>
              length (?selected_chunks ! j) = length (query_chunks ! j)"
            using selected_chunk_lens query_chunk_lens len_selected_chunks
            by simp
          have concat_eq_empty:
            "List.concat ?selected_chunks @ [] = List.concat query_chunks"
            using concat_eq by simp
          have len_eq: "length ?selected_chunks = length query_chunks"
            using len_selected_chunks len_query_chunks by simp
          have "?selected_chunks = query_chunks \<and> ([] :: 'f list) = []"
            by (rule concat_append_eq_concat_same_chunk_lengths
                [OF len_eq same_lens concat_eq_empty])
          then show ?thesis
            by simp
        qed
        have prefix_state_eq:
          "state_after_query_chunks (PState query_state) prefix_chunks i =
            state_after_query_chunks (PState query_state) query_chunks i"
        proof -
          have
            "state_after_query_chunks (PState query_state) ?selected_chunks i =
              state_after_query_chunks (PState query_state) prefix_chunks i"
            by (rule state_after_query_chunks_append_prefix
                [OF len_prefix_chunks])
          then show ?thesis
            using chunks_eq by simp
        qed
        have selected_lookup_global:
          "fmlookup (HashMap final_state)
            (QueryIndexChallenge (PQueryCounter query_state + i)
              (state_after_query_chunks (PState query_state)
                query_chunks i)) =
            Some raw"
          using hash_extension_lookup[OF lookup_suc suffix_ext]
          unfolding counter_i state_i prefix_state_eq .
        have raw_eq: "raw = raw_idxs ! i"
          using selected_lookup_global replay_lookup[OF i_bound] by simp
        have idx_eq: "idx = query_idxs ! i"
          using selected_idx raw_eq query_idxs_eq len_raw i_bound by simp
        have trace_table:
          "partial_authenticated_table fr (scale * clength) trace_openings
            final_state"
          by (rule partial_authenticated_table_mono
              [OF trace_table_suc suffix_ext])
        show ?thesis
          by (rule that)
            (use idx_eq trace_indices trace_table trace_value in simp_all)
      qed
    qed
  qed
qed

lemma ntimes_verifier_query_rounds_zero_trace_final_openings_aligned_with_replay:
  assumes outcome:
      "Some (results, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr [] f_final as fl final)
              rounds)
            query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          [] (map snd fl) (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
  obtains trace_openings where
    "length trace_openings = rounds"
    "\<And>i. i < rounds \<Longrightarrow>
      map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
    "\<And>i. i < rounds \<Longrightarrow>
      partial_authenticated_table fr (scale * clength)
        (trace_openings ! i) final_state"
    "\<And>i. i < rounds \<Longrightarrow>
      opening_value (hd (trace_openings ! i)) = f_final"
proof -
  let ?P =
    "\<lambda>i openings.
      map opening_index openings = powers_scaled (query_idxs ! i) \<and>
      partial_authenticated_table fr (scale * clength) openings final_state \<and>
      opening_value (hd openings) = f_final"
  have ex_round: "\<And>i. i < rounds \<Longrightarrow> \<exists>openings. ?P i openings"
  proof -
    fix i
    assume i_bound: "i < rounds"
    show "\<exists>openings. ?P i openings"
    proof (rule
        ntimes_verifier_query_rounds_selected_zero_trace_final_opening_at
        [OF outcome i_bound len_raw query_idxs_eq len_query_chunks
          transcript_query query_chunk replay_lookup])
      fix trace_openings
      assume
        "map opening_index trace_openings =
          powers_scaled (query_idxs ! i)"
        "partial_authenticated_table fr (scale * clength)
          trace_openings final_state"
        "opening_value (hd trace_openings) = f_final"
      then show ?thesis
        by blast
    qed
  qed
  let ?w = "\<lambda>i. SOME openings. ?P i openings"
  let ?trace_openings = "map ?w [0..<rounds]"
  have len_trace: "length ?trace_openings = rounds"
    by simp
  have props:
    "\<And>i. i < rounds \<Longrightarrow> ?P i (?trace_openings ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have "?P i (?w i)"
      by (rule someI_ex[OF ex_round[OF i_bound]])
    then show "?P i (?trace_openings ! i)"
      using i_bound by simp
  qed
  show ?thesis
    by (rule that[OF len_trace])
      (use props in simp_all)
qed

lemma verify_monad_supplied_empty_header_partial_trace_openings:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and header0:
      "verifier_header_transcript s fr f_fri_roots f_final as dg []
        final rest"
  obtains query_idxs trace_openings where
    "accepted_transcript_shape s (Some (result, final_state)) as
      query_idxs"
    "accepted_with_partial_trace_openings s
      (Some (result, final_state)) fr query_idxs trace_openings"
proof -
  obtain f_fl query_state where f_roots:
      "map snd f_fl = f_fri_roots"
    and query_rest: "PTranscript query_state = rest"
    and query_state_start:
      "PState query_state =
        verifier_header_state s fr f_fri_roots f_final as dg [] final"
    and query_count:
      "PQueryCounter query_state = PQueryCounter s"
    and query_out:
      "Some (result, final_state) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as [] final)
              rounds)
            query_state)"
    by (rule verify_monad_supplied_empty_header_query_rounds
        [OF outcome header0])
  show ?thesis
  proof (rule verify_monad_supplied_header_transcript_shape
      [OF outcome header0])
    fix query_idxs raw_idxs query_chunks
    assume shape:
        "accepted_transcript_shape s (Some (result, final_state)) as
          query_idxs"
      and len_raw: "length raw_idxs = rounds"
      and query_idxs_eq:
        "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
      and len_query_chunks: "length query_chunks = rounds"
      and transcript_query:
        "List.concat query_chunks @ PTranscript final_state = rest"
      and query_chunk:
        "\<And>i. i < rounds \<Longrightarrow>
          verifier_query_round_chunk (query_idxs ! i)
            f_fri_roots [] (query_chunks ! i)"
      and replay_lookup:
        "\<And>i. i < rounds \<Longrightarrow>
          fmlookup (HashMap final_state)
            (QueryIndexChallenge (PQueryCounter s + i)
              (state_after_query_chunks
                (verifier_header_state s fr f_fri_roots f_final as dg []
                  final)
                query_chunks i)) =
          Some (raw_idxs ! i)"
    have transcript_query_state:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
      using transcript_query query_rest by simp
    have query_chunk_empty:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) [] (query_chunks ! i)"
      using query_chunk f_roots by simp
    have replay_lookup_query_state:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
      using replay_lookup query_state_start query_count by simp
    show ?thesis
    proof (rule
        ntimes_verifier_query_rounds_empty_trace_openings_aligned_with_replay
          [OF query_out len_raw query_idxs_eq len_query_chunks
            transcript_query_state query_chunk_empty
            replay_lookup_query_state])
      fix trace_openings
      assume len_trace: "length trace_openings = rounds"
        and trace_indices:
          "\<And>i. i < rounds \<Longrightarrow>
            map opening_index (trace_openings ! i) =
              powers_scaled (query_idxs ! i)"
        and trace_tables:
          "\<And>i. i < rounds \<Longrightarrow>
            partial_authenticated_table fr (scale * clength)
              (trace_openings ! i) final_state"
      have len_query_idxs: "length query_idxs = rounds"
        using len_raw query_idxs_eq by simp
      have partial:
        "accepted_with_partial_trace_openings s
          (Some (result, final_state)) fr query_idxs trace_openings"
        unfolding accepted_with_partial_trace_openings_def accepted_def
        by (intro conjI exI[of _ result] exI[of _ final_state])
          (use len_query_idxs len_trace trace_indices trace_tables in auto)
      show ?thesis
        by (rule that[OF shape partial])
    qed
  qed
qed

end

end
