(*  Title:      Stark/Soundness_FRI_Value_Aligned_Events.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Value_Aligned_Events
  imports Soundness_FRI_Composition_Residuals
begin

text \<open>
  Value-aligned FRI branch events.

  These events are narrower than the raw sampled base-opening conflicts: they
  keep the trace query opening that supplies the first trace FRI input value.
  The intended use is to avoid exporting broad verifier-query-round
  decomposition lemmas, which are expensive for Isabelle to finalize.
\<close>

context soundness
begin

lemma receive_query_commits_head_layer_outcome:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes bfs_eq: "bfs = (b, rt) # bfs_tail"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw) (receive_query_commits bfs)) s)"
  obtains layer_chunks chunk xp xp_path xn xn_path where
    "fri_layers_transcript (length bfs) len layer_chunks chunk"
    "PTranscript s = chunk @ PTranscript t"
    "PState t = foldl concat (PState s) chunk"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
    "layer_chunks \<noteq> []"
    "xp = x"
    "fri_layer_opening_chunk len xp xp_path xn xn_path (hd layer_chunks)"
proof -
  have steps:
    "receive_query_commits bfs =
      fri_layer_opening_step (b, rt) #
        receive_query_commits bfs_tail"
    unfolding bfs_eq receive_query_commits_def fri_layer_opening_step_def
    by simp
  from outcome[unfolded steps]
  obtain out1 s1 where head:
      "Some (out1, s1) \<in>
        set_dist
          (execute
            (fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist (execute
          (mfold out1 (receive_query_commits bfs_tail)) s1)"
    by (auto elim!: set_dist_bindE)
  from fri_layer_opening_step_outcome[OF head]
  obtain xp xp_path xn xn_path x' where out1_eq:
      "out1 = (idx mod (len div 2), x', len div 2, pw + pw)"
    and xp_eq: "xp = x"
    and head_chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path
        ([xp] @ xp_path @ [xn] @ xn_path)"
    and transcript_head:
      "PTranscript s =
        ([xp] @ xp_path @ [xn] @ xn_path) @ PTranscript s1"
    and state_head:
      "PState s1 =
        foldl concat (PState s) ([xp] @ xp_path @ [xn] @ xn_path)"
    and ext_head: "s \<le> s1"
    and counter_head: "PQueryCounter s1 = PQueryCounter s"
    using fri_layer_opening_step_outcome[OF head]
    by blast
  from receive_query_commits_layers_outcome[OF tail[unfolded out1_eq]]
  obtain tail_layers tail_chunk where tail_layers:
      "fri_layers_transcript (length bfs_tail) (len div 2)
        tail_layers tail_chunk"
    and transcript_tail:
      "PTranscript s1 = tail_chunk @ PTranscript t"
    and state_tail:
      "PState t = foldl concat (PState s1) tail_chunk"
    and ext_tail: "s1 \<le> t"
    and counter_tail: "PQueryCounter t = PQueryCounter s1"
    by blast
  let ?head_chunk = "[xp] @ xp_path @ [xn] @ xn_path"
  let ?layers = "?head_chunk # tail_layers"
  let ?chunk = "?head_chunk @ tail_chunk"
  have layers:
    "fri_layers_transcript (length bfs) len ?layers ?chunk"
    using tail_layers head_chunk unfolding bfs_eq fri_layers_transcript_def
    by auto
  have transcript:
    "PTranscript s = ?chunk @ PTranscript t"
    using transcript_head transcript_tail by simp
  have state:
    "PState t = foldl concat (PState s) ?chunk"
    using state_head state_tail by simp
  have ext: "s \<le> t"
    by (rule hash_ext_trans[OF ext_head ext_tail])
  have counter: "PQueryCounter t = PQueryCounter s"
    using counter_head counter_tail by simp
  show ?thesis
    by (rule that[OF layers transcript state ext counter _ xp_eq])
      (use head_chunk in simp_all)
qed

lemma verifier_query_round_after_index_trace_fri_head_value_aligned:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
  obtains idx openings xp xp_path xn xn_path where
    "idx = index (to_nat raw)"
    "map opening_index openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) openings t"
    "openings \<noteq> []"
    "opening_value (hd openings) = xp"
    "fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
      ([xp] @ xp_path @ [xn] @ xn_path)"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s)"
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
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have idx_in: "?idx \<in> query_sample_space"
    using index_less_query_sample_space
    unfolding query_sample_space_def by simp
  from check_decommit_on_query_authenticated_openings
      [OF idx_in query_decommit]
  obtain openings where len_openings:
      "length openings = length (powers_scaled ?idx)"
    and values_openings: "map opening_value openings = fv"
    and idx_openings: "map opening_index openings = powers_scaled ?idx"
    and table_s1:
      "partial_authenticated_table fr (scale * clength) openings s1"
    by blast
  from receive_query_commits_decomp_at
      [OF trace_fri[unfolded f_fl_eq], of 0]
  obtain idx0 x0 len0 pw0 out1 s1' s_suc where
    head:
      "Some (out1, s1') \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt)
            (?idx, hd fv, clength * scale, 1)) s1)"
    by simp blast
  from fri_layer_opening_step_outcome[OF head]
  obtain xp xp_path xn xn_path x' where
    xp_eq: "xp = hd fv"
    and chunk:
      "fri_layer_opening_chunk (clength * scale) xp xp_path xn xn_path
        ([xp] @ xp_path @ [xn] @ xn_path)"
    by blast
  have s1_t: "s1 \<le> t"
  proof -
    obtain idx1 x1 len1 pw1 where f_out_eq:
      "f_out = (idx1, x1, len1, pw1)"
      by (cases f_out)
    have s1_s2:
      "s1 \<le> s2"
      by (rule receive_query_commits_mfold_hash_extends
          [OF trace_fri[unfolded f_out_eq]])
    have s3_eq: "s3 = s2"
      using assert_trace unfolding assert_def f_out_eq
      by (cases "x1 = f_final") (auto simp: throw_no_outcome)
    have s3_s4:
      "s3 \<le> s4"
      by (rule receive_query_commits_mfold_hash_extends[OF comp_fri])
    have t_eq: "t = s4"
      using assert_comp unfolding assert_def
      by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
        (auto simp: throw_no_outcome)
    have s2_s4: "s2 \<le> s4"
      using s3_s4 unfolding s3_eq .
    show ?thesis
      using hash_ext_trans[OF s1_s2 s2_s4] t_eq by simp
  qed
  have table_t:
    "partial_authenticated_table fr (scale * clength) openings t"
    by (rule partial_authenticated_table_mono[OF table_s1 s1_t])
  have openings_nonempty: "openings \<noteq> []"
    using len_openings powers_pos unfolding powers_scaled_def by auto
  have hd_value: "opening_value (hd openings) = hd fv"
    using values_openings openings_nonempty
    by (cases openings; cases fv) simp_all
  show ?thesis
    by (rule that[OF refl idx_openings table_t openings_nonempty])
      (use hd_value xp_eq chunk in \<open>simp_all add: mult.commute\<close>)
qed

lemma verifier_query_round_after_index_trace_fri_head_layer_value_aligned:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
  obtains idx openings query_chunk trace_layer_chunks composition_layer_chunks
      xp xp_path xn xn_path where
    "idx = index (to_nat raw)"
    "query_round_fri_layer_transcripts idx (map snd f_fl) (map snd fl)
      query_chunk trace_layer_chunks composition_layer_chunks"
    "PTranscript s = query_chunk @ PTranscript t"
    "PState t = foldl concat (PState s) query_chunk"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
    "map opening_index openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) openings t"
    "openings \<noteq> []"
    "opening_value (hd openings) = xp"
    "fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
      (trace_layer_chunks ! 0)"
proof -
  let ?idx = "index (to_nat raw)"
  from outcome obtain fv s1 f_out s2 s3 c_out s4 where
    query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr ?idx)) s)"
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
          (mfold (?idx, cp_eval as fv (h ^ ?idx * shift),
              clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
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
  from check_decommit_on_query_outcome[OF query_decommit]
  obtain query_paths decommit_chunk where query_chunk_shape:
      "query_decommitment_transcript ?idx fv query_paths decommit_chunk"
    and tr_s_s1:
      "PTranscript s = decommit_chunk @ PTranscript s1"
    and st_s1:
      "PState s1 = foldl concat (PState s) decommit_chunk"
    and ext_s_s1: "s \<le> s1"
    and query_counter_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  from receive_query_commits_head_layer_outcome[OF f_fl_eq trace_fri]
  obtain trace_layer_chunks trace_fri_chunk xp xp_path xn xn_path where
    trace_layers:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layer_chunks trace_fri_chunk"
    and tr_s1_s2:
      "PTranscript s1 = trace_fri_chunk @ PTranscript s2"
    and st_s2:
      "PState s2 = foldl concat (PState s1) trace_fri_chunk"
    and ext_s1_s2: "s1 \<le> s2"
    and query_counter_s2: "PQueryCounter s2 = PQueryCounter s1"
    and trace_layers_nonempty: "trace_layer_chunks \<noteq> []"
    and xp_eq: "xp = hd fv"
    and head_chunk:
      "fri_layer_opening_chunk (clength * scale) xp xp_path xn xn_path
        (hd trace_layer_chunks)"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  from receive_query_commits_layers_outcome[OF comp_fri]
  obtain composition_layer_chunks composition_fri_chunk where
    composition_layers:
      "fri_layers_transcript (length fl) (clength * scale)
        composition_layer_chunks composition_fri_chunk"
    and tr_s3_s4:
      "PTranscript s3 = composition_fri_chunk @ PTranscript s4"
    and st_s4:
      "PState s4 = foldl concat (PState s3) composition_fri_chunk"
    and ext_s3_s4: "s3 \<le> s4"
    and query_counter_s4: "PQueryCounter s4 = PQueryCounter s3"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  let ?query_chunk =
    "decommit_chunk @ trace_fri_chunk @ composition_fri_chunk"
  have round_layers:
    "query_round_fri_layer_transcripts ?idx (map snd f_fl) (map snd fl)
      ?query_chunk trace_layer_chunks composition_layer_chunks"
    unfolding query_round_fri_layer_transcripts_def
    by (intro exI[of _ decommit_chunk] exI[of _ trace_fri_chunk]
        exI[of _ composition_fri_chunk] exI[of _ fv]
        exI[of _ query_paths] conjI)
      (use query_chunk_shape trace_layers composition_layers in
        \<open>simp_all add: mult.commute\<close>)
  have tr_t: "PTranscript s = ?query_chunk @ PTranscript t"
    using tr_s_s1 tr_s1_s2 tr_s3_s4 s3_eq t_eq by simp
  have st_t: "PState t = foldl concat (PState s) ?query_chunk"
    using st_s1 st_s2 st_s4 s3_eq t_eq by simp
  have ext_s_t: "s \<le> t"
    using ext_s_s1 ext_s1_s2 ext_s3_s4 t_eq unfolding s3_eq
    by (meson hash_ext_trans)
  have query_counter_t: "PQueryCounter t = PQueryCounter s"
    using query_counter_s1 query_counter_s2 query_counter_s4
    unfolding s3_eq t_eq by simp
  have table_t:
    "partial_authenticated_table fr (scale * clength) openings t"
    by (rule partial_authenticated_table_mono[OF table_s1])
      (use ext_s1_s2 ext_s3_s4 t_eq s3_eq in
        \<open>meson hash_ext_trans\<close>)
  have openings_nonempty: "openings \<noteq> []"
    using idx_openings powers_pos unfolding powers_scaled_def by auto
  have hd_value: "opening_value (hd openings) = hd fv"
    using values_openings openings_nonempty
    by (cases openings; cases fv) simp_all
  have head_chunk_nth:
    "fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
      (trace_layer_chunks ! 0)"
    using head_chunk trace_layers_nonempty
    by (cases trace_layer_chunks) (simp_all add: mult.commute)
  show ?thesis
    by (rule that[OF refl round_layers tr_t st_t ext_s_t query_counter_t
          idx_openings table_t openings_nonempty _ head_chunk_nth])
      (use hd_value xp_eq in simp)
qed

lemma verifier_query_round_program_trace_fri_head_value_aligned_with_lookup:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx openings xp xp_path xn xn_path where
    "idx = index (to_nat raw)"
    "map opening_index openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) openings t"
    "openings \<noteq> []"
    "opening_value (hd openings) = xp"
    "fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
      ([xp] @ xp_path @ [xn] @ xn_path)"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where raw:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  obtain idx openings xp xp_path xn xn_path where
    idx_eq: "idx = index (to_nat raw)"
    and idxs: "map opening_index openings = powers_scaled idx"
    and auth_table:
      "partial_authenticated_table fr (scale * clength) openings t"
    and nonempty: "openings \<noteq> []"
    and opening_value_eq: "opening_value (hd openings) = xp"
    and chunk:
      "fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
        ([xp] @ xp_path @ [xn] @ xn_path)"
    using verifier_query_round_after_index_trace_fri_head_value_aligned
      [OF f_fl_eq tail]
    by metis
  have lookup_s0:
    "fmlookup (HashMap s0)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF raw] by simp
  have s0_t: "s0 \<le> t"
    using verifier_query_round_after_index_program_outcome[OF tail]
    by simp
  have lookup_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF lookup_s0 s0_t])
  show ?thesis
    by (rule that[OF idx_eq idxs auth_table nonempty opening_value_eq chunk lookup_t])
qed

lemma ntimes_verifier_query_rounds_selected_trace_fri_head_value_aligned_with_replay_at:
  fixes query_state final_state :: "('f, 'a) protocol_channel_scheme"
  assumes f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    and outcome:
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
  obtains openings xp xp_path xn xn_path where
    "map opening_index openings = powers_scaled (query_idxs ! i)"
    "partial_authenticated_table fr (scale * clength) openings final_state"
    "openings \<noteq> []"
    "opening_value (hd openings) = xp"
    "fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
      ([xp] @ xp_path @ [xn] @ xn_path)"
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
    assume len_prefix_idxs: "length prefix_query_idxs = i"
      and len_prefix_chunks: "length prefix_chunks = i"
      and transcript_prefix:
        "PTranscript query_state =
          List.concat prefix_chunks @ PTranscript s_i"
      and state_i:
        "PState s_i =
          state_after_query_chunks (PState query_state) prefix_chunks i"
      and counter_i:
        "PQueryCounter s_i = PQueryCounter query_state + i"
      and prefix_ext: "query_state \<le> s_i"
      and prefix_rounds:
        "\<And>k. k < i \<Longrightarrow>
          verifier_query_round_chunk (prefix_query_idxs ! k)
            (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    show ?thesis
    proof (rule verifier_query_round_program_outcome_with_authenticated_trace_openings
        [OF round[unfolded x_eq]])
      fix raw idx chunk round_openings
      assume idx_eq: "idx = index (to_nat raw)"
        and chunk_shape:
          "verifier_query_round_chunk idx (map snd f_fl) (map snd fl)
            chunk"
        and transcript_round:
          "PTranscript s_i = chunk @ PTranscript s_suc"
        and state_suc:
          "PState s_suc = foldl concat (PState s_i) chunk"
        and round_ext: "s_i \<le> s_suc"
        and counter_suc:
          "PQueryCounter s_suc = Suc (PQueryCounter s_i)"
        and lookup_suc:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
            Some raw"
        and len_round_openings:
          "length round_openings = length (powers_scaled idx)"
        and trace_indices:
          "map opening_index round_openings = powers_scaled idx"
        and trace_table_suc:
          "partial_authenticated_table fr (scale * clength)
            round_openings s_suc"
      show ?thesis
      proof (rule verifier_query_round_program_trace_fri_head_value_aligned_with_lookup
          [OF f_fl_eq round[unfolded x_eq]])
        fix raw' idx' openings xp xp_path xn xn_path
        assume idx'_eq: "idx' = index (to_nat raw')"
          and opening_indices:
            "map opening_index openings = powers_scaled idx'"
          and auth_table_suc:
            "partial_authenticated_table fr (scale * clength) openings
              s_suc"
          and openings_nonempty: "openings \<noteq> []"
          and opening_value_eq: "opening_value (hd openings) = xp"
          and head_chunk:
            "fri_layer_opening_chunk (scale * clength) xp xp_path xn
              xn_path ([xp] @ xp_path @ [xn] @ xn_path)"
          and lookup_suc':
            "fmlookup (HashMap s_suc)
              (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
              Some raw'"
        have raw'_eq: "raw' = raw"
          using lookup_suc lookup_suc' by simp
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
          have idx'_eq_query: "idx' = query_idxs ! i"
            using idx'_eq raw'_eq raw_eq query_idxs_eq len_raw i_bound
            by simp
          have auth_table_final:
            "partial_authenticated_table fr (scale * clength) openings
              final_state"
            by (rule partial_authenticated_table_mono
                [OF auth_table_suc suffix_ext])
          show ?thesis
            by (rule that[OF _ auth_table_final openings_nonempty
                  opening_value_eq head_chunk])
              (use opening_indices idx'_eq_query in simp)
        qed
      qed
    qed
  qed
qed

definition trace_fri_header_tied_value_aligned_base_opening_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_value_aligned_base_opening_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        round_idx xp xp_path xn xn_path result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      round_idx < length fri_query_idxs \<and>
      0 < length trace_bs \<and>
      trace_openings ! round_idx \<noteq> [] \<and>
      opening_index (hd (trace_openings ! round_idx)) =
        fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0 \<and>
      opening_value (hd (trace_openings ! round_idx)) = xp \<and>
      fri_layer_step_evidence
        (trace_roots ! 0)
        (trace_bs ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
          round_idx 0 xp xn)
        (trace_round_layers ! round_idx ! 0) \<and>
      \<not> fri_opening_matches_table
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        trace_table xp xn)"

definition trace_fri_header_tied_value_aligned_sibling_mismatch
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_value_aligned_sibling_mismatch s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        round_idx xp xp_path xn xn_path result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_low_degree trace_table \<and>
      round_idx < length fri_query_idxs \<and>
      0 < length trace_bs \<and>
      trace_openings ! round_idx \<noteq> [] \<and>
      opening_index (hd (trace_openings ! round_idx)) =
        fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0 \<and>
      opening_value (hd (trace_openings ! round_idx)) = xp \<and>
      fri_layer_step_evidence
        (trace_roots ! 0)
        (trace_bs ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
          round_idx 0 xp xn)
        (trace_round_layers ! round_idx ! 0) \<and>
      trace_table !
        fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        \<noteq> xn)"

lemma trace_fri_header_tied_value_aligned_base_imp_sampled_base:
  assumes
    "trace_fri_header_tied_value_aligned_base_opening_conflict s out"
  shows "trace_fri_header_tied_sampled_base_opening_conflict s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      round_idx xp xp_path xn xn_path result final_state
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and round_bound: "round_idx < length fri_query_idxs"
    and trace_bs_nonempty: "0 < length trace_bs"
    and openings_nonempty: "trace_openings ! round_idx \<noteq> []"
    and hd_idx:
      "opening_index (hd (trace_openings ! round_idx)) =
        fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0"
    and hd_value: "opening_value (hd (trace_openings ! round_idx)) = xp"
    and step:
      "fri_layer_step_evidence
        (trace_roots ! 0)
        (trace_bs ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
          round_idx 0 xp xn)
        (trace_round_layers ! round_idx ! 0)"
    and no_match:
      "\<not> fri_opening_matches_table
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        trace_table xp xn"
    unfolding
      trace_fri_header_tied_value_aligned_base_opening_conflict_def
    by auto
  have base:
    "generic_fri_sampled_base_opening_conflict trace_table trace_roots
      trace_bs fri_query_idxs trace_round_layers"
    unfolding generic_fri_sampled_base_opening_conflict_def
    by (intro exI[of _ round_idx] exI[of _ xp] exI[of _ xp_path]
        exI[of _ xn] exI[of _ xn_path] conjI)
      (use round_bound trace_bs_nonempty step no_match in auto)
  show ?thesis
    unfolding trace_fri_header_tied_sampled_base_opening_conflict_def
    by (intro exI conjI)
      (use out_eq fri_openings header partial cand not_low base in auto)
qed

lemma trace_fri_header_tied_value_aligned_base_imp_sibling_mismatch:
  assumes
    "trace_fri_header_tied_value_aligned_base_opening_conflict s out"
  shows "trace_fri_header_tied_value_aligned_sibling_mismatch s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      round_idx xp xp_path xn xn_path result final_state
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and round_bound: "round_idx < length fri_query_idxs"
    and trace_bs_nonempty: "0 < length trace_bs"
    and openings_nonempty: "trace_openings ! round_idx \<noteq> []"
    and hd_idx:
      "opening_index (hd (trace_openings ! round_idx)) =
        fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0"
    and hd_value: "opening_value (hd (trace_openings ! round_idx)) = xp"
    and step:
      "fri_layer_step_evidence
        (trace_roots ! 0)
        (trace_bs ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
          round_idx 0 xp xn)
        (trace_round_layers ! round_idx ! 0)"
    and no_match:
      "\<not> fri_opening_matches_table
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        trace_table xp xn"
    unfolding
      trace_fri_header_tied_value_aligned_base_opening_conflict_def
    by auto
  let ?idx =
    "fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0"
  let ?len = "fri_evidence_layer_len trace_roots 0"
  let ?opn = "hd (trace_openings ! round_idx)"
  have round_bound_rounds: "round_idx < rounds"
    using round_bound accepted_fri_opening_transcript_shapes(7)[OF fri_openings]
    by simp
  have opn_in: "?opn \<in> set (trace_openings ! round_idx)"
    using openings_nonempty by simp
  have table_len: "length trace_table = scale * clength"
    by (rule partial_trace_table_candidateD(1)
        [OF cand round_bound_rounds opn_in])
  have idx_bound_eval: "?idx < scale * clength"
    using partial_trace_table_candidateD(2)
        [OF cand round_bound_rounds opn_in] hd_idx
    by simp
  have table_left: "trace_table ! ?idx = xp"
    using partial_trace_table_candidateD(3)
        [OF cand round_bound_rounds opn_in] hd_idx hd_value
    by simp
  have roots_nonempty: "0 < length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings]
      trace_bs_nonempty
    by simp
  have len_eq: "?len = scale * clength"
    unfolding fri_evidence_layer_len_def
    using fri_layer_lengths_nth_div[of 0 "length trace_roots"
        "clength * scale"] roots_nonempty
    by (simp add: mult.commute)
  have sibling_mismatch:
    "trace_table ! fri_sibling_index ?len ?idx \<noteq> xn"
  proof
    assume sibling_eq: "trace_table ! fri_sibling_index ?len ?idx = xn"
    have "fri_opening_matches_table ?len ?idx trace_table xp xn"
      unfolding fri_opening_matches_table_def
      using idx_bound_eval table_len table_left sibling_eq len_eq
      by (simp add: mult.commute)
    then show False
      using no_match by contradiction
  qed
  show ?thesis
    unfolding trace_fri_header_tied_value_aligned_sibling_mismatch_def
    by (intro exI conjI)
      (use out_eq fri_openings header partial cand not_low round_bound
        trace_bs_nonempty openings_nonempty hd_idx hd_value step
        sibling_mismatch in auto)
qed

lemma wp_trace_fri_header_tied_value_aligned_base_bound_from_sibling_mismatch:
  assumes mismatch_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_value_aligned_sibling_mismatch s) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_value_aligned_base_opening_conflict s) s \<le> M"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_value_aligned_base_opening_conflict s) s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_value_aligned_sibling_mismatch s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_value_aligned_base_imp_sibling_mismatch)
  then show ?thesis
    by (rule order_trans[OF _ mismatch_bound])
qed

definition trace_fri_header_tied_sibling_mismatch_structural_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_sibling_mismatch_structural_gap s out
    \<longleftrightarrow>
    trace_fri_header_tied_value_aligned_sibling_mismatch s out \<and>
    \<not> partial_merkle_inconsistency_bad s out"

lemma trace_fri_header_tied_value_aligned_sibling_mismatch_imp_partial_merkle_or_structural_gap:
  assumes mismatch:
    "trace_fri_header_tied_value_aligned_sibling_mismatch s out"
  shows
    "partial_merkle_inconsistency_bad s out \<or>
     trace_fri_header_tied_sibling_mismatch_structural_gap s out"
proof -
  show ?thesis
    using mismatch
    unfolding trace_fri_header_tied_sibling_mismatch_structural_gap_def
    by blast
qed

lemma wp_trace_fri_header_tied_value_aligned_sibling_mismatch_bound_from_partial_merkle_and_structural_gap:
  fixes P G :: prob
  assumes partial_merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_value_aligned_sibling_mismatch s) s \<le> P + G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_value_aligned_sibling_mismatch s) s \<le>
      wp_event verify_monad
        (\<lambda>out. partial_merkle_inconsistency_bad s out \<or>
          trace_fri_header_tied_sibling_mismatch_structural_gap s out) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_value_aligned_sibling_mismatch_imp_partial_merkle_or_structural_gap)
  also have "... \<le>
      wp_event verify_monad (partial_merkle_inconsistency_bad s) s +
      wp_event verify_monad
        (trace_fri_header_tied_sibling_mismatch_structural_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> P + G"
    by (intro add_mono partial_merkle_bound gap_bound)
  finally show ?thesis .
qed

definition trace_fri_header_tied_base_value_alignment_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_base_value_alignment_gap s out \<longleftrightarrow>
    trace_fri_header_tied_sampled_base_opening_conflict s out \<and>
    \<not> trace_fri_header_tied_value_aligned_base_opening_conflict s out"

lemma trace_fri_header_tied_sampled_base_imp_value_aligned_or_gap:
  assumes "trace_fri_header_tied_sampled_base_opening_conflict s out"
  shows
    "trace_fri_header_tied_value_aligned_base_opening_conflict s out \<or>
     trace_fri_header_tied_base_value_alignment_gap s out"
  using assms
  unfolding trace_fri_header_tied_base_value_alignment_gap_def
  by blast

lemma wp_trace_fri_header_tied_sampled_base_bound_from_value_aligned_and_gap:
  fixes V G :: prob
  assumes value_aligned_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_value_aligned_base_opening_conflict s) s \<le> V"
    and gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_base_opening_conflict s) s \<le> V + G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_sampled_base_opening_conflict s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_value_aligned_base_opening_conflict s out \<or>
          trace_fri_header_tied_base_value_alignment_gap s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_sampled_base_imp_value_aligned_or_gap)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_value_aligned_base_opening_conflict s) s +
      wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> V + G"
    by (intro add_mono value_aligned_bound gap_bound)
  finally show ?thesis .
qed

lemma wp_trace_fri_header_tied_sampled_base_bound_from_sibling_mismatch_and_gap:
  fixes M G :: prob
  assumes mismatch_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_value_aligned_sibling_mismatch s) s \<le> M"
    and gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_base_opening_conflict s) s \<le> M + G"
  by (rule
      wp_trace_fri_header_tied_sampled_base_bound_from_value_aligned_and_gap)
    (rule wp_trace_fri_header_tied_value_aligned_base_bound_from_sibling_mismatch
      [OF mismatch_bound], rule gap_bound)

end

end
