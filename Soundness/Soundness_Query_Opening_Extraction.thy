(*  Title:      Stark/Soundness_Query_Opening_Extraction.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Query_Opening_Extraction
  imports Soundness_Partial_Merkle
begin

text \<open>
  Low-level verifier query extraction lemmas used by staged soundness.

  This layer is deliberately kept below the staged event definitions: it only
  talks about verifier query rounds, authenticated openings, transcript chunks,
  and random-oracle lookups.
\<close>

context soundness
begin

lemma query_opening_fri_layer_opening_step_partial_authenticated_table_first_value:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes len_pos: "0 < len"
    and idx_bound: "idx < len"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
  obtains openings where
    "partial_authenticated_table rt len openings t"
    "map opening_index openings = [idx, (idx + len div 2) mod len]"
    "length openings = 2"
    "opening_value (openings ! 0) = x"
proof -
  from outcome[unfolded fri_layer_opening_step_unfold_finish]
  obtain xp s1 xp_path s2 xn s3 xn_path s4 where
    read_xp: "Some (xp, s1) \<in> set_dist (execute read s)"
    and read_xp_path:
      "Some (xp_path, s2) \<in>
        set_dist (execute (ntimes read (floor_log len)) s1)"
    and read_xn: "Some (xn, s3) \<in> set_dist (execute read s2)"
    and read_xn_path:
      "Some (xn_path, s4) \<in>
        set_dist (execute (ntimes read (floor_log len)) s3)"
    and finish:
      "Some (out, t) \<in>
        set_dist
          (execute
            (fri_layer_opening_finish b rt idx x len pw xp xp_path xn
              xn_path) s4)"
    by (auto elim!: set_dist_bindE)
  have xp_path_length: "length xp_path = floor_log len"
    using ntimes_read_any_outcome[OF read_xp_path] by simp
  have xn_path_length: "length xn_path = floor_log len"
    using ntimes_read_any_outcome[OF read_xn_path] by simp
  have sibling_bound: "(idx + len div 2) mod len < len"
    using len_pos by simp
  have xp_x: "xp = x"
    using finish
    unfolding fri_layer_opening_finish_def assert_def
    by (auto simp: throw_no_outcome elim!: set_dist_bindE split: if_splits)
  from fri_layer_opening_finish_authenticated_openings
      [OF idx_bound sibling_bound xp_path_length xn_path_length finish]
  obtain xp_opening xn_opening where
    xp_eq:
      "xp_opening =
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path\<rparr>"
    and xn_eq:
      "xn_opening =
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = (idx + len div 2) mod len,
         opening_value = xn,
         opening_path = xn_path\<rparr>"
    and xp_auth: "authenticated_opening_in t xp_opening"
    and xn_auth: "authenticated_opening_in t xn_opening"
    by blast
  let ?openings = "[xp_opening, xn_opening]"
  have table: "partial_authenticated_table rt len ?openings t"
    unfolding partial_authenticated_table_def
    using xp_eq xn_eq xp_auth xn_auth by simp
  have indices:
    "map opening_index ?openings = [idx, (idx + len div 2) mod len]"
    using xp_eq xn_eq by simp
  have first_value: "opening_value (?openings ! 0) = x"
    using xp_eq xp_x by simp
  show ?thesis
    by (rule that[OF table indices _ first_value]) simp
qed

lemma query_opening_ntimes_outcome_decomp_at:
  assumes outcome:
      "Some (results, t) \<in> set_dist (execute (ntimes m n) s)"
    and i_bound: "i < n"
  shows
    "\<exists>prefix x suffix s_i s_suc.
      Some (prefix, s_i) \<in> set_dist (execute (ntimes m i) s) \<and>
      Some (x, s_suc) \<in> set_dist (execute m s_i) \<and>
      Some (suffix, t) \<in>
        set_dist (execute (ntimes m (n - Suc i)) s_suc) \<and>
      results = prefix @ x # suffix"
  using outcome i_bound
proof (induction n arbitrary: i s results t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain x results' s1 where
    head: "Some (x, s1) \<in> set_dist (execute m s)"
    and tail:
      "Some (results', t) \<in> set_dist (execute (ntimes m n) s1)"
    and results_eq: "results = x # results'"
    by (auto elim!: set_dist_bindE)
  show ?case
  proof (cases i)
    case 0
    have prefix0:
      "Some ([], s) \<in> set_dist (execute (ntimes m i) s)"
      using 0 by simp
    have suffix0:
      "Some (results', t) \<in>
        set_dist (execute (ntimes m (Suc n - Suc i)) s1)"
      using tail 0 by simp
    show ?thesis
      using prefix0 head suffix0 results_eq
      by (intro exI[of _ "[]"] exI[of _ x] exI[of _ results']
          exI[of _ s] exI[of _ s1]) simp
  next
    case (Suc j)
    have j_bound: "j < n"
      using Suc.prems(2) Suc by simp
    from Suc.IH[OF tail j_bound]
    obtain prefix y suffix s_j s_suc where
      prefix:
        "Some (prefix, s_j) \<in> set_dist (execute (ntimes m j) s1)"
      and round: "Some (y, s_suc) \<in> set_dist (execute m s_j)"
      and suffix:
        "Some (suffix, t) \<in>
          set_dist (execute (ntimes m (n - Suc j)) s_suc)"
      and results'_eq: "results' = prefix @ y # suffix"
      by blast
    have prefix_suc:
      "Some (x # prefix, s_j) \<in>
        set_dist (execute (ntimes m (Suc j)) s)"
      unfolding ntimes.simps
      apply (rule set_dist_bindI[OF head])
      apply (rule set_dist_bindI[OF prefix])
      apply simp
      done
    have n_minus: "Suc n - Suc (Suc j) = n - Suc j"
      by simp
    have suffix_suc:
      "Some (suffix, t) \<in>
        set_dist (execute (ntimes m (Suc n - Suc i)) s_suc)"
      using suffix n_minus Suc by simp
    show ?thesis
      using prefix_suc round suffix_suc results_eq results'_eq Suc
      by (intro exI[of _ "x # prefix"] exI[of _ y] exI[of _ suffix]
          exI[of _ s_j] exI[of _ s_suc]) simp
  qed
qed

lemma query_opening_verifier_query_round_program_authenticated_with_lookup:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx trace_leaves trace_openings composition_openings where
    "idx = index (to_nat raw)"
    "map opening_value trace_openings = trace_leaves"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  from outcome[unfolded verifier_query_round_program_alt_def]
  obtain raw s0 where rand:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and tail:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s0)"
    by (auto elim!: set_dist_bindE)
  have lookup_s0:
    "fmlookup (HashMap s0)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF rand] by simp
  have lookup_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using verifier_query_round_after_index_program_preserves_query_lookup
        [OF tail, of "PQueryCounter s" "PState s"] lookup_s0
    by simp
  show ?thesis
  proof (rule verifier_query_round_after_index_authenticated_trace_openings
      [OF tail])
    fix idx trace_leaves trace_openings
    assume idx_eq: "idx = index (to_nat raw)"
      and trace_values:
        "map opening_value trace_openings = trace_leaves"
      and trace_indices:
        "map opening_index trace_openings = powers_scaled idx"
      and trace_table:
        "partial_authenticated_table fr (scale * clength)
          trace_openings t"
    show ?thesis
    proof (rule
        verifier_query_round_after_index_authenticated_composition_openings
        [OF fl_eq tail])
      fix idx' composition_openings
      assume idx'_eq: "idx' = index (to_nat raw)"
        and comp_table:
          "partial_authenticated_table composition_root (scale * clength)
            composition_openings t"
        and comp_indices:
          "map opening_index composition_openings =
            [idx', fri_sibling_index (scale * clength) idx']"
      have idx'_idx: "idx' = idx"
        using idx_eq idx'_eq by simp
      show ?thesis
        by (rule that[OF idx_eq trace_values trace_indices trace_table
              comp_table _ lookup_t])
          (use comp_indices idx'_idx in simp)
    qed
  qed
qed

lemma query_opening_verifier_query_round_program_authenticated_with_chunk:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx chunk trace_leaves trace_openings composition_openings
  where
    "idx = index (to_nat raw)"
    "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    "PTranscript s = chunk @ PTranscript t"
    "PState t = foldl concat (PState s) chunk"
    "s \<le> t"
    "PQueryCounter t = Suc (PQueryCounter s)"
    "map opening_value trace_openings = trace_leaves"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
proof -
  show ?thesis
  proof (rule verifier_query_round_program_outcome[OF outcome])
    fix raw0 idx0 chunk
    assume idx0_eq: "idx0 = index (to_nat raw0)"
      and chunk_shape:
        "verifier_query_round_chunk idx0 (map snd f_fl) (map snd fl)
          chunk"
      and transcript:
        "PTranscript s = chunk @ PTranscript t"
      and state:
        "PState t = foldl concat (PState s) chunk"
      and ext: "s \<le> t"
      and counter:
        "PQueryCounter t = Suc (PQueryCounter s)"
      and lookup0:
        "fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw0"
    show ?thesis
    proof (rule
        query_opening_verifier_query_round_program_authenticated_with_lookup
          [OF fl_eq outcome])
      fix raw idx trace_leaves trace_openings composition_openings
      assume idx_eq: "idx = index (to_nat raw)"
        and trace_values:
          "map opening_value trace_openings = trace_leaves"
        and trace_indices:
          "map opening_index trace_openings = powers_scaled idx"
        and trace_table:
          "partial_authenticated_table fr (scale * clength)
            trace_openings t"
        and comp_table:
          "partial_authenticated_table composition_root (scale * clength)
            composition_openings t"
        and comp_indices:
          "map opening_index composition_openings =
            [idx, fri_sibling_index (scale * clength) idx]"
        and lookup:
          "fmlookup (HashMap t)
            (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
      have raw_eq: "raw = raw0"
        using lookup lookup0 by simp
      have idx_idx0: "idx = idx0"
        using idx_eq idx0_eq raw_eq by simp
      show ?thesis
        by (rule that[OF idx_eq _ transcript state ext counter
              trace_values trace_indices trace_table comp_table comp_indices
              lookup])
          (use chunk_shape idx_idx0 in simp)
    qed
  qed
qed

lemma query_opening_ntimes_prefix_state_alignment:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (prefix, t) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final) i)
          s)"
  obtains prefix_chunks where
    "length prefix_chunks = i"
    "PState t = state_after_query_chunks (PState s) prefix_chunks i"
    "PQueryCounter t = PQueryCounter s + i"
    "s \<le> t"
proof -
  from ntimes_verifier_query_rounds_outcome[OF outcome]
  obtain raw_idxs query_idxs prefix_chunks where
    len_chunks: "length prefix_chunks = i"
    and state:
      "PState t = state_after_query_chunks (PState s) prefix_chunks i"
    and ext: "s \<le> t"
    and counter: "PQueryCounter t = PQueryCounter s + i"
    by blast
  show ?thesis
    by (rule that[OF len_chunks state counter ext])
qed

lemma query_opening_ntimes_prefix_transcript_state_alignment:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (prefix, t) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final) i)
          s)"
  obtains prefix_query_idxs prefix_chunks where
    "length prefix_query_idxs = i"
    "length prefix_chunks = i"
    "PTranscript s = List.concat prefix_chunks @ PTranscript t"
    "PState t = state_after_query_chunks (PState s) prefix_chunks i"
    "PQueryCounter t = PQueryCounter s + i"
    "s \<le> t"
    "\<And>j. j < i \<Longrightarrow>
      verifier_query_round_chunk (prefix_query_idxs ! j)
        (map snd f_fl) (map snd fl) (prefix_chunks ! j)"
proof -
  from ntimes_verifier_query_rounds_outcome[OF outcome]
  obtain raw_idxs query_idxs prefix_chunks where
    len_raw_idxs: "length raw_idxs = i"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and
    len_chunks: "length prefix_chunks = i"
    and transcript:
      "PTranscript s = List.concat prefix_chunks @ PTranscript t"
    and state:
      "PState t = state_after_query_chunks (PState s) prefix_chunks i"
    and ext: "s \<le> t"
    and counter: "PQueryCounter t = PQueryCounter s + i"
    and rounds:
      "\<And>j. j < i \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! j)
          (map snd f_fl) (map snd fl) (prefix_chunks ! j)"
    by blast
  have len_idxs: "length query_idxs = i"
    using len_raw_idxs query_idxs_eq by simp
  show ?thesis
    by (rule that[OF len_idxs len_chunks transcript state counter ext])
      (use rounds in blast)
qed

lemma query_opening_ntimes_suffix_extends:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (suffix, t) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final) n)
          s)"
  shows "s \<le> t"
proof -
  from ntimes_verifier_query_rounds_outcome[OF outcome]
  show ?thesis
    by blast
qed

lemma query_opening_ntimes_suffix_transcript_state_alignment:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
    "Some (suffix, t) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl f_final as fl final) n)
          s)"
  obtains suffix_query_idxs suffix_chunks where
    "length suffix_query_idxs = n"
    "length suffix_chunks = n"
    "PTranscript s = List.concat suffix_chunks @ PTranscript t"
    "PState t = state_after_query_chunks (PState s) suffix_chunks n"
    "PQueryCounter t = PQueryCounter s + n"
    "s \<le> t"
    "\<And>j. j < n \<Longrightarrow>
      verifier_query_round_chunk (suffix_query_idxs ! j)
        (map snd f_fl) (map snd fl) (suffix_chunks ! j)"
proof -
  from ntimes_verifier_query_rounds_outcome[OF outcome]
  obtain raw_idxs query_idxs suffix_chunks where
    len_raw_idxs: "length raw_idxs = n"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_chunks: "length suffix_chunks = n"
    and transcript:
      "PTranscript s = List.concat suffix_chunks @ PTranscript t"
    and state:
      "PState t = state_after_query_chunks (PState s) suffix_chunks n"
    and ext: "s \<le> t"
    and counter: "PQueryCounter t = PQueryCounter s + n"
    and rounds:
      "\<And>j. j < n \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! j)
          (map snd f_fl) (map snd fl) (suffix_chunks ! j)"
    by blast
  have len_idxs: "length query_idxs = n"
    using len_raw_idxs query_idxs_eq by simp
  show ?thesis
    by (rule that[OF len_idxs len_chunks transcript state counter ext])
      (use rounds in blast)
qed

lemma query_opening_ntimes_authenticated_initial_openings_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, composition_root) # fl_tail"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl f_final as fl final) n)
            s)"
    and i_bound: "i < n"
  obtains raw idx prefix_chunks trace_openings composition_openings where
    "idx = index (to_nat raw)"
    "length prefix_chunks = i"
    "map opening_index trace_openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) trace_openings t"
    "partial_authenticated_table composition_root (scale * clength)
      composition_openings t"
    "map opening_index composition_openings =
      [idx, fri_sibling_index (scale * clength) idx]"
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
  proof (rule
      query_opening_verifier_query_round_program_authenticated_with_chunk
      [OF fl_eq round[unfolded round_unit]])
    fix raw idx chunk trace_leaves trace_openings composition_openings
    assume idx_eq: "idx = index (to_nat raw)"
      and chunk_shape:
        "verifier_query_round_chunk idx (map snd f_fl) (map snd fl)
          chunk"
      and transcript: "PTranscript s_i = chunk @ PTranscript s_suc"
      and state_suc: "PState s_suc = foldl concat (PState s_i) chunk"
      and ext_round: "s_i \<le> s_suc"
      and counter_suc: "PQueryCounter s_suc = Suc (PQueryCounter s_i)"
      and trace_values: "map opening_value trace_openings = trace_leaves"
      and trace_indices:
        "map opening_index trace_openings = powers_scaled idx"
      and trace_table_suc:
        "partial_authenticated_table fr (scale * clength)
          trace_openings s_suc"
      and comp_table_suc:
        "partial_authenticated_table composition_root (scale * clength)
          composition_openings s_suc"
      and comp_indices:
        "map opening_index composition_openings =
          [idx, fri_sibling_index (scale * clength) idx]"
      and lookup_suc:
        "fmlookup (HashMap s_suc)
          (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw"
    show ?thesis
    proof (rule query_opening_ntimes_prefix_state_alignment[OF prefix])
      fix prefix_chunks
      assume len_chunks: "length prefix_chunks = i"
        and state_i:
          "PState s_i =
            state_after_query_chunks (PState s) prefix_chunks i"
        and counter_i: "PQueryCounter s_i = PQueryCounter s + i"
      have suffix_ext: "s_suc \<le> t"
        by (rule query_opening_ntimes_suffix_extends[OF suffix])
      have trace_table_t:
        "partial_authenticated_table fr (scale * clength)
          trace_openings t"
        by (rule
            partial_authenticated_table_mono[OF trace_table_suc
              suffix_ext])
      have comp_table_t:
        "partial_authenticated_table composition_root (scale * clength)
          composition_openings t"
        by (rule
            partial_authenticated_table_mono[OF comp_table_suc suffix_ext])
      have lookup_t:
        "fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) prefix_chunks i)) =
          Some raw"
        using hash_extension_lookup[OF lookup_suc suffix_ext]
        unfolding counter_i state_i .
      show ?thesis
        by (rule that[OF idx_eq len_chunks trace_indices trace_table_t
              comp_table_t comp_indices lookup_t])
    qed
  qed
qed

end

end
