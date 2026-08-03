(*  Title:      Stark/Soundness_FRI_Final_Step_Replay.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Final_Step_Replay
  imports Soundness_FRI_Raw_Layer_Bounds
begin

text \<open>
  Selected final-step replay for trace FRI openings.

  This layer lifts the monadic replay fact for the last trace FRI fold step
  through the accepted FRI transcript.  It keeps the result local to sampled
  verifier evidence and does not reconstruct complete FRI tables.
\<close>

context soundness
begin

lemma accepted_fri_opening_transcript_trace_final_step_evidence_at:
  assumes fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and round_bound: "i < rounds"
    and nonempty: "0 < length trace_roots"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length trace_roots) (clength * scale) !
          (length trace_roots - 1) \<and>
        fri_layer_indices (length trace_roots) (index (to_nat raw))
          (clength * scale) ! (length trace_roots - 1) <
        fri_layer_lengths (length trace_roots) (clength * scale) !
          (length trace_roots - 1)"
  obtains actual_chunk axp axp_path axn axn_path where
    "fri_layer_chunk_authenticated
      (trace_roots ! (length trace_roots - 1))
      (fri_evidence_layer_len trace_roots (length trace_roots - 1))
      (fri_evidence_layer_idx trace_roots query_idxs i
        (length trace_roots - 1))
      actual_chunk final_state"
    "fri_layer_step_evidence
      (trace_roots ! (length trace_roots - 1))
      (trace_bs ! (length trace_roots - 1))
      (fri_evidence_layer_len trace_roots (length trace_roots - 1))
      (fri_evidence_layer_idx trace_roots query_idxs i
        (length trace_roots - 1))
      (2 ^ (length trace_roots - 1))
      (fri_sibling_index
        (fri_evidence_layer_len trace_roots (length trace_roots - 1))
        (fri_evidence_layer_idx trace_roots query_idxs i
          (length trace_roots - 1)))
      axp axp_path axn axn_path
      (fri_evidence_next_idx trace_roots query_idxs i
        (length trace_roots - 1))
      trace_final actual_chunk"
proof -
  from fri_openings obtain result' final_state' fr f_fl as fl query_state
      raw_idxs query_chunks where
    out_def: "out = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and trace_bs_eq: "trace_bs = map fst f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and query_out:
      "Some (result', final_state') \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl trace_final as fl
                composition_final)
              rounds)
            query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state'"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    unfolding accepted_fri_opening_transcript_def by blast
  have result_eq: "result' = result"
    using out_def out_eq by simp
  have final_state_eq: "final_state' = final_state"
    using out_def out_eq by simp
  have query_out':
    "Some (result, final_state) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl trace_final as fl
              composition_final)
            rounds)
          query_state)"
    using query_out result_eq final_state_eq by simp
  have f_fl_nonempty: "0 < length f_fl"
    using nonempty trace_roots_eq by simp
  have raw_layer_f:
    "\<And>raw.
      0 < fri_layer_lengths (length f_fl) (clength * scale) !
        (length f_fl - 1) \<and>
      fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! (length f_fl - 1) <
      fri_layer_lengths (length f_fl) (clength * scale) !
        (length f_fl - 1)"
    using raw_layer trace_roots_eq by simp
  from ntimes_verifier_query_rounds_selected_trace_fri_last_step_with_prefix_at
      [OF query_out' round_bound f_fl_nonempty raw_layer_f]
  obtain raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
      suffix_chunks actual_chunk axp axp_path axn axn_path where
    idx_eq: "idx = index (to_nat raw)"
    and len_prefix_idxs: "length prefix_query_idxs = i"
    and len_prefix_chunks: "length prefix_chunks = i"
    and len_suffix_idxs: "length suffix_query_idxs = rounds - Suc i"
    and len_suffix_chunks: "length suffix_chunks = rounds - Suc i"
    and chunk_shape:
      "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    and prefix_rounds:
      "\<And>k. k < i \<Longrightarrow>
        verifier_query_round_chunk (prefix_query_idxs ! k)
          (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    and suffix_rounds:
      "\<And>k. k < rounds - Suc i \<Longrightarrow>
        verifier_query_round_chunk (suffix_query_idxs ! k)
          (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
    and selected_transcript:
      "PTranscript query_state =
        List.concat (prefix_chunks @ chunk # suffix_chunks) @
          PTranscript final_state"
    and auth:
      "fri_layer_chunk_authenticated
        (snd (f_fl ! (length f_fl - 1)))
        (fri_layer_lengths (length f_fl) (clength * scale) !
          (length f_fl - 1))
        (fri_layer_indices (length f_fl) idx (clength * scale) !
          (length f_fl - 1))
        actual_chunk final_state"
    and step:
      "fri_layer_step_evidence
        (snd (f_fl ! (length f_fl - 1)))
        (fst (f_fl ! (length f_fl - 1)))
        (fri_layer_lengths (length f_fl) (clength * scale) !
          (length f_fl - 1))
        (fri_layer_indices (length f_fl) idx (clength * scale) !
          (length f_fl - 1))
        (2 ^ (length f_fl - 1))
        (fri_sibling_index
          (fri_layer_lengths (length f_fl) (clength * scale) !
            (length f_fl - 1))
          (fri_layer_indices (length f_fl) idx (clength * scale) !
            (length f_fl - 1)))
        axp axp_path axn axn_path
        ((fri_layer_indices (length f_fl) idx (clength * scale) !
            (length f_fl - 1)) mod
          ((fri_layer_lengths (length f_fl) (clength * scale) !
            (length f_fl - 1)) div 2))
        trace_final actual_chunk"
    and selected_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) prefix_chunks i)) =
      Some raw"
    by (rule
        ntimes_verifier_query_rounds_selected_trace_fri_last_step_with_prefix_at
          [OF query_out' round_bound f_fl_nonempty raw_layer_f])
      (rule that, assumption+)
  let ?selected_chunks = "prefix_chunks @ chunk # suffix_chunks"
  have len_selected_chunks: "length ?selected_chunks = rounds"
    using len_prefix_chunks len_suffix_chunks round_bound by simp
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
        by (rule verifier_query_round_chunk_length[OF prefix_rounds[OF True]])
      then show ?thesis
        using nth_eq
        by (simp add: verifier_query_round_transcript_length_index_irrelevant)
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
          by (simp add: verifier_query_round_transcript_length_index_irrelevant)
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
          by (simp add: verifier_query_round_transcript_length_index_irrelevant)
      qed
    qed
  qed
  have query_chunk_lens:
    "\<And>k. k < rounds \<Longrightarrow>
      length (query_chunks ! k) =
        verifier_query_round_transcript_length (query_idxs ! k)
          (map snd f_fl) (map snd fl)"
  proof -
    fix k
    assume k_bound: "k < rounds"
    have
      "verifier_query_round_chunk (query_idxs ! k)
        (map snd f_fl) (map snd fl) (query_chunks ! k)"
      using query_chunk[OF k_bound] trace_roots_eq composition_roots_eq
      by simp
    then show
      "length (query_chunks ! k) =
        verifier_query_round_transcript_length (query_idxs ! k)
          (map snd f_fl) (map snd fl)"
      by (rule verifier_query_round_chunk_length)
  qed
  have concat_eq: "List.concat ?selected_chunks = List.concat query_chunks"
    using selected_transcript transcript_query final_state_eq by simp
  have chunks_eq: "?selected_chunks = query_chunks"
  proof -
    have same_lens:
      "\<And>k. k < length ?selected_chunks \<Longrightarrow>
        length (?selected_chunks ! k) = length (query_chunks ! k)"
      using selected_chunk_lens query_chunk_lens len_selected_chunks by simp
    have concat_eq_empty:
      "List.concat ?selected_chunks @ [] = List.concat query_chunks"
      using concat_eq by simp
    have len_eq: "length ?selected_chunks = length query_chunks"
      using len_selected_chunks len_query_chunks by simp
    have "?selected_chunks = query_chunks \<and> ([] :: 'f list) = []"
      by (rule concat_append_eq_concat_same_chunk_lengths
          [OF len_eq same_lens concat_eq_empty])
    then show ?thesis by simp
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
    using selected_lookup_global replay_lookup[OF round_bound]
      final_state_eq by simp
  have idx_eq_query: "idx = query_idxs ! i"
    using idx_eq raw_eq query_idxs_eq len_raw round_bound by simp
  have auth':
    "fri_layer_chunk_authenticated
      (trace_roots ! (length trace_roots - 1))
      (fri_evidence_layer_len trace_roots (length trace_roots - 1))
      (fri_evidence_layer_idx trace_roots query_idxs i
        (length trace_roots - 1))
      actual_chunk final_state"
    using auth idx_eq_query trace_roots_eq f_fl_nonempty
    unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
    by simp
  have step':
    "fri_layer_step_evidence
      (trace_roots ! (length trace_roots - 1))
      (trace_bs ! (length trace_roots - 1))
      (fri_evidence_layer_len trace_roots (length trace_roots - 1))
      (fri_evidence_layer_idx trace_roots query_idxs i
        (length trace_roots - 1))
      (2 ^ (length trace_roots - 1))
      (fri_sibling_index
        (fri_evidence_layer_len trace_roots (length trace_roots - 1))
        (fri_evidence_layer_idx trace_roots query_idxs i
          (length trace_roots - 1)))
      axp axp_path axn axn_path
      (fri_evidence_next_idx trace_roots query_idxs i
        (length trace_roots - 1))
      trace_final actual_chunk"
    using step idx_eq_query trace_roots_eq trace_bs_eq f_fl_nonempty
    unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
      fri_evidence_next_idx_def
    by simp
  show ?thesis
    by (rule that[OF auth' step'])
qed

lemma accepted_fri_opening_transcript_composition_final_step_evidence_at:
  assumes fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and round_bound: "i < rounds"
    and nonempty: "0 < length composition_roots"
    and raw_layer:
      "\<And>raw.
        0 < fri_layer_lengths (length composition_roots) (clength * scale) !
          (length composition_roots - 1) \<and>
        fri_layer_indices (length composition_roots) (index (to_nat raw))
          (clength * scale) ! (length composition_roots - 1) <
        fri_layer_lengths (length composition_roots) (clength * scale) !
          (length composition_roots - 1)"
  obtains actual_chunk axp axp_path axn axn_path where
    "fri_layer_chunk_authenticated
      (composition_roots ! (length composition_roots - 1))
      (fri_evidence_layer_len composition_roots (length composition_roots - 1))
      (fri_evidence_layer_idx composition_roots query_idxs i
        (length composition_roots - 1))
      actual_chunk final_state"
    "fri_layer_step_evidence
      (composition_roots ! (length composition_roots - 1))
      (composition_bs ! (length composition_roots - 1))
      (fri_evidence_layer_len composition_roots (length composition_roots - 1))
      (fri_evidence_layer_idx composition_roots query_idxs i
        (length composition_roots - 1))
      (2 ^ (length composition_roots - 1))
      (fri_sibling_index
        (fri_evidence_layer_len composition_roots (length composition_roots - 1))
        (fri_evidence_layer_idx composition_roots query_idxs i
          (length composition_roots - 1)))
      axp axp_path axn axn_path
      (fri_evidence_next_idx composition_roots query_idxs i
        (length composition_roots - 1))
      composition_final actual_chunk"
proof -
  from fri_openings obtain result' final_state' fr f_fl as fl query_state
      raw_idxs query_chunks where
    out_def: "out = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_bs_eq: "composition_bs = map fst fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and query_out:
      "Some (result', final_state') \<in>
        set_dist
          (execute
            (ntimes
              (verifier_query_round_program fr f_fl trace_final as fl
                composition_final)
              rounds)
            query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq:
      "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state'"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    unfolding accepted_fri_opening_transcript_def by blast
  have result_eq: "result' = result"
    using out_def out_eq by simp
  have final_state_eq: "final_state' = final_state"
    using out_def out_eq by simp
  have query_out':
    "Some (result, final_state) \<in>
      set_dist
        (execute
          (ntimes
            (verifier_query_round_program fr f_fl trace_final as fl
              composition_final)
            rounds)
          query_state)"
    using query_out result_eq final_state_eq by simp
  have fl_nonempty: "0 < length fl"
    using nonempty composition_roots_eq by simp
  have raw_layer_fl:
    "\<And>raw.
      0 < fri_layer_lengths (length fl) (clength * scale) !
        (length fl - 1) \<and>
      fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! (length fl - 1) <
      fri_layer_lengths (length fl) (clength * scale) !
        (length fl - 1)"
    using raw_layer composition_roots_eq by simp
  from ntimes_verifier_query_rounds_selected_composition_fri_last_step_with_prefix_at
      [OF query_out' round_bound fl_nonempty raw_layer_fl]
  obtain raw idx prefix_query_idxs prefix_chunks chunk suffix_query_idxs
      suffix_chunks actual_chunk axp axp_path axn axn_path where
    idx_eq: "idx = index (to_nat raw)"
    and len_prefix_idxs: "length prefix_query_idxs = i"
    and len_prefix_chunks: "length prefix_chunks = i"
    and len_suffix_idxs: "length suffix_query_idxs = rounds - Suc i"
    and len_suffix_chunks: "length suffix_chunks = rounds - Suc i"
    and chunk_shape:
      "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    and prefix_rounds:
      "\<And>k. k < i \<Longrightarrow>
        verifier_query_round_chunk (prefix_query_idxs ! k)
          (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    and suffix_rounds:
      "\<And>k. k < rounds - Suc i \<Longrightarrow>
        verifier_query_round_chunk (suffix_query_idxs ! k)
          (map snd f_fl) (map snd fl) (suffix_chunks ! k)"
    and selected_transcript:
      "PTranscript query_state =
        List.concat (prefix_chunks @ chunk # suffix_chunks) @
          PTranscript final_state"
    and auth:
      "fri_layer_chunk_authenticated
        (snd (fl ! (length fl - 1)))
        (fri_layer_lengths (length fl) (clength * scale) !
          (length fl - 1))
        (fri_layer_indices (length fl) idx (clength * scale) !
          (length fl - 1))
        actual_chunk final_state"
    and step:
      "fri_layer_step_evidence
        (snd (fl ! (length fl - 1)))
        (fst (fl ! (length fl - 1)))
        (fri_layer_lengths (length fl) (clength * scale) !
          (length fl - 1))
        (fri_layer_indices (length fl) idx (clength * scale) !
          (length fl - 1))
        (2 ^ (length fl - 1))
        (fri_sibling_index
          (fri_layer_lengths (length fl) (clength * scale) !
            (length fl - 1))
          (fri_layer_indices (length fl) idx (clength * scale) !
            (length fl - 1)))
        axp axp_path axn axn_path
        ((fri_layer_indices (length fl) idx (clength * scale) !
            (length fl - 1)) mod
          ((fri_layer_lengths (length fl) (clength * scale) !
            (length fl - 1)) div 2))
        composition_final actual_chunk"
    and selected_lookup:
      "fmlookup (HashMap final_state)
        (QueryIndexChallenge (PQueryCounter query_state + i)
          (state_after_query_chunks (PState query_state) prefix_chunks i)) =
      Some raw"
    by (rule
        ntimes_verifier_query_rounds_selected_composition_fri_last_step_with_prefix_at
          [OF query_out' round_bound fl_nonempty raw_layer_fl])
      (rule that, assumption+)
  let ?selected_chunks = "prefix_chunks @ chunk # suffix_chunks"
  have len_selected_chunks: "length ?selected_chunks = rounds"
    using len_prefix_chunks len_suffix_chunks round_bound by simp
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
        by (rule verifier_query_round_chunk_length[OF prefix_rounds[OF True]])
      then show ?thesis
        using nth_eq
        by (simp add: verifier_query_round_transcript_length_index_irrelevant)
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
          by (simp add: verifier_query_round_transcript_length_index_irrelevant)
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
          by (simp add: verifier_query_round_transcript_length_index_irrelevant)
      qed
    qed
  qed
  have query_chunk_lens:
    "\<And>k. k < rounds \<Longrightarrow>
      length (query_chunks ! k) =
        verifier_query_round_transcript_length (query_idxs ! k)
          (map snd f_fl) (map snd fl)"
  proof -
    fix k
    assume k_bound: "k < rounds"
    have
      "verifier_query_round_chunk (query_idxs ! k)
        (map snd f_fl) (map snd fl) (query_chunks ! k)"
      using query_chunk[OF k_bound] trace_roots_eq composition_roots_eq
      by simp
    then show
      "length (query_chunks ! k) =
        verifier_query_round_transcript_length (query_idxs ! k)
          (map snd f_fl) (map snd fl)"
      by (rule verifier_query_round_chunk_length)
  qed
  have concat_eq: "List.concat ?selected_chunks = List.concat query_chunks"
    using selected_transcript transcript_query final_state_eq by simp
  have chunks_eq: "?selected_chunks = query_chunks"
  proof -
    have same_lens:
      "\<And>k. k < length ?selected_chunks \<Longrightarrow>
        length (?selected_chunks ! k) = length (query_chunks ! k)"
      using selected_chunk_lens query_chunk_lens len_selected_chunks by simp
    have concat_eq_empty:
      "List.concat ?selected_chunks @ [] = List.concat query_chunks"
      using concat_eq by simp
    have len_eq: "length ?selected_chunks = length query_chunks"
      using len_selected_chunks len_query_chunks by simp
    have "?selected_chunks = query_chunks \<and> ([] :: 'f list) = []"
      by (rule concat_append_eq_concat_same_chunk_lengths
          [OF len_eq same_lens concat_eq_empty])
    then show ?thesis by simp
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
    using selected_lookup_global replay_lookup[OF round_bound]
      final_state_eq by simp
  have idx_eq_query: "idx = query_idxs ! i"
    using idx_eq raw_eq query_idxs_eq len_raw round_bound by simp
  have auth':
    "fri_layer_chunk_authenticated
      (composition_roots ! (length composition_roots - 1))
      (fri_evidence_layer_len composition_roots (length composition_roots - 1))
      (fri_evidence_layer_idx composition_roots query_idxs i
        (length composition_roots - 1))
      actual_chunk final_state"
    using auth idx_eq_query composition_roots_eq fl_nonempty
    unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
    by simp
  have step':
    "fri_layer_step_evidence
      (composition_roots ! (length composition_roots - 1))
      (composition_bs ! (length composition_roots - 1))
      (fri_evidence_layer_len composition_roots (length composition_roots - 1))
      (fri_evidence_layer_idx composition_roots query_idxs i
        (length composition_roots - 1))
      (2 ^ (length composition_roots - 1))
      (fri_sibling_index
        (fri_evidence_layer_len composition_roots (length composition_roots - 1))
        (fri_evidence_layer_idx composition_roots query_idxs i
          (length composition_roots - 1)))
      axp axp_path axn axn_path
      (fri_evidence_next_idx composition_roots query_idxs i
        (length composition_roots - 1))
      composition_final actual_chunk"
    using step idx_eq_query composition_roots_eq composition_bs_eq fl_nonempty
    unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
      fri_evidence_next_idx_def
    by simp
  show ?thesis
    by (rule that[OF auth' step'])
qed

end

end
