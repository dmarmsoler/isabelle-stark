(*  Title:      Stark/Soundness_FRI_Trace_Head_Value.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Trace_Head_Value
  imports
    Soundness_FRI_Trace_Residuals
    Soundness_FRI_Query_Openings
begin

text \<open>
  Local replay facts for the trace base head-value residual.  This theory keeps
  the exact selected trace-layer replay needed by the residual proof out of the
  already large trace residual layer.
\<close>

context soundness
begin

lemma verifier_query_round_program_trace_fri_head_layer_value_aligned_with_lookup:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx openings query_chunk trace_layer_chunks
      composition_layer_chunks xp xp_path xn xn_path where
    "idx = index (to_nat raw)"
    "query_round_fri_layer_transcripts idx (map snd f_fl) (map snd fl)
      query_chunk trace_layer_chunks composition_layer_chunks"
    "PTranscript s = query_chunk @ PTranscript t"
    "PState t = foldl concat (PState s) query_chunk"
    "s \<le> t"
    "map opening_index openings = powers_scaled idx"
    "partial_authenticated_table fr (scale * clength) openings t"
    "openings \<noteq> []"
    "opening_value (hd openings) = xp"
    "fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
      (trace_layer_chunks ! 0)"
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
  obtain idx openings query_chunk trace_layer_chunks composition_layer_chunks
      xp xp_path xn xn_path
  where idx_eq: "idx = index (to_nat raw)"
    and layers:
      "query_round_fri_layer_transcripts idx (map snd f_fl) (map snd fl)
        query_chunk trace_layer_chunks composition_layer_chunks"
    and tr_t: "PTranscript s0 = query_chunk @ PTranscript t"
    and st_t: "PState t = foldl concat (PState s0) query_chunk"
    and ext_s0_t: "s0 \<le> t"
    and idxs: "map opening_index openings = powers_scaled idx"
    and auth_table:
      "partial_authenticated_table fr (scale * clength) openings t"
    and nonempty: "openings \<noteq> []"
    and opening_value_eq: "opening_value (hd openings) = xp"
    and head_chunk:
      "fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
        (trace_layer_chunks ! 0)"
    using verifier_query_round_after_index_trace_fri_head_layer_value_aligned
      [OF f_fl_eq tail]
    by metis
  have lookup_s0:
    "fmlookup (HashMap s0)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF raw] by simp
  have lookup_t:
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF lookup_s0 ext_s0_t])
  have tr_s0: "PTranscript s = PTranscript s0"
    using receive_query_index_challenge_outcome[OF raw] by simp
  have st_s0: "PState s0 = PState s"
    using receive_query_index_challenge_outcome[OF raw] by simp
  have ext_s_s0: "s \<le> s0"
    using receive_query_index_challenge_outcome[OF raw] by simp
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_s0 ext_s0_t])
  have tr_goal: "PTranscript s = query_chunk @ PTranscript t"
    using tr_t tr_s0 by simp
  have st_goal: "PState t = foldl concat (PState s) query_chunk"
    using st_t st_s0 by simp
  show ?thesis
    by (rule that[OF idx_eq layers tr_goal st_goal ext_s_t idxs auth_table
          nonempty opening_value_eq head_chunk lookup_t])
qed

lemma ntimes_verifier_query_rounds_selected_trace_fri_head_layer_value_aligned_with_replay_at:
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
    and query_layers:
      "query_round_fri_layer_transcripts (query_idxs ! i)
        (map snd f_fl) (map snd fl) (query_chunks ! i)
        trace_layer_chunks composition_layer_chunks"
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
      (trace_layer_chunks ! 0)"
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
    proof (rule
        verifier_query_round_program_trace_fri_head_layer_value_aligned_with_lookup
          [OF f_fl_eq round[unfolded x_eq]])
      fix raw idx chunk actual_trace_layers actual_composition_layers
        openings xp xp_path xn xn_path
      assume idx_eq: "idx = index (to_nat raw)"
        and actual_layers:
          "query_round_fri_layer_transcripts idx (map snd f_fl)
            (map snd fl) chunk actual_trace_layers actual_composition_layers"
        and transcript_round: "PTranscript s_i = chunk @ PTranscript s_suc"
        and state_suc: "PState s_suc = foldl concat (PState s_i) chunk"
        and round_ext: "s_i \<le> s_suc"
        and opening_indices: "map opening_index openings = powers_scaled idx"
        and auth_table_suc:
          "partial_authenticated_table fr (scale * clength) openings s_suc"
        and openings_nonempty: "openings \<noteq> []"
        and opening_value_eq: "opening_value (hd openings) = xp"
        and head_chunk:
          "fri_layer_opening_chunk (scale * clength) xp xp_path xn
            xn_path (actual_trace_layers ! 0)"
        and lookup_suc:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
            Some raw"
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
              have chunk_shape:
                "verifier_query_round_chunk idx (map snd f_fl) (map snd fl)
                  chunk"
                unfolding verifier_query_round_chunk_def
                using actual_layers
                unfolding query_round_fri_layer_transcripts_def by blast
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
        have selected_nth: "?selected_chunks ! i = chunk"
          using len_prefix_chunks by (simp add: nth_append)
        have actual_layers_query:
          "query_round_fri_layer_transcripts (query_idxs ! i)
            (map snd f_fl) (map snd fl) (query_chunks ! i)
            actual_trace_layers actual_composition_layers"
          using actual_layers idx_eq_query chunks_eq selected_nth by simp
        have actual_trace_layers_eq:
          "actual_trace_layers = trace_layer_chunks"
          by (rule query_round_fri_layer_transcripts_unique(1)
              [OF actual_layers_query query_layers])
        show ?thesis
          by (rule that[OF _ auth_table_final openings_nonempty
                opening_value_eq])
            (use opening_indices idx_eq_query head_chunk
              actual_trace_layers_eq in simp_all)
      qed
    qed
  qed
qed

lemma accepted_fri_opening_transcript_trace_head_layer_value_aligned_at:
  assumes fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
        query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final header_as dg
        composition_roots composition_final header_rest"
    and out_eq: "out = Some (result, final_state)"
    and round_bound: "round_idx < length query_idxs"
    and trace_bs_nonempty: "0 < length trace_bs"
  obtains openings xp xp_path xn xn_path where
    "map opening_index openings = powers_scaled (query_idxs ! round_idx)"
    "partial_authenticated_table fr (scale * clength) openings final_state"
    "openings \<noteq> []"
    "opening_value (hd openings) = xp"
    "fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
      (trace_round_layers ! round_idx ! 0)"
proof -
  from fri_openings obtain result' final_state' fr' f_fl as fl query_state
      raw_idxs query_chunks
  where out_def: "out = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and trace_bs_eq: "trace_bs = map fst f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and header':
      "verifier_header_transcript s fr' trace_roots trace_final as dg
        composition_roots composition_final (PTranscript query_state)"
    and query_out:
      "Some (result', final_state') \<in>
        set_dist (execute
          (ntimes
            (verifier_query_round_program fr' f_fl trace_final as fl
              composition_final)
            rounds)
          query_state)"
    and len_raw: "length raw_idxs = rounds"
    and query_idxs_eq: "query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs"
    and len_query_chunks: "length query_chunks = rounds"
    and transcript_query:
      "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state'"
    and query_chunk:
      "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)"
    and query_layers:
      "\<And>i. i < rounds \<Longrightarrow>
        query_round_fri_layer_transcripts (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)
          (trace_round_layers ! i) (composition_round_layers ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    unfolding accepted_fri_opening_transcript_def by blast
  have fr'_eq: "fr' = fr"
    using verifier_header_transcript_unique[OF header header'] by simp
  have result'_eq: "result' = result"
    using out_def out_eq by simp
  have final_state'_eq: "final_state' = final_state"
    using out_def out_eq by simp
  have query_out':
    "Some (result, final_state) \<in>
      set_dist (execute
        (ntimes
          (verifier_query_round_program fr' f_fl trace_final as fl
            composition_final)
          rounds)
        query_state)"
    using query_out result'_eq final_state'_eq by simp
  have round_bound_rounds: "round_idx < rounds"
    using round_bound
      accepted_fri_opening_transcript_shapes(7)[OF fri_openings]
    by simp
  obtain b rt f_fl_tail where f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
  proof (cases f_fl)
    case Nil
    then show ?thesis
      using trace_bs_nonempty trace_bs_eq by simp
  next
    case (Cons head tail)
    then obtain b rt where head_eq: "head = (b, rt)"
      by (cases head)
    then show ?thesis
      using Cons that by simp
  qed
  have query_layer:
    "query_round_fri_layer_transcripts (query_idxs ! round_idx)
      (map snd f_fl) (map snd fl) (query_chunks ! round_idx)
      (trace_round_layers ! round_idx)
      (composition_round_layers ! round_idx)"
    using query_layers[OF round_bound_rounds]
      trace_roots_eq composition_roots_eq by simp
  have ex:
    "\<exists>openings xp xp_path xn xn_path.
      map opening_index openings = powers_scaled (query_idxs ! round_idx) \<and>
      partial_authenticated_table fr' (scale * clength) openings final_state \<and>
      openings \<noteq> [] \<and>
      opening_value (hd openings) = xp \<and>
      fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
        (trace_round_layers ! round_idx ! 0)"
  proof (rule
      ntimes_verifier_query_rounds_selected_trace_fri_head_layer_value_aligned_with_replay_at
        [OF f_fl_eq query_out' round_bound_rounds len_raw query_idxs_eq
          len_query_chunks])
    show "PTranscript query_state =
        List.concat query_chunks @ PTranscript final_state"
      using transcript_query final_state'_eq by simp
    show "\<And>i. i < rounds \<Longrightarrow>
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
      using query_chunk trace_roots_eq composition_roots_eq by simp
    show "query_round_fri_layer_transcripts (query_idxs ! round_idx)
        (map snd f_fl) (map snd fl) (query_chunks ! round_idx)
        (trace_round_layers ! round_idx)
        (composition_round_layers ! round_idx)"
      by (rule query_layer)
    show "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state)
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks
              (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
      using replay_lookup final_state'_eq by simp
  next
    fix openings xp xp_path xn xn_path
    assume "map opening_index openings =
        powers_scaled (query_idxs ! round_idx)"
      and "partial_authenticated_table fr' (scale * clength) openings
        final_state"
      and "openings \<noteq> []"
      and "opening_value (hd openings) = xp"
      and "fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
        (trace_round_layers ! round_idx ! 0)"
    then show ?thesis
      by blast
  qed
  from ex show ?thesis
    by (metis fr'_eq that)
qed

lemma trace_fri_header_tied_base_head_value_neq_gap_imp_partial_merkle:
  assumes "trace_fri_header_tied_base_head_value_neq_gap s out"
  shows "partial_merkle_inconsistency_bad s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      round_idx xp xp_path xn xn_path result final_state
  where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and candidate: "partial_trace_table_candidate trace_table trace_openings"
    and nonlow: "\<not> trace_table_low_degree trace_table"
    and round_bound: "round_idx < length fri_query_idxs"
    and trace_bs_nonempty: "0 < length trace_bs"
    and openings_nonempty: "trace_openings ! round_idx \<noteq> []"
    and hd_idx:
      "opening_index (hd (trace_openings ! round_idx)) =
        fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0"
    and hd_neq: "opening_value (hd (trace_openings ! round_idx)) \<noteq> xp"
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
      "\<not> fri_opening_matches_table (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        trace_table xp xn"
    unfolding trace_fri_header_tied_base_head_value_neq_gap_def
    by metis
  have round_bound_rounds: "round_idx < rounds"
    using round_bound
      accepted_fri_opening_transcript_shapes(7)[OF fri_openings]
    by simp
  from accepted_fri_opening_transcript_trace_head_layer_value_aligned_at
      [OF fri_openings header out_eq round_bound trace_bs_nonempty]
  obtain openings yp yp_path yn yn_path where actual_idxs:
      "map opening_index openings = powers_scaled (fri_query_idxs ! round_idx)"
    and actual_auth:
      "partial_authenticated_table fr (scale * clength) openings final_state"
    and actual_nonempty: "openings \<noteq> []"
    and actual_value: "opening_value (hd openings) = yp"
    and actual_chunk:
      "fri_layer_opening_chunk (scale * clength) yp yp_path yn yn_path
        (trace_round_layers ! round_idx ! 0)"
    by blast
  have roots_nonempty: "0 < length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings]
      trace_bs_nonempty by simp
  have len_eq:
    "fri_evidence_layer_len trace_roots 0 = scale * clength"
    unfolding fri_evidence_layer_len_def
    using roots_nonempty
    by (cases trace_roots) (simp_all add: mult.commute)
  have step_chunk:
    "fri_layer_opening_chunk (scale * clength) xp xp_path xn xn_path
      (trace_round_layers ! round_idx ! 0)"
    using fri_layer_step_evidenceD(4)[OF step]
    unfolding len_eq .
  have yp_eq: "yp = xp"
    by (rule fri_layer_opening_chunk_values_unique(1)
        [OF actual_chunk step_chunk])
  have actual_head_idx:
    "opening_index (hd openings) =
      fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0"
  proof -
    have "opening_index (hd openings) = fri_query_idxs ! round_idx"
    proof -
      have "opening_index (hd openings) =
          hd (map opening_index openings)"
        using actual_nonempty by (cases openings) auto
      also have "... = hd (powers_scaled (fri_query_idxs ! round_idx))"
        using actual_idxs by simp
      also have "... = fri_query_idxs ! round_idx"
        by (rule powers_scaled_hd)
      finally show ?thesis .
    qed
    moreover have
      "fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0 =
        fri_query_idxs ! round_idx"
      using roots_nonempty
      unfolding fri_evidence_layer_idx_def
      by (cases trace_roots) simp_all
    ultimately show ?thesis by simp
  qed
  let ?opn = "hd (trace_openings ! round_idx)"
  let ?opn' = "hd openings"
  have trace_table:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! round_idx) final_state"
    using partial round_bound_rounds out_eq
    unfolding accepted_with_partial_trace_openings_def by blast
  have opn_auth: "authenticated_opening_in final_state ?opn"
    using trace_table openings_nonempty
    unfolding partial_authenticated_table_def by simp
  have opn'_auth: "authenticated_opening_in final_state ?opn'"
    using actual_auth actual_nonempty
    unfolding partial_authenticated_table_def by simp
  have same_root: "opening_root ?opn = opening_root ?opn'"
    using trace_table actual_auth openings_nonempty actual_nonempty
    unfolding partial_authenticated_table_def by auto
  have same_length: "opening_length ?opn = opening_length ?opn'"
    using trace_table actual_auth openings_nonempty actual_nonempty
    unfolding partial_authenticated_table_def by auto
  have same_index: "opening_index ?opn = opening_index ?opn'"
    using hd_idx actual_head_idx by simp
  have diff_value: "opening_value ?opn \<noteq> opening_value ?opn'"
    using hd_neq actual_value yp_eq by simp
  have acc: "accepted out"
    unfolding accepted_def out_eq by simp
  show ?thesis
    unfolding partial_merkle_inconsistency_bad_def
    by (intro conjI exI)
      (rule acc, rule out_eq, rule opn_auth, rule opn'_auth,
        rule same_root, rule same_length, rule same_index, rule diff_value)
qed

lemma wp_trace_fri_header_tied_base_head_value_neq_gap_bound_from_partial_merkle:
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap s) s \<le> M"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_base_head_value_neq_gap s) s \<le>
      wp_event verify_monad (partial_merkle_inconsistency_bad s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_base_head_value_neq_gap_imp_partial_merkle)
  then show ?thesis
    by (rule order_trans[OF _ merkle_bound])
qed

end

end
