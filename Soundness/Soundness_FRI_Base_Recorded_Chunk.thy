(*  Title:      Stark/Soundness_FRI_Base_Recorded_Chunk.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Base_Recorded_Chunk
  imports Soundness_FRI_Layer_Merkle
begin

section \<open>FRI Replay and Active Bounds\<close>

text \<open>
  Base-layer recorded chunk replay.  This is the small case needed for the
  existing first-layer composition residual: the head chunk read by
  @{term receive_query_commits} is the first chunk in the extracted layer
  transcript, hence the recorded first layer is authenticated.
\<close>

context soundness
begin

lemma mfold_fri_layer_opening_head_recorded_chunk_authenticated:
  assumes outcome:
    "Some (out, t) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (map fri_layer_opening_step ((b, rt) # bfs))) s)"
    and layers:
      "fri_layers_transcript (length ((b, rt) # bfs)) len layer_chunks
        total_chunk"
    and transcript: "PTranscript s = total_chunk @ PTranscript t"
    and len_pos: "0 < len"
    and idx_bound: "idx < len"
  shows
    "fri_layer_chunk_authenticated rt len idx (layer_chunks ! 0) t"
proof -
  from outcome obtain out1 s1 where
    head:
      "Some (out1, s1) \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist (execute (mfold out1 (map fri_layer_opening_step bfs)) s1)"
    by (auto elim!: set_dist_bindE)
  obtain xp xp_path xn xn_path x' head_chunk where
    out1_eq:
      "out1 = (idx mod (len div 2), x', len div 2, pw + pw)"
    and head_open:
      "fri_layer_opening_chunk len xp xp_path xn xn_path head_chunk"
    and tr_head: "PTranscript s = head_chunk @ PTranscript s1"
    and auth_xp:
      "authenticated_opening_in s1
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path\<rparr>"
    and auth_xn:
      "authenticated_opening_in s1
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = xn,
         opening_path = xn_path\<rparr>"
    by (rule fri_layer_opening_step_outcome_authenticated
        [OF len_pos idx_bound head])
  from mfold_fri_layer_openings_outcome[OF tail[unfolded out1_eq]]
  obtain tail_layers tail_chunk where
    tail_layers:
      "fri_layers_transcript (length bfs) (len div 2) tail_layers
        tail_chunk"
    and tr_tail: "PTranscript s1 = tail_chunk @ PTranscript t"
    and ext_tail: "s1 \<le> t"
    by auto
  let ?layers = "head_chunk # tail_layers"
  let ?chunk = "head_chunk @ tail_chunk"
  have exec_layers:
    "fri_layers_transcript (length ((b, rt) # bfs)) len ?layers ?chunk"
    using head_open tail_layers
    unfolding fri_layers_transcript_def by auto
  have exec_transcript: "PTranscript s = ?chunk @ PTranscript t"
    using tr_head tr_tail by simp
  have chunk_eq: "?chunk = total_chunk"
    using exec_transcript transcript by simp
  have layers_eq: "?layers = layer_chunks"
    by (rule fri_layers_transcript_unique[OF exec_layers])
      (use layers chunk_eq in simp)
  have head_auth_s1:
    "fri_layer_chunk_authenticated rt len idx head_chunk s1"
    by (rule fri_layer_chunk_authenticatedI[OF head_open auth_xp auth_xn])
  have head_auth_t:
    "fri_layer_chunk_authenticated rt len idx head_chunk t"
    by (rule fri_layer_chunk_authenticated_mono[OF head_auth_s1 ext_tail])
  show ?thesis
    using head_auth_t layers_eq[symmetric] by simp
qed

lemma receive_query_commits_head_recorded_chunk_authenticated:
  assumes outcome:
    "Some (out, t) \<in>
      set_dist
        (execute
          (mfold (idx, x, len, pw)
            (receive_query_commits ((b, rt) # bfs))) s)"
    and layers:
      "fri_layers_transcript (length ((b, rt) # bfs)) len layer_chunks
        total_chunk"
    and transcript: "PTranscript s = total_chunk @ PTranscript t"
    and len_pos: "0 < len"
    and idx_bound: "idx < len"
  shows
    "fri_layer_chunk_authenticated rt len idx (layer_chunks ! 0) t"
proof -
  have map_eq:
    "receive_query_commits ((b, rt) # bfs) =
      map fri_layer_opening_step ((b, rt) # bfs)"
    unfolding receive_query_commits_def fri_layer_opening_step_def
    by (simp add: fun_eq_iff split: prod.splits)
  show ?thesis
    by (rule mfold_fri_layer_opening_head_recorded_chunk_authenticated
        [OF outcome[unfolded map_eq] layers transcript len_pos idx_bound])
qed

lemma verifier_query_round_after_index_trace_base_recorded_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
    and recorded:
      "query_round_fri_layer_transcripts (index (to_nat raw))
        (map snd f_fl) (map snd fl) round_chunk trace_layers
        composition_layers"
    and transcript: "PTranscript s = round_chunk @ PTranscript t"
  shows
    "fri_layer_chunk_authenticated rt (clength * scale)
      (index (to_nat raw)) (trace_layers ! 0) t"
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
          (mfold
            (?idx, cp_eval as fv (h ^ ?idx * shift), clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  from check_decommit_on_query_outcome[OF query_decommit]
  obtain query_paths query_chunk where
    query_chunk_shape:
      "query_decommitment_transcript ?idx fv query_paths query_chunk"
    and tr_s: "PTranscript s = query_chunk @ PTranscript s1"
    by blast
  from receive_query_commits_layers_outcome[OF trace_fri]
  obtain trace_layer_chunks trace_fri_chunk where
    trace_layers_actual:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layer_chunks trace_fri_chunk"
    and tr_s1: "PTranscript s1 = trace_fri_chunk @ PTranscript s2"
    and ext_s1_s2: "s1 \<le> s2"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  from receive_query_commits_layers_outcome[OF comp_fri]
  obtain comp_layer_chunks comp_fri_chunk where
    comp_layers_actual:
      "fri_layers_transcript (length fl) (clength * scale)
        comp_layer_chunks comp_fri_chunk"
    and tr_s3: "PTranscript s3 = comp_fri_chunk @ PTranscript s4"
    and ext_s3_s4: "s3 \<le> s4"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  let ?actual_chunk = "query_chunk @ trace_fri_chunk @ comp_fri_chunk"
  have actual_recorded:
    "query_round_fri_layer_transcripts ?idx (map snd f_fl) (map snd fl)
      ?actual_chunk trace_layer_chunks comp_layer_chunks"
    unfolding query_round_fri_layer_transcripts_def
    by (intro exI[of _ query_chunk] exI[of _ trace_fri_chunk]
        exI[of _ comp_fri_chunk] exI[of _ fv] exI[of _ query_paths] conjI)
      (use query_chunk_shape trace_layers_actual comp_layers_actual in
        \<open>simp_all add: mult.commute\<close>)
  have actual_transcript:
    "PTranscript s = ?actual_chunk @ PTranscript t"
    using tr_s tr_s1 tr_s3 s3_eq t_eq by simp
  have actual_chunk_eq: "?actual_chunk = round_chunk"
    using actual_transcript transcript by simp
  have trace_layer_chunks_eq:
    "trace_layer_chunks = trace_layers"
    by (rule query_round_fri_layer_transcripts_unique(1)
        [OF actual_recorded[unfolded actual_chunk_eq] recorded])
  have len_pos: "0 < clength * scale"
    by (rule eval_domain_size_pos)
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  have auth_s2:
    "fri_layer_chunk_authenticated rt (clength * scale) ?idx
      (trace_layer_chunks ! 0) s2"
    by (rule receive_query_commits_head_recorded_chunk_authenticated
        [OF trace_fri[unfolded f_fl_eq]
          trace_layers_actual[unfolded f_fl_eq] tr_s1 len_pos idx_bound])
  have s2_t: "s2 \<le> t"
    using ext_s3_s4 s3_eq t_eq by simp
  have auth_t:
    "fri_layer_chunk_authenticated rt (clength * scale) ?idx
      (trace_layer_chunks ! 0) t"
    by (rule fri_layer_chunk_authenticated_mono[OF auth_s2 s2_t])
  show ?thesis
    using auth_t trace_layer_chunks_eq by simp
qed

lemma verifier_query_round_after_index_composition_base_recorded_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes fl_eq: "fl = (b, rt) # fl_tail"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_after_index_program
              fr f_fl f_final as fl final raw) s)"
    and recorded:
      "query_round_fri_layer_transcripts (index (to_nat raw))
        (map snd f_fl) (map snd fl) round_chunk trace_layers
        composition_layers"
    and transcript: "PTranscript s = round_chunk @ PTranscript t"
  shows
    "fri_layer_chunk_authenticated rt (clength * scale)
      (index (to_nat raw)) (composition_layers ! 0) t"
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
          (mfold
            (?idx, cp_eval as fv (h ^ ?idx * shift), clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_after_index_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  from check_decommit_on_query_outcome[OF query_decommit]
  obtain query_paths query_chunk where
    query_chunk_shape:
      "query_decommitment_transcript ?idx fv query_paths query_chunk"
    and tr_s: "PTranscript s = query_chunk @ PTranscript s1"
    by blast
  from receive_query_commits_layers_outcome[OF trace_fri]
  obtain trace_layer_chunks trace_fri_chunk where
    trace_layers_actual:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layer_chunks trace_fri_chunk"
    and tr_s1: "PTranscript s1 = trace_fri_chunk @ PTranscript s2"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  from receive_query_commits_layers_outcome[OF comp_fri]
  obtain comp_layer_chunks comp_fri_chunk where
    comp_layers_actual:
      "fri_layers_transcript (length fl) (clength * scale)
        comp_layer_chunks comp_fri_chunk"
    and tr_s3: "PTranscript s3 = comp_fri_chunk @ PTranscript s4"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  let ?actual_chunk = "query_chunk @ trace_fri_chunk @ comp_fri_chunk"
  have actual_recorded:
    "query_round_fri_layer_transcripts ?idx (map snd f_fl) (map snd fl)
      ?actual_chunk trace_layer_chunks comp_layer_chunks"
    unfolding query_round_fri_layer_transcripts_def
    by (intro exI[of _ query_chunk] exI[of _ trace_fri_chunk]
        exI[of _ comp_fri_chunk] exI[of _ fv] exI[of _ query_paths] conjI)
      (use query_chunk_shape trace_layers_actual comp_layers_actual in
        \<open>simp_all add: mult.commute\<close>)
  have actual_transcript:
    "PTranscript s = ?actual_chunk @ PTranscript t"
    using tr_s tr_s1 tr_s3 s3_eq t_eq by simp
  have actual_chunk_eq: "?actual_chunk = round_chunk"
    using actual_transcript transcript by simp
  have comp_layer_chunks_eq:
    "comp_layer_chunks = composition_layers"
    by (rule query_round_fri_layer_transcripts_unique(2)
        [OF actual_recorded[unfolded actual_chunk_eq] recorded])
  have len_pos: "0 < clength * scale"
    by (rule eval_domain_size_pos)
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  have auth_s4:
    "fri_layer_chunk_authenticated rt (clength * scale) ?idx
      (comp_layer_chunks ! 0) s4"
    by (rule receive_query_commits_head_recorded_chunk_authenticated
        [OF comp_fri[unfolded fl_eq] comp_layers_actual[unfolded fl_eq]
          tr_s3 len_pos idx_bound])
  show ?thesis
    using auth_s4 comp_layer_chunks_eq t_eq by simp
qed

lemma accepted_fri_opening_transcript_trace_base_recorded_chunk_authenticated_at:
  assumes fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and round_bound: "i < rounds"
    and trace_nonempty: "0 < length trace_roots"
  shows
    "fri_layer_chunk_authenticated (trace_roots ! 0) (clength * scale)
      (query_idxs ! i) (trace_round_layers ! i ! 0) final_state"
proof -
  from fri_openings obtain result' final_state' fr f_fl as fl query_state
      raw_idxs query_chunks where
    out_def: "out = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and outcome:
      "Some (result', final_state') \<in>
        set_dist (execute
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
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    and recorded:
      "\<And>i. i < rounds \<Longrightarrow>
        query_round_fri_layer_transcripts (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)
          (trace_round_layers ! i) (composition_round_layers ! i)"
    unfolding accepted_fri_opening_transcript_def by blast
  have result_eq: "result' = result"
    using out_def out_eq by simp
  have final_state_eq: "final_state' = final_state"
    using out_def out_eq by simp
  have outcome':
    "Some (result, final_state) \<in>
      set_dist (execute
        (ntimes
          (verifier_query_round_program fr f_fl trace_final as fl
            composition_final)
          rounds)
        query_state)"
    using outcome result_eq final_state_eq by simp
  have f_fl_nonempty: "f_fl \<noteq> []"
    using trace_nonempty trace_roots_eq by auto
  then obtain bf f_fl_tail where f_fl_cons: "f_fl = bf # f_fl_tail"
    by (cases f_fl) auto
  obtain b rt where bf_eq: "bf = (b, rt)"
    by (cases bf)
  have f_fl_eq: "f_fl = (b, rt) # f_fl_tail"
    using f_fl_cons bf_eq by simp
  have rt_eq: "rt = trace_roots ! 0"
    using f_fl_cons bf_eq trace_roots_eq by simp
  let ?round =
    "verifier_query_round_program fr f_fl trace_final as fl composition_final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome' round_bound]
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
      and counter_i: "PQueryCounter s_i = PQueryCounter query_state + i"
      and prefix_ext: "query_state \<le> s_i"
      and prefix_rounds:
        "\<And>k. k < i \<Longrightarrow>
          verifier_query_round_chunk (prefix_query_idxs ! k)
            (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    from round[unfolded x_eq verifier_query_round_program_alt_def]
    obtain raw s0 where
      raw_out:
        "Some (raw, s0) \<in>
          set_dist (execute receive_query_index_challenge s_i)"
      and after:
        "Some ((), s_suc) \<in>
          set_dist (execute
            (verifier_query_round_after_index_program fr f_fl trace_final as
              fl composition_final raw) s0)"
      by (auto elim!: set_dist_bindE)
    have tr_s0: "PTranscript s0 = PTranscript s_i"
      using receive_query_index_challenge_outcome[OF raw_out] by simp
    show ?thesis
    proof (rule verifier_query_round_program_outcome[OF round[unfolded x_eq]])
      fix raw' idx chunk
      assume idx_eq: "idx = index (to_nat raw')"
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
          Some raw'"
      have raw_eq': "raw = raw'"
      proof -
        have lookup_s0:
          "fmlookup (HashMap s0)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw"
          using receive_query_index_challenge_outcome[OF raw_out] by simp
        have s0_suc: "s0 \<le> s_suc"
          using verifier_query_round_after_index_program_outcome[OF after]
          by simp
        have lookup_suc_raw:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw"
          using hash_extension_lookup[OF lookup_s0 s0_suc] .
        show ?thesis
          using lookup_suc lookup_suc_raw by simp
      qed
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
        have selected_transcript:
          "PTranscript query_state =
            List.concat ?selected_chunks @ PTranscript final_state"
          using transcript_prefix transcript_round transcript_suffix by simp
        have concat_eq: "List.concat ?selected_chunks = List.concat query_chunks"
          using selected_transcript transcript_query final_state_eq by simp
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
            "state_after_query_chunks (PState query_state) ?selected_chunks i =
              state_after_query_chunks (PState query_state) prefix_chunks i"
            by (rule state_after_query_chunks_append_prefix
                [OF len_prefix_chunks])
          then show ?thesis
            using chunks_eq by simp
        qed
        have lookup_final:
          "fmlookup (HashMap final_state)
            (QueryIndexChallenge (PQueryCounter query_state + i)
              (state_after_query_chunks (PState query_state) query_chunks i)) =
          Some raw'"
        proof -
          have lookup_suc':
            "fmlookup (HashMap s_suc)
              (QueryIndexChallenge (PQueryCounter query_state + i)
                (state_after_query_chunks (PState query_state)
                  prefix_chunks i)) =
            Some raw'"
            using lookup_suc state_i counter_i by simp
          have lookup_final_prefix:
            "fmlookup (HashMap final_state)
              (QueryIndexChallenge (PQueryCounter query_state + i)
                (state_after_query_chunks (PState query_state)
                  prefix_chunks i)) =
            Some raw'"
            using hash_extension_lookup[OF lookup_suc' suffix_ext] .
          show ?thesis
            using lookup_final_prefix prefix_state_eq by simp
        qed
        have raw_idx_eq: "raw' = raw_idxs ! i"
          using lookup_final replay_lookup[OF round_bound] final_state_eq
          by simp
        have idx_eq_query: "idx = query_idxs ! i"
          using idx_eq raw_idx_eq query_idxs_eq len_raw round_bound by simp
        have selected_i: "?selected_chunks ! i = chunk"
          using len_prefix_chunks by (simp add: nth_append)
        have chunk_i_eq: "chunk = query_chunks ! i"
          using chunks_eq selected_i by simp
        have recorded_i:
          "query_round_fri_layer_transcripts (index (to_nat raw))
            (map snd f_fl) (map snd fl) chunk (trace_round_layers ! i)
            (composition_round_layers ! i)"
          using recorded[OF round_bound] idx_eq idx_eq_query raw_eq'
            chunk_i_eq trace_roots_eq composition_roots_eq
          by simp
        have tr_s0_suc:
          "PTranscript s0 = chunk @ PTranscript s_suc"
          using tr_s0 transcript_round by simp
        have auth_suc:
          "fri_layer_chunk_authenticated rt (clength * scale)
            (index (to_nat raw)) (trace_round_layers ! i ! 0) s_suc"
          by (rule
              verifier_query_round_after_index_trace_base_recorded_chunk_authenticated
                [OF f_fl_eq after recorded_i tr_s0_suc])
        have auth_final:
          "fri_layer_chunk_authenticated rt (clength * scale)
            (index (to_nat raw)) (trace_round_layers ! i ! 0)
            final_state"
          by (rule fri_layer_chunk_authenticated_mono[OF auth_suc suffix_ext])
        have raw_idx_query: "index (to_nat raw) = query_idxs ! i"
          using idx_eq idx_eq_query raw_eq' by simp
        show ?thesis
          using auth_final rt_eq raw_idx_query by simp
      qed
    qed
  qed
qed

lemma accepted_fri_opening_transcript_composition_base_recorded_chunk_authenticated_at:
  assumes fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and round_bound: "i < rounds"
    and composition_nonempty: "0 < length composition_roots"
  shows
    "fri_layer_chunk_authenticated (composition_roots ! 0) (clength * scale)
      (query_idxs ! i) (composition_round_layers ! i ! 0) final_state"
proof -
  from fri_openings obtain result' final_state' fr f_fl as fl query_state
      raw_idxs query_chunks where
    out_def: "out = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and outcome:
      "Some (result', final_state') \<in>
        set_dist (execute
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
          (map snd f_fl) (map snd fl) (query_chunks ! i)"
    and replay_lookup:
      "\<And>i. i < rounds \<Longrightarrow>
        fmlookup (HashMap final_state')
          (QueryIndexChallenge (PQueryCounter query_state + i)
            (state_after_query_chunks (PState query_state) query_chunks i)) =
        Some (raw_idxs ! i)"
    and recorded:
      "\<And>i. i < rounds \<Longrightarrow>
        query_round_fri_layer_transcripts (query_idxs ! i)
          trace_roots composition_roots (query_chunks ! i)
          (trace_round_layers ! i) (composition_round_layers ! i)"
    unfolding accepted_fri_opening_transcript_def by blast
  have result_eq: "result' = result"
    using out_def out_eq by simp
  have final_state_eq: "final_state' = final_state"
    using out_def out_eq by simp
  have outcome':
    "Some (result, final_state) \<in>
      set_dist (execute
        (ntimes
          (verifier_query_round_program fr f_fl trace_final as fl
            composition_final)
          rounds)
        query_state)"
    using outcome result_eq final_state_eq by simp
  have fl_nonempty: "fl \<noteq> []"
    using composition_nonempty composition_roots_eq by auto
  then obtain bf fl_tail where fl_cons: "fl = bf # fl_tail"
    by (cases fl) auto
  obtain b rt where bf_eq: "bf = (b, rt)"
    by (cases bf)
  have fl_eq: "fl = (b, rt) # fl_tail"
    using fl_cons bf_eq by simp
  have rt_eq: "rt = composition_roots ! 0"
    using fl_cons bf_eq composition_roots_eq by simp
  let ?round =
    "verifier_query_round_program fr f_fl trace_final as fl composition_final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome' round_bound]
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
      and counter_i: "PQueryCounter s_i = PQueryCounter query_state + i"
      and prefix_ext: "query_state \<le> s_i"
      and prefix_rounds:
        "\<And>k. k < i \<Longrightarrow>
          verifier_query_round_chunk (prefix_query_idxs ! k)
            (map snd f_fl) (map snd fl) (prefix_chunks ! k)"
    from round[unfolded x_eq verifier_query_round_program_alt_def]
    obtain raw s0 where
      raw_out:
        "Some (raw, s0) \<in>
          set_dist (execute receive_query_index_challenge s_i)"
      and after:
        "Some ((), s_suc) \<in>
          set_dist (execute
            (verifier_query_round_after_index_program fr f_fl trace_final as
              fl composition_final raw) s0)"
      by (auto elim!: set_dist_bindE)
    have tr_s0: "PTranscript s0 = PTranscript s_i"
      using receive_query_index_challenge_outcome[OF raw_out] by simp
    show ?thesis
    proof (rule verifier_query_round_program_outcome[OF round[unfolded x_eq]])
      fix raw' idx chunk
      assume idx_eq: "idx = index (to_nat raw')"
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
          Some raw'"
      have raw_eq': "raw = raw'"
      proof -
        have lookup_s0:
          "fmlookup (HashMap s0)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw"
          using receive_query_index_challenge_outcome[OF raw_out] by simp
        have s0_suc: "s0 \<le> s_suc"
          using verifier_query_round_after_index_program_outcome[OF after]
          by simp
        have lookup_suc_raw:
          "fmlookup (HashMap s_suc)
            (QueryIndexChallenge (PQueryCounter s_i) (PState s_i)) =
          Some raw"
          using hash_extension_lookup[OF lookup_s0 s0_suc] .
        show ?thesis
          using lookup_suc lookup_suc_raw by simp
      qed
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
        have selected_transcript:
          "PTranscript query_state =
            List.concat ?selected_chunks @ PTranscript final_state"
          using transcript_prefix transcript_round transcript_suffix by simp
        have concat_eq: "List.concat ?selected_chunks = List.concat query_chunks"
          using selected_transcript transcript_query final_state_eq by simp
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
            "state_after_query_chunks (PState query_state) ?selected_chunks i =
              state_after_query_chunks (PState query_state) prefix_chunks i"
            by (rule state_after_query_chunks_append_prefix
                [OF len_prefix_chunks])
          then show ?thesis
            using chunks_eq by simp
        qed
        have lookup_final:
          "fmlookup (HashMap final_state)
            (QueryIndexChallenge (PQueryCounter query_state + i)
              (state_after_query_chunks (PState query_state) query_chunks i)) =
          Some raw'"
        proof -
          have lookup_suc':
            "fmlookup (HashMap s_suc)
              (QueryIndexChallenge (PQueryCounter query_state + i)
                (state_after_query_chunks (PState query_state)
                  prefix_chunks i)) =
            Some raw'"
            using lookup_suc state_i counter_i by simp
          have lookup_final_prefix:
            "fmlookup (HashMap final_state)
              (QueryIndexChallenge (PQueryCounter query_state + i)
                (state_after_query_chunks (PState query_state)
                  prefix_chunks i)) =
            Some raw'"
            using hash_extension_lookup[OF lookup_suc' suffix_ext] .
          show ?thesis
            using lookup_final_prefix prefix_state_eq by simp
        qed
        have raw_idx_eq: "raw' = raw_idxs ! i"
          using lookup_final replay_lookup[OF round_bound] final_state_eq
          by simp
        have idx_eq_query: "idx = query_idxs ! i"
          using idx_eq raw_idx_eq query_idxs_eq len_raw round_bound by simp
        have selected_i: "?selected_chunks ! i = chunk"
          using len_prefix_chunks by (simp add: nth_append)
        have chunk_i_eq: "chunk = query_chunks ! i"
          using chunks_eq selected_i by simp
        have recorded_i:
          "query_round_fri_layer_transcripts (index (to_nat raw))
            (map snd f_fl) (map snd fl) chunk (trace_round_layers ! i)
            (composition_round_layers ! i)"
          using recorded[OF round_bound] idx_eq idx_eq_query raw_eq'
            chunk_i_eq trace_roots_eq composition_roots_eq
          by simp
        have tr_s0_suc:
          "PTranscript s0 = chunk @ PTranscript s_suc"
          using tr_s0 transcript_round by simp
        have auth_suc:
          "fri_layer_chunk_authenticated rt (clength * scale)
            (index (to_nat raw)) (composition_round_layers ! i ! 0) s_suc"
          by (rule
              verifier_query_round_after_index_composition_base_recorded_chunk_authenticated
                [OF fl_eq after recorded_i tr_s0_suc])
        have auth_final:
          "fri_layer_chunk_authenticated rt (clength * scale)
            (index (to_nat raw)) (composition_round_layers ! i ! 0)
            final_state"
          by (rule fri_layer_chunk_authenticated_mono[OF auth_suc suffix_ext])
        have raw_idx_query: "index (to_nat raw) = query_idxs ! i"
          using idx_eq idx_eq_query raw_eq' by simp
        show ?thesis
          using auth_final rt_eq raw_idx_query by simp
      qed
    qed
  qed
qed

end

end
