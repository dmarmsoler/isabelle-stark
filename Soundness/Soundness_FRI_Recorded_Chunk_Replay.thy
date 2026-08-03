(*  Title:      Stark/Soundness_FRI_Recorded_Chunk_Replay.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Recorded_Chunk_Replay
  imports Soundness_FRI_Raw_Layer_Bounds
begin

text \<open>
  Selected recorded FRI layer replay.

  The authenticated-route layer already proves that the verifier authenticates
  some chunk at the replayed root/index of a selected FRI layer.  The residual
  proofs need the stronger fact that the specific chunk recorded in the
  extracted verifier transcript is authenticated.  This theory proves that
  narrow replay fact for one selected layer, avoiding the earlier broad
  all-layer replay induction.
\<close>

context soundness
begin

lemma fri_layer_lengths_nth_pos_imp_initial_pos:
  assumes j_bound: "j < n"
    and pos: "0 < fri_layer_lengths n len ! j"
  shows "0 < len"
  using assms
proof (induction j arbitrary: n len)
  case 0
  then show ?case
    by (cases n) simp_all
next
  case (Suc j)
  then obtain n' where n_eq: "n = Suc n'"
    by (cases n) auto
  have j_bound': "j < n'"
    using Suc.prems(1) unfolding n_eq by simp
  have pos': "0 < fri_layer_lengths n' (len div 2) ! j"
    using Suc.prems(2) unfolding n_eq by simp
  have "0 < len div 2"
    by (rule Suc.IH[OF j_bound' pos'])
  then show ?case
    by simp
qed

lemma mfold_fri_layer_opening_selected_recorded_chunk_authenticated_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw)
              (map fri_layer_opening_step bfs)) s)"
    and layers:
      "fri_layers_transcript (length bfs) len layer_chunks total_chunk"
    and transcript:
      "PTranscript s = total_chunk @ PTranscript t"
    and initial_idx_bound: "idx < len"
    and all_layer_bounds:
      "\<And>k. k < length bfs \<Longrightarrow>
        0 < fri_layer_lengths (length bfs) len ! k \<and>
        fri_layer_indices (length bfs) idx len ! k <
          fri_layer_lengths (length bfs) len ! k"
    and j_bound: "j < length bfs"
  shows
    "fri_layer_chunk_authenticated (snd (bfs ! j))
      (fri_layer_lengths (length bfs) len ! j)
      (fri_layer_indices (length bfs) idx len ! j)
      (layer_chunks ! j) t"
  using outcome layers transcript initial_idx_bound all_layer_bounds j_bound
proof (induction bfs arbitrary: idx x len pw s out t j layer_chunks total_chunk)
  case Nil
  then show ?case by simp
next
  case (Cons bf bfs)
  obtain b rt where bf_eq: "bf = (b, rt)"
    by (cases bf)
  from Cons.prems(1)[unfolded bf_eq]
  obtain out1 s1 where
    head:
      "Some (out1, s1) \<in>
        set_dist
          (execute (fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist
          (execute (mfold out1 (map fri_layer_opening_step bfs)) s1)"
    by (auto elim!: set_dist_bindE)
  obtain first rest where chunks_eq: "layer_chunks = first # rest"
    using Cons.prems(6) Cons.prems(2)
    unfolding fri_layers_transcript_def by (cases layer_chunks) auto
  have total_eq: "total_chunk = first @ List.concat rest"
    using Cons.prems(2) unfolding fri_layers_transcript_def chunks_eq
    by simp
  have first_open:
    "\<exists>xp xp_path xn xn_path.
      fri_layer_opening_chunk len xp xp_path xn xn_path first"
    using Cons.prems(2) unfolding fri_layers_transcript_def chunks_eq
    by auto
  have rest_layers:
    "fri_layers_transcript (length bfs) (len div 2) rest
      (List.concat rest)"
    using Cons.prems(2) unfolding fri_layers_transcript_def chunks_eq
    by auto
  obtain x' xp xp_path xn xn_path head_chunk where
    out1_eq:
      "out1 = (idx mod (len div 2), x', len div 2, pw + pw)"
    and head_chunk_def: "head_chunk = [xp] @ xp_path @ [xn] @ xn_path"
    and head_open:
      "fri_layer_opening_chunk len xp xp_path xn xn_path head_chunk"
    and tr_head: "PTranscript s = head_chunk @ PTranscript s1"
    and xp_auth:
      "authenticated_opening_in s1
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path\<rparr>"
    and xn_auth:
      "authenticated_opening_in s1
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = xn,
         opening_path = xn_path\<rparr>"
  proof -
    have len_pos: "0 < len"
      using Cons.prems(5)[of 0] by simp
    have idx_bound: "idx < len"
      by (rule Cons.prems(4))
    show ?thesis
    proof (rule fri_layer_opening_step_outcome_authenticated
        [OF len_pos idx_bound head])
      fix xp' xp_path' xn' xn_path' x'' chunk
      assume out_eq:
          "out1 = (idx mod (len div 2), x'', len div 2, pw + pw)"
        and chunk_eq: "chunk = [xp'] @ xp_path' @ [xn'] @ xn_path'"
        and chunk_open:
          "fri_layer_opening_chunk len xp' xp_path' xn' xn_path' chunk"
        and tr: "PTranscript s = chunk @ PTranscript s1"
        and ext: "s \<le> s1"
        and auth_xp:
          "authenticated_opening_in s1
            \<lparr>opening_root = rt, opening_length = len,
             opening_index = idx, opening_value = xp',
             opening_path = xp_path'\<rparr>"
        and auth_xn:
          "authenticated_opening_in s1
            \<lparr>opening_root = rt, opening_length = len,
             opening_index = fri_sibling_index len idx,
             opening_value = xn', opening_path = xn_path'\<rparr>"
      show ?thesis
        by (rule that[OF out_eq chunk_eq chunk_open tr auth_xp auth_xn])
    qed
  qed
  from mfold_fri_layer_openings_outcome[OF tail[unfolded out1_eq]]
  obtain tail_layers tail_chunk where
    tail_transcript:
      "PTranscript s1 = tail_chunk @ PTranscript t"
    and tail_ext: "s1 \<le> t"
    by blast
  have head_len: "length head_chunk = length first"
  proof -
    obtain yp yp_path yn yn_path where first_open':
      "fri_layer_opening_chunk len yp yp_path yn yn_path first"
      using first_open by blast
    show ?thesis
      using fri_layer_opening_chunk_length[OF head_open]
        fri_layer_opening_chunk_length[OF first_open']
      by simp
  qed
  have chunks_total_eq:
    "head_chunk @ tail_chunk = first @ List.concat rest"
    using tr_head tail_transcript Cons.prems(3) total_eq by simp
  have head_eq: "head_chunk = first"
    using arg_cong[OF chunks_total_eq, of "take (length head_chunk)"]
      head_len
    by simp
  have tail_transcript_rest:
    "PTranscript s1 = List.concat rest @ PTranscript t"
    using chunks_total_eq head_eq tail_transcript by simp
  show ?case
  proof (cases j)
    case 0
    have auth_s1:
      "fri_layer_chunk_authenticated rt len idx head_chunk s1"
      by (rule fri_layer_chunk_authenticatedI[OF head_open xp_auth xn_auth])
    have auth_t:
      "fri_layer_chunk_authenticated rt len idx head_chunk t"
      by (rule fri_layer_chunk_authenticated_mono[OF auth_s1 tail_ext])
    show ?thesis
      using auth_t head_eq 0 chunks_eq bf_eq by simp
  next
    case (Suc k)
    have k_bound: "k < length bfs"
      using Cons.prems(6) Suc by simp
    have tail_all_layer_bounds:
      "\<And>m. m < length bfs \<Longrightarrow>
        0 < fri_layer_lengths (length bfs) (len div 2) ! m \<and>
        fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! m <
        fri_layer_lengths (length bfs) (len div 2) ! m"
      using Cons.prems(5)[of "Suc m" for m] by simp
    have tail_initial_idx_bound: "idx mod (len div 2) < len div 2"
      using tail_all_layer_bounds[of 0] k_bound by (cases bfs) simp_all
    have tail_auth:
      "fri_layer_chunk_authenticated (snd (bfs ! k))
        (fri_layer_lengths (length bfs) (len div 2) ! k)
        (fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! k)
        (rest ! k) t"
      by (rule Cons.IH[OF tail[unfolded out1_eq] rest_layers
            tail_transcript_rest tail_initial_idx_bound tail_all_layer_bounds
            k_bound])
    show ?thesis
      using tail_auth Suc chunks_eq by simp
  qed
qed

lemma receive_query_commits_selected_recorded_chunk_authenticated_at:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw) (receive_query_commits bfs)) s)"
    and layers:
      "fri_layers_transcript (length bfs) len layer_chunks total_chunk"
    and transcript:
      "PTranscript s = total_chunk @ PTranscript t"
    and initial_idx_bound: "idx < len"
    and all_layer_bounds:
      "\<And>k. k < length bfs \<Longrightarrow>
        0 < fri_layer_lengths (length bfs) len ! k \<and>
        fri_layer_indices (length bfs) idx len ! k <
          fri_layer_lengths (length bfs) len ! k"
    and j_bound: "j < length bfs"
  shows
    "fri_layer_chunk_authenticated (snd (bfs ! j))
      (fri_layer_lengths (length bfs) len ! j)
      (fri_layer_indices (length bfs) idx len ! j)
      (layer_chunks ! j) t"
proof -
  have map_eq: "receive_query_commits bfs = map fri_layer_opening_step bfs"
    unfolding receive_query_commits_def fri_layer_opening_step_def
    by (simp add: fun_eq_iff split: prod.splits)
  show ?thesis
    by (rule mfold_fri_layer_opening_selected_recorded_chunk_authenticated_at
        [OF outcome[unfolded map_eq] layers transcript initial_idx_bound
          all_layer_bounds j_bound])
qed

lemma verifier_query_round_after_index_trace_recorded_layer_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
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
    and j_bound: "j < length f_fl"
    and all_layer_bounds:
      "\<And>k. k < length f_fl \<Longrightarrow>
        0 < fri_layer_lengths (length f_fl) (clength * scale) ! k \<and>
        fri_layer_indices (length f_fl) (index (to_nat raw))
          (clength * scale) ! k <
        fri_layer_lengths (length f_fl) (clength * scale) ! k"
  shows
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) (index (to_nat raw))
        (clength * scale) ! j)
      (trace_layers ! j) t"
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
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  have auth_s2:
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) ?idx (clength * scale) ! j)
      (trace_layer_chunks ! j) s2"
    by (rule receive_query_commits_selected_recorded_chunk_authenticated_at
        [OF trace_fri trace_layers_actual tr_s1 idx_bound
          all_layer_bounds j_bound])
  have s2_t: "s2 \<le> t"
    using ext_s3_s4 s3_eq t_eq by simp
  have auth_t:
    "fri_layer_chunk_authenticated (snd (f_fl ! j))
      (fri_layer_lengths (length f_fl) (clength * scale) ! j)
      (fri_layer_indices (length f_fl) ?idx (clength * scale) ! j)
      (trace_layer_chunks ! j) t"
    by (rule fri_layer_chunk_authenticated_mono[OF auth_s2 s2_t])
  show ?thesis
    using auth_t trace_layer_chunks_eq by simp
qed

lemma verifier_query_round_after_index_composition_recorded_layer_chunk_authenticated:
  fixes s t :: "('f, 'a) protocol_channel_scheme"
  assumes outcome:
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
    and j_bound: "j < length fl"
    and all_layer_bounds:
      "\<And>k. k < length fl \<Longrightarrow>
        0 < fri_layer_lengths (length fl) (clength * scale) ! k \<and>
        fri_layer_indices (length fl) (index (to_nat raw))
          (clength * scale) ! k <
        fri_layer_lengths (length fl) (clength * scale) ! k"
  shows
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) (index (to_nat raw))
        (clength * scale) ! j)
      (composition_layers ! j) t"
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
  have idx_bound: "?idx < clength * scale"
    by (rule index_less_domain)
  have auth_s4:
    "fri_layer_chunk_authenticated (snd (fl ! j))
      (fri_layer_lengths (length fl) (clength * scale) ! j)
      (fri_layer_indices (length fl) ?idx (clength * scale) ! j)
      (comp_layer_chunks ! j) s4"
    by (rule receive_query_commits_selected_recorded_chunk_authenticated_at
        [OF comp_fri comp_layers_actual tr_s3 idx_bound
          all_layer_bounds j_bound])
  show ?thesis
    using auth_s4 comp_layer_chunks_eq t_eq by simp
qed

lemma accepted_fri_opening_transcript_trace_recorded_layer_chunk_authenticated_at:
  assumes fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and round_bound: "i < rounds"
    and layer_bound: "j < length trace_roots"
    and all_layer_bounds:
      "\<And>raw k. k < length trace_roots \<Longrightarrow>
        0 < fri_layer_lengths (length trace_roots) (clength * scale) ! k \<and>
        fri_layer_indices (length trace_roots) (index (to_nat raw))
          (clength * scale) ! k <
        fri_layer_lengths (length trace_roots) (clength * scale) ! k"
  shows
    "generic_fri_recorded_layer_chunk_authenticated trace_roots query_idxs
      trace_round_layers final_state i j"
proof -
  from fri_openings obtain result' final_state' fr f_fl as fl query_state
      raw_idxs query_chunks where
    out_def: "out = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and trace_bs_eq: "trace_bs = map fst f_fl"
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
          trace_roots composition_roots (query_chunks ! i)"
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
        have query_chunk_f:
          "\<And>k. k < rounds \<Longrightarrow>
            verifier_query_round_chunk (query_idxs ! k)
              (map snd f_fl) (map snd fl) (query_chunks ! k)"
          using query_chunk trace_roots_eq composition_roots_eq by simp
        have query_chunk_lens:
          "\<And>k. k < rounds \<Longrightarrow>
            length (query_chunks ! k) =
              verifier_query_round_transcript_length (query_idxs ! k)
                (map snd f_fl) (map snd fl)"
          using query_chunk_f verifier_query_round_chunk_length by blast
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
        have j_bound_f: "j < length f_fl"
          using layer_bound trace_roots_eq by simp
        have all_layer_bounds_f:
          "\<And>k. k < length f_fl \<Longrightarrow>
            0 < fri_layer_lengths (length f_fl) (clength * scale) ! k \<and>
            fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) ! k <
            fri_layer_lengths (length f_fl) (clength * scale) ! k"
          using all_layer_bounds trace_roots_eq by simp
        have auth_suc:
          "fri_layer_chunk_authenticated (snd (f_fl ! j))
            (fri_layer_lengths (length f_fl) (clength * scale) ! j)
            (fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) ! j)
            (trace_round_layers ! i ! j) s_suc"
          by (rule
              verifier_query_round_after_index_trace_recorded_layer_chunk_authenticated
                [OF after recorded_i tr_s0_suc j_bound_f
                  all_layer_bounds_f])
        have auth_final:
          "fri_layer_chunk_authenticated (snd (f_fl ! j))
            (fri_layer_lengths (length f_fl) (clength * scale) ! j)
            (fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) ! j)
            (trace_round_layers ! i ! j) final_state"
          by (rule fri_layer_chunk_authenticated_mono[OF auth_suc suffix_ext])
        have raw_idx_query: "index (to_nat raw) = query_idxs ! i"
          using idx_eq idx_eq_query raw_eq' by simp
        have auth:
          "fri_layer_chunk_authenticated (trace_roots ! j)
            (fri_evidence_layer_len trace_roots j)
            (fri_evidence_layer_idx trace_roots query_idxs i j)
            (trace_round_layers ! i ! j) final_state"
          using auth_final trace_roots_eq raw_idx_query layer_bound
          unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
          by simp
        show ?thesis
          unfolding generic_fri_recorded_layer_chunk_authenticated_def
          by (rule auth)
      qed
    qed
  qed
qed

lemma accepted_fri_opening_transcript_composition_recorded_layer_chunk_authenticated_at:
  assumes fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final query_idxs
        trace_round_layers composition_round_layers"
    and out_eq: "out = Some (result, final_state)"
    and round_bound: "i < rounds"
    and layer_bound: "j < length composition_roots"
    and all_layer_bounds:
      "\<And>raw k. k < length composition_roots \<Longrightarrow>
        0 < fri_layer_lengths (length composition_roots) (clength * scale) ! k \<and>
        fri_layer_indices (length composition_roots) (index (to_nat raw))
          (clength * scale) ! k <
        fri_layer_lengths (length composition_roots) (clength * scale) ! k"
  shows
    "generic_fri_recorded_layer_chunk_authenticated composition_roots
      query_idxs composition_round_layers final_state i j"
proof -
  from fri_openings obtain result' final_state' fr f_fl as fl query_state
      raw_idxs query_chunks where
    out_def: "out = Some (result', final_state')"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and composition_bs_eq: "composition_bs = map fst fl"
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
          trace_roots composition_roots (query_chunks ! i)"
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
        have query_chunk_f:
          "\<And>k. k < rounds \<Longrightarrow>
            verifier_query_round_chunk (query_idxs ! k)
              (map snd f_fl) (map snd fl) (query_chunks ! k)"
          using query_chunk trace_roots_eq composition_roots_eq by simp
        have query_chunk_lens:
          "\<And>k. k < rounds \<Longrightarrow>
            length (query_chunks ! k) =
              verifier_query_round_transcript_length (query_idxs ! k)
                (map snd f_fl) (map snd fl)"
          using query_chunk_f verifier_query_round_chunk_length by blast
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
        have j_bound_fl: "j < length fl"
          using layer_bound composition_roots_eq by simp
        have all_layer_bounds_fl:
          "\<And>k. k < length fl \<Longrightarrow>
            0 < fri_layer_lengths (length fl) (clength * scale) ! k \<and>
            fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) ! k <
            fri_layer_lengths (length fl) (clength * scale) ! k"
          using all_layer_bounds composition_roots_eq by simp
        have auth_suc:
          "fri_layer_chunk_authenticated (snd (fl ! j))
            (fri_layer_lengths (length fl) (clength * scale) ! j)
            (fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) ! j)
            (composition_round_layers ! i ! j) s_suc"
          by (rule
              verifier_query_round_after_index_composition_recorded_layer_chunk_authenticated
                [OF after recorded_i tr_s0_suc j_bound_fl
                  all_layer_bounds_fl])
        have auth_final:
          "fri_layer_chunk_authenticated (snd (fl ! j))
            (fri_layer_lengths (length fl) (clength * scale) ! j)
            (fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) ! j)
            (composition_round_layers ! i ! j) final_state"
          by (rule fri_layer_chunk_authenticated_mono[OF auth_suc suffix_ext])
        have raw_idx_query: "index (to_nat raw) = query_idxs ! i"
          using idx_eq idx_eq_query raw_eq' by simp
        have auth:
          "fri_layer_chunk_authenticated (composition_roots ! j)
            (fri_evidence_layer_len composition_roots j)
            (fri_evidence_layer_idx composition_roots query_idxs i j)
            (composition_round_layers ! i ! j) final_state"
          using auth_final composition_roots_eq raw_idx_query layer_bound
          unfolding fri_evidence_layer_len_def fri_evidence_layer_idx_def
          by simp
        show ?thesis
          unfolding generic_fri_recorded_layer_chunk_authenticated_def
          by (rule auth)
      qed
    qed
  qed
qed

end

end
