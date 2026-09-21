theory Soundness_FRI_RO_Actual_Query_Accepted_Evidence
  imports Soundness_FRI_RO_Actual_Query_Partial_Evidence
begin


context soundness
begin

lemma ro_verifier_query_round_program_final_checks:
  assumes outcome:
    "Some ((), t) \<in>
      set_dist
        (execute
          (ro_verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx fv s0 s1 f_i f_len f_pow s2 c_i c_len c_pow s4
  where
    "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    "idx = index (to_nat raw)"
    "Some (fv, s1) \<in>
      set_dist (execute (mmap (ro_check_decommit_on_query fr idx)) s0)"
    "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
      set_dist
        (execute
          (mfold (idx, hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl)) s1)"
    "Some ((c_i, final, c_len, c_pow), s4) \<in>
      set_dist
        (execute
          (mfold (idx, cp_eval as fv (h ^ idx * shift),
              clength * scale, 1)
            (ro_receive_query_commits fl)) s2)"
    "t = s4"
proof -
  from outcome obtain raw s0 fv s1 f_out s2 s3 c_out s4 where
    raw:
      "Some (raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and query_decommit:
      "Some (fv, s1) \<in>
        set_dist
          (execute
            (mmap
              (ro_check_decommit_on_query fr (index (to_nat raw)))) s0)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat raw), hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in>
        set_dist
          (execute
            (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat raw),
                cp_eval as fv (h ^ index (to_nat raw) * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in>
        set_dist
          (execute
            (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding ro_verifier_query_round_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  obtain f_i f_x f_len f_pow where f_out_eq:
    "f_out = (f_i, f_x, f_len, f_pow)"
    by (cases f_out) auto
  have f_x_eq: "f_x = f_final"
    using assert_trace unfolding assert_def f_out_eq
    by (cases "f_x = f_final") (auto simp: throw_no_outcome)
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def f_out_eq f_x_eq by simp
  obtain c_i c_x c_len c_pow where c_out_eq:
    "c_out = (c_i, c_x, c_len, c_pow)"
    by (cases c_out) auto
  have c_x_eq: "c_x = final"
    using assert_comp unfolding assert_def c_out_eq
    by (cases "c_x = final") (auto simp: throw_no_outcome)
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def c_out_eq c_x_eq by simp
  have trace_fri':
    "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
      set_dist
        (execute
          (mfold
            (index (to_nat raw), hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl)) s1)"
    using trace_fri f_out_eq f_x_eq by simp
  have comp_fri':
    "Some ((c_i, final, c_len, c_pow), s4) \<in>
      set_dist
        (execute
          (mfold
            (index (to_nat raw),
              cp_eval as fv (h ^ index (to_nat raw) * shift),
              clength * scale, 1)
            (ro_receive_query_commits fl)) s2)"
    using comp_fri c_out_eq c_x_eq s3_eq by simp
  show ?thesis
    by (rule that[OF raw refl query_decommit trace_fri' comp_fri' t_eq])
qed

lemma ntimes_ro_verifier_query_round_program_final_checks_at:
  assumes outcome:
    "Some (results, t) \<in>
      set_dist
        (execute
          (ntimes
            (ro_verifier_query_round_program fr f_fl f_final as fl final) n)
          s)"
    and i_bound: "i < n"
  obtains prefix suffix s_i s_suc raw idx fv s0 s1
      f_i f_len f_pow s2 c_i c_len c_pow s4
  where
    "Some (prefix, s_i) \<in>
      set_dist
        (execute
          (ntimes
            (ro_verifier_query_round_program fr f_fl f_final as fl final) i)
          s)"
    "Some ((), s_suc) \<in>
      set_dist
        (execute
          (ro_verifier_query_round_program fr f_fl f_final as fl final) s_i)"
    "Some (suffix, t) \<in>
      set_dist
        (execute
          (ntimes
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            (n - Suc i))
          s_suc)"
    "results = prefix @ () # suffix"
    "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s_i)"
    "idx = index (to_nat raw)"
    "Some (fv, s1) \<in>
      set_dist (execute (mmap (ro_check_decommit_on_query fr idx)) s0)"
    "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
      set_dist
        (execute
          (mfold (idx, hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl)) s1)"
    "Some ((c_i, final, c_len, c_pow), s4) \<in>
      set_dist
        (execute
          (mfold (idx, cp_eval as fv (h ^ idx * shift),
              clength * scale, 1)
            (ro_receive_query_commits fl)) s2)"
    "s_suc = s4"
proof -
  let ?round =
    "ro_verifier_query_round_program fr f_fl f_final as fl final"
  from query_opening_ntimes_outcome_decomp_at[OF outcome i_bound]
  obtain prefix x suffix s_i s_suc where
    prefix:
      "Some (prefix, s_i) \<in> set_dist (execute (ntimes ?round i) s)"
    and round:
      "Some (x, s_suc) \<in> set_dist (execute ?round s_i)"
    and suffix:
      "Some (suffix, t) \<in>
        set_dist (execute (ntimes ?round (n - Suc i)) s_suc)"
    and results_eq: "results = prefix @ x # suffix"
    by blast
  have x_eq: "x = ()"
    by (cases x) simp
  have round_unit:
    "Some ((), s_suc) \<in> set_dist (execute ?round s_i)"
    using round x_eq by simp
  show ?thesis
  proof (rule ro_verifier_query_round_program_final_checks[OF round_unit])
    fix raw idx fv s0 s1 f_i f_len f_pow s2 c_i c_len c_pow s4
    assume raw:
        "Some (raw, s0) \<in>
          set_dist (execute receive_query_index_challenge s_i)"
      and idx_eq: "idx = index (to_nat raw)"
      and query_decommit:
        "Some (fv, s1) \<in>
          set_dist (execute (mmap (ro_check_decommit_on_query fr idx)) s0)"
      and trace_final:
        "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
          set_dist
            (execute
              (mfold (idx, hd fv, clength * scale, 1)
                (ro_receive_query_commits f_fl)) s1)"
      and composition_final:
        "Some ((c_i, final, c_len, c_pow), s4) \<in>
          set_dist
            (execute
              (mfold (idx, cp_eval as fv (h ^ idx * shift),
                  clength * scale, 1)
                (ro_receive_query_commits fl)) s2)"
      and s_suc_eq: "s_suc = s4"
    have results_unit: "results = prefix @ () # suffix"
      using results_eq x_eq by simp
    show ?thesis
      by (rule that[OF prefix round_unit suffix results_unit raw idx_eq
            query_decommit trace_final composition_final s_suc_eq])
  qed
qed


lemma ro_fri_layer_opening_step_authenticated_consumed_chunk:
  fixes s t :: "'f protocol_channel"
  assumes len_pos: "0 < len"
    and idx_bound: "idx < len"
    and outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (ro_fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
  obtains xp xp_path xn xn_path chunk where
    "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    "fri_layer_chunk_authenticated rt len idx chunk t"
    "PTranscript s = chunk @ PTranscript t"
proof -
  from outcome obtain xp s1 xp_path s2 xn s3 xn_path s4 s5 ap1 s6 s7
      ap2 s8 s9 where
    read_xp:
      "Some (xp, s1) \<in> set_dist (execute protocol_absorb_read s)"
    and read_xp_path:
      "Some (xp_path, s2) \<in>
        set_dist (execute (ntimes protocol_absorb_read (floor_log len)) s1)"
    and read_xn:
      "Some (xn, s3) \<in> set_dist (execute protocol_absorb_read s2)"
    and read_xn_path:
      "Some (xn_path, s4) \<in>
        set_dist (execute (ntimes protocol_absorb_read (floor_log len)) s3)"
    and assert_xp:
      "Some ((), s5) \<in> set_dist (execute (assert (xp = x)) s4)"
    and check1:
      "Some (ap1, s6) \<in>
        set_dist (execute (check_authentication_path len idx xp xp_path) s5)"
    and assert_ap1:
      "Some ((), s7) \<in> set_dist (execute (assert (ap1 = rt)) s6)"
    and check2:
      "Some (ap2, s8) \<in>
        set_dist
          (execute
            (check_authentication_path len
              ((idx + len div 2) mod len) xn xn_path) s7)"
    and assert_ap2:
      "Some ((), s9) \<in> set_dist (execute (assert (ap2 = rt)) s8)"
    and ret:
      "Some (out, t) \<in>
        set_dist
          (execute
            (return
              (idx mod (len div 2),
                (xp + xn) div 2 +
                  b * ((xp - xn) div
                    (2 * ((h ^ idx) * shift) ^ pw)),
                len div 2, pw + pw))
            s9)"
    unfolding ro_fri_layer_opening_step_def fri_layer_opening_finish_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  from protocol_absorb_read_outcome_with_lookup_chain[OF read_xp]
  obtain rest1 where
    transcript_s: "PTranscript s = xp # rest1"
    and transcript_s1: "PTranscript s1 = rest1"
    by blast
  from ntimes_protocol_absorb_read_outcome_with_lookup_chain[OF read_xp_path]
  obtain rest2 where
    xp_path_len: "length xp_path = floor_log len"
    and transcript_xp_path: "PTranscript s1 = xp_path @ rest2"
    and transcript_s2: "PTranscript s2 = rest2"
    by blast
  from protocol_absorb_read_outcome_with_lookup_chain[OF read_xn]
  obtain rest3 where
    transcript_s2_xn: "PTranscript s2 = xn # rest3"
    and transcript_s3: "PTranscript s3 = rest3"
    by blast
  from ntimes_protocol_absorb_read_outcome_with_lookup_chain[OF read_xn_path]
  obtain rest4 where
    xn_path_len: "length xn_path = floor_log len"
    and transcript_xn_path: "PTranscript s3 = xn_path @ rest4"
    and transcript_s4: "PTranscript s4 = rest4"
    by blast
  have xp_eq: "xp = x"
    using assert_xp unfolding assert_def
    by (cases "xp = x") (auto simp: throw_no_outcome)
  have s5_eq: "s5 = s4"
    using assert_xp xp_eq unfolding assert_def by simp
  have transcript_s6: "PTranscript s6 = PTranscript s5"
    using check_authentication_path_preserves_channel(2)[OF check1] .
  have ap1_eq: "ap1 = rt"
    using assert_ap1 unfolding assert_def
    by (cases "ap1 = rt") (auto simp: throw_no_outcome)
  have s7_eq: "s7 = s6"
    using assert_ap1 ap1_eq unfolding assert_def by simp
  have transcript_s8: "PTranscript s8 = PTranscript s7"
    using check_authentication_path_preserves_channel(2)[OF check2] .
  have ap2_eq: "ap2 = rt"
    using assert_ap2 unfolding assert_def
    by (cases "ap2 = rt") (auto simp: throw_no_outcome)
  have s9_eq: "s9 = s8"
    using assert_ap2 ap2_eq unfolding assert_def by simp
  have t_eq: "t = s9"
    using ret by simp
  have transcript_t: "PTranscript t = PTranscript s4"
    using transcript_s6 transcript_s8 s5_eq s7_eq s9_eq t_eq by simp
  have sibling_bound: "(idx + len div 2) mod len < len"
    using len_pos by simp
  have finish:
      "Some (out, t) \<in>
        set_dist
          (execute
            (fri_layer_opening_finish b rt idx x len pw
              xp xp_path xn xn_path)
            s4)"
    using assert_xp check1 assert_ap1 check2 assert_ap2 ret
    unfolding fri_layer_opening_finish_def
    by (auto intro!: set_dist_bindI)
  from fri_layer_opening_finish_authenticated_openings
      [OF idx_bound sibling_bound xp_path_len xn_path_len finish]
  obtain xp_opening xn_opening where
    xp_opening_eq:
      "xp_opening =
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path\<rparr>"
    and xn_opening_eq:
      "xn_opening =
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = (idx + len div 2) mod len,
         opening_value = xn,
         opening_path = xn_path\<rparr>"
    and xp_opening_auth: "authenticated_opening_in t xp_opening"
    and xn_opening_auth: "authenticated_opening_in t xn_opening"
    by blast
  have xp_auth:
      "authenticated_opening_in t
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = idx,
         opening_value = xp,
         opening_path = xp_path\<rparr>"
    using xp_opening_auth xp_opening_eq by simp
  have xn_auth:
      "authenticated_opening_in t
        \<lparr>opening_root = rt,
         opening_length = len,
         opening_index = fri_sibling_index len idx,
         opening_value = xn,
         opening_path = xn_path\<rparr>"
    using xn_opening_auth xn_opening_eq
    unfolding fri_sibling_index_def by simp
  let ?chunk = "[xp] @ xp_path @ [xn] @ xn_path"
  have chunk:
    "fri_layer_opening_chunk len xp xp_path xn xn_path ?chunk"
    using xp_path_len xn_path_len
    unfolding fri_layer_opening_chunk_def by simp
  have auth: "fri_layer_chunk_authenticated rt len idx ?chunk t"
    by (rule fri_layer_chunk_authenticatedI[OF chunk xp_auth xn_auth])
  have transcript: "PTranscript s = ?chunk @ PTranscript t"
    using transcript_s transcript_s1 transcript_xp_path transcript_s2
      transcript_s2_xn transcript_s3 transcript_xn_path transcript_s4
      transcript_t
    by simp
  show ?thesis
    by (rule that[OF chunk auth transcript])
qed


lemma mfold_ro_fri_layer_opening_steps_authenticated_consumed_chunks_exists:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw)
              (map ro_fri_layer_opening_step bfs))
            s)"
    and layer_bounds:
      "\<forall>j < length bfs.
        0 < fri_layer_lengths (length bfs) len ! j \<and>
        fri_layer_indices (length bfs) idx len ! j <
          fri_layer_lengths (length bfs) len ! j"
  shows
    "\<exists>layer_chunks chunk.
      fri_layers_transcript (length bfs) len layer_chunks chunk \<and>
      PTranscript s = chunk @ PTranscript t \<and>
      length layer_chunks = length bfs \<and>
      (\<forall>j < length bfs.
        fri_layer_chunk_authenticated (snd (bfs ! j))
          (fri_layer_lengths (length bfs) len ! j)
          (fri_layer_indices (length bfs) idx len ! j)
          (layer_chunks ! j) t)"
  using outcome layer_bounds
proof (induction bfs arbitrary: idx x len pw s out t)
  case Nil
  then show ?case
    by (intro exI[of _ "[]"] exI[of _ "[]"])
      (simp add: fri_layers_transcript_def)
next
  case (Cons bf bfs)
  obtain b rt where bf_eq: "bf = (b, rt)"
    by (cases bf)
  from Cons.prems(1)[unfolded bf_eq]
  obtain idx1 x1 len1 pw1 s1 where
    head:
      "Some ((idx1, x1, len1, pw1), s1) \<in>
        set_dist
          (execute
            (ro_fri_layer_opening_step (b, rt) (idx, x, len, pw)) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx1, x1, len1, pw1)
              (map ro_fri_layer_opening_step bfs))
            s1)"
    by (auto elim!: set_dist_bindE)
  have out1_shape:
      "\<exists>folded.
        (idx1, x1, len1, pw1) =
          (idx mod (len div 2), folded, len div 2, pw + pw)"
  proof (rule ro_fri_layer_opening_step_outcome_with_lookup_chain[OF head])
    fix xp xp_path xn xn_path folded chunk
    assume out_eq:
      "(idx1, x1, len1, pw1) =
        (idx mod (len div 2), folded, len div 2, pw + pw)"
    show ?thesis
      by (rule exI[of _ folded]) (rule out_eq)
  qed
  from out1_shape obtain folded0 where
    out1_eq:
      "(idx1, x1, len1, pw1) =
        (idx mod (len div 2), folded0, len div 2, pw + pw)"
    by blast
  have head_bounds:
      "0 < fri_layer_lengths (length (bf # bfs)) len ! 0 \<and>
       fri_layer_indices (length (bf # bfs)) idx len ! 0 <
         fri_layer_lengths (length (bf # bfs)) len ! 0"
    by (rule Cons.prems(2)[rule_format]) simp
  have len_pos: "0 < len"
    using head_bounds by simp
  have idx_bound: "idx < len"
    using head_bounds by simp
  from ro_fri_layer_opening_step_authenticated_consumed_chunk
      [OF len_pos idx_bound head]
  obtain xp xp_path xn xn_path head_chunk where
    head_shape:
      "fri_layer_opening_chunk len xp xp_path xn xn_path head_chunk"
    and head_auth_s1:
      "fri_layer_chunk_authenticated rt len idx head_chunk s1"
    and head_transcript:
      "PTranscript s = head_chunk @ PTranscript s1"
    by blast
  have tail_bounds:
      "\<forall>j < length bfs.
        0 < fri_layer_lengths (length bfs) (len div 2) ! j \<and>
        fri_layer_indices (length bfs) (idx mod (len div 2))
            (len div 2) ! j <
          fri_layer_lengths (length bfs) (len div 2) ! j"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length bfs"
    have
      "0 < fri_layer_lengths (length (bf # bfs)) len ! Suc j \<and>
       fri_layer_indices (length (bf # bfs)) idx len ! Suc j <
         fri_layer_lengths (length (bf # bfs)) len ! Suc j"
      by (rule Cons.prems(2)[rule_format]) (use j_bound in simp)
    then show
      "0 < fri_layer_lengths (length bfs) (len div 2) ! j \<and>
       fri_layer_indices (length bfs) (idx mod (len div 2))
          (len div 2) ! j <
        fri_layer_lengths (length bfs) (len div 2) ! j"
      by simp
  qed
  from Cons.IH[OF tail[unfolded out1_eq] tail_bounds]
  obtain tail_chunks tail_chunk where
    tail_layers:
      "fri_layers_transcript (length bfs) (len div 2)
        tail_chunks tail_chunk"
    and tail_transcript:
      "PTranscript s1 = tail_chunk @ PTranscript t"
    and tail_chunks_len: "length tail_chunks = length bfs"
    and tail_auth:
      "\<forall>j < length bfs.
        fri_layer_chunk_authenticated (snd (bfs ! j))
          (fri_layer_lengths (length bfs) (len div 2) ! j)
          (fri_layer_indices (length bfs) (idx mod (len div 2))
            (len div 2) ! j)
          (tail_chunks ! j) t"
    by blast
  have s1_t: "s1 \<le> t"
    using mfold_ro_fri_layer_opening_steps_outcome_extends_counter
      [OF tail[unfolded out1_eq]]
    by simp
  have head_auth_t:
      "fri_layer_chunk_authenticated rt len idx head_chunk t"
    by (rule fri_layer_chunk_authenticated_mono[OF head_auth_s1 s1_t])
  let ?layer_chunks = "head_chunk # tail_chunks"
  let ?chunk = "head_chunk @ tail_chunk"
  have layers:
      "fri_layers_transcript (length (bf # bfs)) len ?layer_chunks ?chunk"
    using head_shape tail_layers
    unfolding fri_layers_transcript_def by auto
  have transcript: "PTranscript s = ?chunk @ PTranscript t"
    using head_transcript tail_transcript by simp
  have chunks_len: "length ?layer_chunks = length (bf # bfs)"
    using tail_chunks_len by simp
  have auth:
      "\<forall>j < length (bf # bfs).
        fri_layer_chunk_authenticated (snd ((bf # bfs) ! j))
          (fri_layer_lengths (length (bf # bfs)) len ! j)
          (fri_layer_indices (length (bf # bfs)) idx len ! j)
          (?layer_chunks ! j) t"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length (bf # bfs)"
    show
      "fri_layer_chunk_authenticated (snd ((bf # bfs) ! j))
        (fri_layer_lengths (length (bf # bfs)) len ! j)
        (fri_layer_indices (length (bf # bfs)) idx len ! j)
        (?layer_chunks ! j) t"
    proof (cases j)
      case 0
      then show ?thesis
        using head_auth_t bf_eq by simp
    next
      case (Suc k)
      then have k_bound: "k < length bfs"
        using j_bound by simp
      have tail_at:
          "fri_layer_chunk_authenticated (snd (bfs ! k))
            (fri_layer_lengths (length bfs) (len div 2) ! k)
            (fri_layer_indices (length bfs) (idx mod (len div 2))
              (len div 2) ! k)
            (tail_chunks ! k) t"
        by (rule tail_auth[rule_format, OF k_bound])
      show ?thesis
        using tail_at Suc by simp
    qed
  qed
  show ?case
    by (intro exI[of _ ?layer_chunks] exI[of _ ?chunk])
      (use layers transcript chunks_len auth in simp)
qed

lemma mfold_ro_fri_layer_opening_steps_authenticated_consumed_chunks:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
      "Some (out, t) \<in>
        set_dist
          (execute
            (mfold (idx, x, len, pw)
              (map ro_fri_layer_opening_step bfs))
            s)"
    and layer_bounds:
      "\<forall>j < length bfs.
        0 < fri_layer_lengths (length bfs) len ! j \<and>
        fri_layer_indices (length bfs) idx len ! j <
          fri_layer_lengths (length bfs) len ! j"
  obtains layer_chunks chunk where
    "fri_layers_transcript (length bfs) len layer_chunks chunk"
    "PTranscript s = chunk @ PTranscript t"
    "length layer_chunks = length bfs"
    "\<forall>j < length bfs.
      fri_layer_chunk_authenticated (snd (bfs ! j))
        (fri_layer_lengths (length bfs) len ! j)
        (fri_layer_indices (length bfs) idx len ! j)
        (layer_chunks ! j) t"
  using
    mfold_ro_fri_layer_opening_steps_authenticated_consumed_chunks_exists
      [OF outcome layer_bounds]
  by blast


lemma ro_verifier_query_round_program_authenticated_consumed_fri_chunks:
  fixes s t :: "'f protocol_channel"
  assumes eval_power: "clength * scale = 2 ^ N"
    and trace_count: "length f_fl \<le> N"
    and composition_count: "length fl \<le> N"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (ro_verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw idx fv s0 s1
      query_paths query_chunk
      trace_layers trace_chunk
      composition_layers composition_chunk
      f_i f_len f_pow s2 c_i c_len c_pow
  where
    "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    "idx = index (to_nat raw)"
    "fmlookup (HashMap t)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    "Some (fv, s1) \<in>
      set_dist (execute (mmap (ro_check_decommit_on_query fr idx)) s0)"
    "query_decommitment_transcript idx fv query_paths query_chunk"
    "fri_layers_transcript (length f_fl) (clength * scale)
      trace_layers trace_chunk"
    "PTranscript s1 = trace_chunk @ PTranscript s2"
    "fri_layers_transcript (length fl) (clength * scale)
      composition_layers composition_chunk"
    "PTranscript s2 = composition_chunk @ PTranscript t"
    "query_round_fri_layer_transcripts idx (map snd f_fl) (map snd fl)
      (query_chunk @ trace_chunk @ composition_chunk)
      trace_layers composition_layers"
    "PTranscript s =
      (query_chunk @ trace_chunk @ composition_chunk) @ PTranscript t"
    "length trace_layers = length f_fl"
    "\<forall>j < length f_fl.
      fri_layer_chunk_authenticated (snd (f_fl ! j))
        (fri_layer_lengths (length f_fl) (clength * scale) ! j)
        (fri_layer_indices (length f_fl) idx (clength * scale) ! j)
        (trace_layers ! j) t"
    "length composition_layers = length fl"
    "\<forall>j < length fl.
      fri_layer_chunk_authenticated (snd (fl ! j))
        (fri_layer_lengths (length fl) (clength * scale) ! j)
        (fri_layer_indices (length fl) idx (clength * scale) ! j)
        (composition_layers ! j) t"
    "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
      set_dist
        (execute
          (mfold (idx, hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl)) s1)"
    "Some ((c_i, final, c_len, c_pow), t) \<in>
      set_dist
        (execute
          (mfold (idx, cp_eval as fv (h ^ idx * shift),
              clength * scale, 1)
            (ro_receive_query_commits fl)) s2)"
proof -
  from ro_verifier_query_round_program_final_checks[OF outcome]
  obtain raw idx fv s0 s1 f_i f_len f_pow s2 c_i c_len c_pow s4 where
    raw:
      "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    and idx_eq: "idx = index (to_nat raw)"
    and query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (ro_check_decommit_on_query fr idx)) s0)"
    and trace_fri:
      "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
        set_dist
          (execute
            (mfold (idx, hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl)) s1)"
    and composition_fri:
      "Some ((c_i, final, c_len, c_pow), s4) \<in>
        set_dist
          (execute
            (mfold (idx, cp_eval as fv (h ^ idx * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl)) s2)"
    and t_eq: "t = s4"
    .
  from ro_check_decommit_on_query_outcome_with_lookup_chain[OF query_decommit]
  obtain query_paths query_chunk where
    query_shape:
      "query_decommitment_transcript idx fv query_paths query_chunk"
    and query_transcript:
      "PTranscript s0 = query_chunk @ PTranscript s1"
    and query_ext: "s0 \<le> s1"
    by blast
  have challenge_transcript: "PTranscript s0 = PTranscript s"
    using receive_query_index_challenge_outcome[OF raw] by simp
  have trace_bounds:
      "\<forall>j < length f_fl.
        0 < fri_layer_lengths (length f_fl) (clength * scale) ! j \<and>
        fri_layer_indices (length f_fl) idx (clength * scale) ! j <
          fri_layer_lengths (length f_fl) (clength * scale) ! j"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length f_fl"
    show
      "0 < fri_layer_lengths (length f_fl) (clength * scale) ! j \<and>
       fri_layer_indices (length f_fl) idx (clength * scale) ! j <
         fri_layer_lengths (length f_fl) (clength * scale) ! j"
      using fri_layer_raw_bound[OF j_bound eval_power trace_count, of raw]
        idx_eq
      by simp
  qed
  from mfold_ro_fri_layer_opening_steps_authenticated_consumed_chunks[
      OF trace_fri[unfolded ro_receive_query_commits_def] trace_bounds]
  obtain trace_layers trace_chunk where
    trace_shape:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layers trace_chunk"
    and trace_transcript:
      "PTranscript s1 = trace_chunk @ PTranscript s2"
    and trace_layers_len: "length trace_layers = length f_fl"
    and trace_auth_s2:
      "\<forall>j < length f_fl.
        fri_layer_chunk_authenticated (snd (f_fl ! j))
          (fri_layer_lengths (length f_fl) (clength * scale) ! j)
          (fri_layer_indices (length f_fl) idx (clength * scale) ! j)
          (trace_layers ! j) s2"
    by blast
  have composition_bounds:
      "\<forall>j < length fl.
        0 < fri_layer_lengths (length fl) (clength * scale) ! j \<and>
        fri_layer_indices (length fl) idx (clength * scale) ! j <
          fri_layer_lengths (length fl) (clength * scale) ! j"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length fl"
    show
      "0 < fri_layer_lengths (length fl) (clength * scale) ! j \<and>
       fri_layer_indices (length fl) idx (clength * scale) ! j <
         fri_layer_lengths (length fl) (clength * scale) ! j"
      using fri_layer_raw_bound[
          OF j_bound eval_power composition_count, of raw]
        idx_eq
      by simp
  qed
  from mfold_ro_fri_layer_opening_steps_authenticated_consumed_chunks[
      OF composition_fri[unfolded ro_receive_query_commits_def]
        composition_bounds]
  obtain composition_layers composition_chunk where
    composition_shape:
      "fri_layers_transcript (length fl) (clength * scale)
        composition_layers composition_chunk"
    and composition_transcript:
      "PTranscript s2 = composition_chunk @ PTranscript s4"
    and composition_layers_len: "length composition_layers = length fl"
    and composition_auth_s4:
      "\<forall>j < length fl.
        fri_layer_chunk_authenticated (snd (fl ! j))
          (fri_layer_lengths (length fl) (clength * scale) ! j)
          (fri_layer_indices (length fl) idx (clength * scale) ! j)
          (composition_layers ! j) s4"
    by blast
  have s1_s2: "s1 \<le> s2"
    using mfold_ro_fri_layer_opening_steps_outcome_extends_counter[
      OF trace_fri[unfolded ro_receive_query_commits_def]]
    by simp
  have s2_s4: "s2 \<le> s4"
    using mfold_ro_fri_layer_opening_steps_outcome_extends_counter[
      OF composition_fri[unfolded ro_receive_query_commits_def]]
    by simp
  have s0_s4: "s0 \<le> s4"
    by (rule hash_ext_trans[OF query_ext])
      (rule hash_ext_trans[OF s1_s2 s2_s4])
  have raw_lookup_s0:
      "fmlookup (HashMap s0)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using receive_query_index_challenge_outcome[OF raw] by simp
  have raw_lookup_s4:
      "fmlookup (HashMap s4)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by (rule hash_extension_lookup[OF raw_lookup_s0 s0_s4])
  have raw_lookup_t:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using raw_lookup_s4 t_eq by simp
  have trace_auth_s4:
      "\<forall>j < length f_fl.
        fri_layer_chunk_authenticated (snd (f_fl ! j))
          (fri_layer_lengths (length f_fl) (clength * scale) ! j)
          (fri_layer_indices (length f_fl) idx (clength * scale) ! j)
          (trace_layers ! j) s4"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length f_fl"
    show
      "fri_layer_chunk_authenticated (snd (f_fl ! j))
        (fri_layer_lengths (length f_fl) (clength * scale) ! j)
        (fri_layer_indices (length f_fl) idx (clength * scale) ! j)
        (trace_layers ! j) s4"
      by (rule fri_layer_chunk_authenticated_mono[
            OF trace_auth_s2[rule_format, OF j_bound] s2_s4])
  qed
  have round_layers:
      "query_round_fri_layer_transcripts idx (map snd f_fl) (map snd fl)
        (query_chunk @ trace_chunk @ composition_chunk)
        trace_layers composition_layers"
    unfolding query_round_fri_layer_transcripts_def
    by (intro exI[of _ query_chunk] exI[of _ trace_chunk]
          exI[of _ composition_chunk] exI[of _ fv]
          exI[of _ query_paths])
      (use query_shape trace_shape composition_shape in simp)
  have transcript:
      "PTranscript s =
        (query_chunk @ trace_chunk @ composition_chunk) @ PTranscript t"
    using challenge_transcript query_transcript trace_transcript
      composition_transcript t_eq
    by simp
  have composition_fri_t:
      "Some ((c_i, final, c_len, c_pow), t) \<in>
        set_dist
          (execute
            (mfold (idx, cp_eval as fv (h ^ idx * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl)) s2)"
    using composition_fri t_eq by simp
  have trace_auth_t:
      "\<forall>j < length f_fl.
        fri_layer_chunk_authenticated (snd (f_fl ! j))
          (fri_layer_lengths (length f_fl) (clength * scale) ! j)
          (fri_layer_indices (length f_fl) idx (clength * scale) ! j)
          (trace_layers ! j) t"
    using trace_auth_s4 t_eq by simp
  have composition_auth_t:
      "\<forall>j < length fl.
        fri_layer_chunk_authenticated (snd (fl ! j))
          (fri_layer_lengths (length fl) (clength * scale) ! j)
          (fri_layer_indices (length fl) idx (clength * scale) ! j)
          (composition_layers ! j) t"
    using composition_auth_s4 t_eq by simp
  show ?thesis
    by (rule that[OF raw idx_eq raw_lookup_t query_decommit query_shape
          trace_shape trace_transcript composition_shape
          composition_transcript[unfolded t_eq[symmetric]] round_layers transcript
          trace_layers_len trace_auth_t composition_layers_len
          composition_auth_t trace_fri composition_fri_t])
qed



lemma ro_verifier_query_round_program_recorded_fri_chunks_authenticated:
  fixes s t :: "'f protocol_channel"
  assumes eval_power: "clength * scale = 2 ^ N"
    and trace_count: "length f_fl \<le> N"
    and composition_count: "length fl \<le> N"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (ro_verifier_query_round_program fr f_fl f_final as fl final) s)"
    and recorded_lookup:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) =
        Some recorded_raw"
    and recorded_layers:
      "query_round_fri_layer_transcripts (index (to_nat recorded_raw))
        (map snd f_fl) (map snd fl) chunk
        trace_layers composition_layers"
    and recorded_transcript:
      "PTranscript s = chunk @ PTranscript t"
  obtains fv s0 s1 trace_chunk f_i f_len f_pow s2
      composition_chunk c_i c_len c_pow
  where
    "\<forall>j < length f_fl.
      fri_layer_chunk_authenticated ((map snd f_fl) ! j)
        (fri_layer_lengths (length f_fl) (clength * scale) ! j)
        (fri_layer_indices (length f_fl) (index (to_nat recorded_raw))
          (clength * scale) ! j)
        (trace_layers ! j) t"
    "fri_layers_transcript (length f_fl) (clength * scale)
      trace_layers trace_chunk"
    "PTranscript s1 = trace_chunk @ PTranscript s2"
    "\<forall>j < length fl.
      fri_layer_chunk_authenticated ((map snd fl) ! j)
        (fri_layer_lengths (length fl) (clength * scale) ! j)
        (fri_layer_indices (length fl) (index (to_nat recorded_raw))
          (clength * scale) ! j)
        (composition_layers ! j) t"
    "fri_layers_transcript (length fl) (clength * scale)
      composition_layers composition_chunk"
    "PTranscript s2 = composition_chunk @ PTranscript t"
    "Some (recorded_raw, s0) \<in>
      set_dist (execute receive_query_index_challenge s)"
    "Some (fv, s1) \<in>
      set_dist
        (execute
          (mmap
            (ro_check_decommit_on_query fr (index (to_nat recorded_raw))))
          s0)"
    "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
      set_dist
        (execute
          (mfold
            (index (to_nat recorded_raw), hd fv, clength * scale, 1)
            (ro_receive_query_commits f_fl))
          s1)"
    "Some ((c_i, final, c_len, c_pow), t) \<in>
      set_dist
        (execute
          (mfold
            (index (to_nat recorded_raw),
              cp_eval as fv
                (h ^ index (to_nat recorded_raw) * shift),
              clength * scale, 1)
            (ro_receive_query_commits fl))
          s2)"
proof -
  from ro_verifier_query_round_program_authenticated_consumed_fri_chunks[
      OF eval_power trace_count composition_count outcome]
  obtain raw idx fv s0 s1 query_paths query_chunk
      actual_trace_layers trace_chunk
      actual_composition_layers composition_chunk
      f_i f_len f_pow s2 c_i c_len c_pow where
    raw:
      "Some (raw, s0) \<in> set_dist (execute receive_query_index_challenge s)"
    and idx_eq: "idx = index (to_nat raw)"
    and actual_lookup:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    and query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (ro_check_decommit_on_query fr idx)) s0)"
    and query_shape:
      "query_decommitment_transcript idx fv query_paths query_chunk"
    and trace_shape:
      "fri_layers_transcript (length f_fl) (clength * scale)
        actual_trace_layers trace_chunk"
    and trace_transcript:
      "PTranscript s1 = trace_chunk @ PTranscript s2"
    and composition_shape:
      "fri_layers_transcript (length fl) (clength * scale)
        actual_composition_layers composition_chunk"
    and composition_transcript:
      "PTranscript s2 = composition_chunk @ PTranscript t"
    and actual_layers:
      "query_round_fri_layer_transcripts idx (map snd f_fl) (map snd fl)
        (query_chunk @ trace_chunk @ composition_chunk)
        actual_trace_layers actual_composition_layers"
    and actual_transcript:
      "PTranscript s =
        (query_chunk @ trace_chunk @ composition_chunk) @ PTranscript t"
    and actual_trace_len:
      "length actual_trace_layers = length f_fl"
    and actual_trace_auth:
      "\<forall>j < length f_fl.
        fri_layer_chunk_authenticated (snd (f_fl ! j))
          (fri_layer_lengths (length f_fl) (clength * scale) ! j)
          (fri_layer_indices (length f_fl) idx (clength * scale) ! j)
          (actual_trace_layers ! j) t"
    and actual_composition_len:
      "length actual_composition_layers = length fl"
    and actual_composition_auth:
      "\<forall>j < length fl.
        fri_layer_chunk_authenticated (snd (fl ! j))
          (fri_layer_lengths (length fl) (clength * scale) ! j)
          (fri_layer_indices (length fl) idx (clength * scale) ! j)
          (actual_composition_layers ! j) t"
    and trace_fri:
      "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
        set_dist
          (execute
            (mfold (idx, hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl)) s1)"
    and composition_fri:
      "Some ((c_i, final, c_len, c_pow), t) \<in>
        set_dist
          (execute
            (mfold (idx, cp_eval as fv (h ^ idx * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl)) s2)"
    .
  have raw_eq: "raw = recorded_raw"
    using actual_lookup recorded_lookup by simp
  have idx_recorded: "idx = index (to_nat recorded_raw)"
    using idx_eq raw_eq by simp
  have chunk_eq:
      "query_chunk @ trace_chunk @ composition_chunk = chunk"
    using actual_transcript recorded_transcript by simp
  have actual_layers_recorded_chunk:
      "query_round_fri_layer_transcripts (index (to_nat recorded_raw))
        (map snd f_fl) (map snd fl) chunk
        actual_trace_layers actual_composition_layers"
    using actual_layers idx_recorded chunk_eq by simp
  have trace_layers_eq: "trace_layers = actual_trace_layers"
    by (rule query_round_fri_layer_transcripts_unique(1)[
          OF recorded_layers actual_layers_recorded_chunk])
  have composition_layers_eq:
      "composition_layers = actual_composition_layers"
    by (rule query_round_fri_layer_transcripts_unique(2)[
          OF recorded_layers actual_layers_recorded_chunk])
  have trace_shape_recorded:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layers trace_chunk"
    using trace_shape trace_layers_eq by simp
  have composition_shape_recorded:
      "fri_layers_transcript (length fl) (clength * scale)
        composition_layers composition_chunk"
    using composition_shape composition_layers_eq by simp
  have trace_auth:
      "\<forall>j < length f_fl.
        fri_layer_chunk_authenticated ((map snd f_fl) ! j)
          (fri_layer_lengths (length f_fl) (clength * scale) ! j)
          (fri_layer_indices (length f_fl) (index (to_nat recorded_raw))
            (clength * scale) ! j)
          (trace_layers ! j) t"
    using actual_trace_auth idx_recorded trace_layers_eq by simp
  have composition_auth:
      "\<forall>j < length fl.
        fri_layer_chunk_authenticated ((map snd fl) ! j)
          (fri_layer_lengths (length fl) (clength * scale) ! j)
          (fri_layer_indices (length fl) (index (to_nat recorded_raw))
            (clength * scale) ! j)
          (composition_layers ! j) t"
    using actual_composition_auth idx_recorded composition_layers_eq by simp
  have raw_recorded:
      "Some (recorded_raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    using raw raw_eq by simp
  have query_decommit_recorded:
      "Some (fv, s1) \<in>
        set_dist
          (execute
            (mmap
              (ro_check_decommit_on_query fr (index (to_nat recorded_raw))))
            s0)"
    using query_decommit idx_recorded by simp
  have trace_fri_recorded:
      "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat recorded_raw), hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl))
            s1)"
    using trace_fri idx_recorded by simp
  have composition_fri_recorded:
      "Some ((c_i, final, c_len, c_pow), t) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat recorded_raw),
                cp_eval as fv
                  (h ^ index (to_nat recorded_raw) * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl))
            s2)"
    using composition_fri idx_recorded by simp
  show ?thesis
    by (rule that[OF trace_auth trace_shape_recorded trace_transcript
          composition_auth composition_shape_recorded composition_transcript
          raw_recorded query_decommit_recorded trace_fri_recorded
          composition_fri_recorded])
qed



definition ro_recorded_query_fri_accepted_evidence
  where
    "ro_recorded_query_fri_accepted_evidence fr f_fl f_final as fl final
        raw trace_layers composition_layers final_state \<longleftrightarrow>
      (\<exists>round_state round_final fv s0 s1 trace_chunk
          f_i f_len f_pow s2 composition_chunk c_i c_len c_pow.
        Some ((), round_final) \<in>
          set_dist
            (execute
              (ro_verifier_query_round_program
                fr f_fl f_final as fl final)
              round_state) \<and>
        round_final \<le> final_state \<and>
        (\<forall>j < length f_fl.
          fri_layer_chunk_authenticated ((map snd f_fl) ! j)
            (fri_layer_lengths (length f_fl) (clength * scale) ! j)
            (fri_layer_indices (length f_fl) (index (to_nat raw))
              (clength * scale) ! j)
            (trace_layers ! j) final_state) \<and>
        fri_layers_transcript (length f_fl) (clength * scale)
          trace_layers trace_chunk \<and>
        PTranscript s1 = trace_chunk @ PTranscript s2 \<and>
        (\<forall>j < length fl.
          fri_layer_chunk_authenticated ((map snd fl) ! j)
            (fri_layer_lengths (length fl) (clength * scale) ! j)
            (fri_layer_indices (length fl) (index (to_nat raw))
              (clength * scale) ! j)
            (composition_layers ! j) final_state) \<and>
        fri_layers_transcript (length fl) (clength * scale)
          composition_layers composition_chunk \<and>
        PTranscript s2 = composition_chunk @ PTranscript round_final \<and>
        Some (raw, s0) \<in>
          set_dist (execute receive_query_index_challenge round_state) \<and>
        Some (fv, s1) \<in>
          set_dist
            (execute
              (mmap
                (ro_check_decommit_on_query fr (index (to_nat raw))))
              s0) \<and>
        Some ((f_i, f_final, f_len, f_pow), s2) \<in>
          set_dist
            (execute
              (mfold
                (index (to_nat raw), hd fv, clength * scale, 1)
                (ro_receive_query_commits f_fl))
              s1) \<and>
        Some ((c_i, final, c_len, c_pow), round_final) \<in>
          set_dist
            (execute
              (mfold
                (index (to_nat raw),
                  cp_eval as fv (h ^ index (to_nat raw) * shift),
                  clength * scale, 1)
                (ro_receive_query_commits fl))
              s2))"


lemma ro_verifier_query_round_program_recorded_fri_accepted_evidence:
  fixes s t final_state :: "'f protocol_channel"
  assumes eval_power: "clength * scale = 2 ^ N"
    and trace_count: "length f_fl \<le> N"
    and composition_count: "length fl \<le> N"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (ro_verifier_query_round_program fr f_fl f_final as fl final) s)"
    and recorded_lookup:
      "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s) (PState s)) =
        Some recorded_raw"
    and recorded_layers:
      "query_round_fri_layer_transcripts (index (to_nat recorded_raw))
        (map snd f_fl) (map snd fl) chunk
        trace_layers composition_layers"
    and recorded_transcript:
      "PTranscript s = chunk @ PTranscript t"
    and final_ext: "t \<le> final_state"
  shows
    "ro_recorded_query_fri_accepted_evidence
      fr f_fl f_final as fl final recorded_raw
      trace_layers composition_layers final_state"
proof -
  from ro_verifier_query_round_program_recorded_fri_chunks_authenticated[
      OF eval_power trace_count composition_count outcome recorded_lookup
        recorded_layers recorded_transcript]
  obtain fv s0 s1 trace_chunk f_i f_len f_pow s2
      composition_chunk c_i c_len c_pow where
    trace_auth_t:
      "\<forall>j < length f_fl.
        fri_layer_chunk_authenticated ((map snd f_fl) ! j)
          (fri_layer_lengths (length f_fl) (clength * scale) ! j)
          (fri_layer_indices (length f_fl) (index (to_nat recorded_raw))
            (clength * scale) ! j)
          (trace_layers ! j) t"
    and trace_shape:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layers trace_chunk"
    and trace_transcript:
      "PTranscript s1 = trace_chunk @ PTranscript s2"
    and composition_auth_t:
      "\<forall>j < length fl.
        fri_layer_chunk_authenticated ((map snd fl) ! j)
          (fri_layer_lengths (length fl) (clength * scale) ! j)
          (fri_layer_indices (length fl) (index (to_nat recorded_raw))
            (clength * scale) ! j)
          (composition_layers ! j) t"
    and composition_shape:
      "fri_layers_transcript (length fl) (clength * scale)
        composition_layers composition_chunk"
    and composition_transcript:
      "PTranscript s2 = composition_chunk @ PTranscript t"
    and raw:
      "Some (recorded_raw, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and query_decommit:
      "Some (fv, s1) \<in>
        set_dist
          (execute
            (mmap
              (ro_check_decommit_on_query fr (index (to_nat recorded_raw))))
            s0)"
    and trace_fri:
      "Some ((f_i, f_final, f_len, f_pow), s2) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat recorded_raw), hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl))
            s1)"
    and composition_fri:
      "Some ((c_i, final, c_len, c_pow), t) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat recorded_raw),
                cp_eval as fv
                  (h ^ index (to_nat recorded_raw) * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl))
            s2)"
    .
  have trace_auth_final:
      "\<forall>j < length f_fl.
        fri_layer_chunk_authenticated ((map snd f_fl) ! j)
          (fri_layer_lengths (length f_fl) (clength * scale) ! j)
          (fri_layer_indices (length f_fl) (index (to_nat recorded_raw))
            (clength * scale) ! j)
          (trace_layers ! j) final_state"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length f_fl"
    show
      "fri_layer_chunk_authenticated ((map snd f_fl) ! j)
        (fri_layer_lengths (length f_fl) (clength * scale) ! j)
        (fri_layer_indices (length f_fl) (index (to_nat recorded_raw))
          (clength * scale) ! j)
        (trace_layers ! j) final_state"
      by (rule fri_layer_chunk_authenticated_mono[
            OF trace_auth_t[rule_format, OF j_bound] final_ext])
  qed
  have composition_auth_final:
      "\<forall>j < length fl.
        fri_layer_chunk_authenticated ((map snd fl) ! j)
          (fri_layer_lengths (length fl) (clength * scale) ! j)
          (fri_layer_indices (length fl) (index (to_nat recorded_raw))
            (clength * scale) ! j)
          (composition_layers ! j) final_state"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < length fl"
    show
      "fri_layer_chunk_authenticated ((map snd fl) ! j)
        (fri_layer_lengths (length fl) (clength * scale) ! j)
        (fri_layer_indices (length fl) (index (to_nat recorded_raw))
          (clength * scale) ! j)
        (composition_layers ! j) final_state"
      by (rule fri_layer_chunk_authenticated_mono[
            OF composition_auth_t[rule_format, OF j_bound] final_ext])
  qed
  show ?thesis
    unfolding ro_recorded_query_fri_accepted_evidence_def
    apply (rule exI[of _ s])
    apply (rule exI[of _ t])
    apply (rule exI[of _ fv])
    apply (rule exI[of _ s0])
    apply (rule exI[of _ s1])
    apply (rule exI[of _ trace_chunk])
    apply (rule exI[of _ f_i])
    apply (rule exI[of _ f_len])
    apply (rule exI[of _ f_pow])
    apply (rule exI[of _ s2])
    apply (rule exI[of _ composition_chunk])
    apply (rule exI[of _ c_i])
    apply (rule exI[of _ c_len])
    apply (rule exI[of _ c_pow])
    using outcome final_ext trace_auth_final trace_shape trace_transcript
      composition_auth_final composition_shape composition_transcript raw
      query_decommit trace_fri composition_fri
    apply simp
    done
qed



lemma
  ro_checked_staged_query_program_with_witnesses_recorded_fri_accepted_evidence:
  fixes builder sent verifier_state verifier_final :: "'f protocol_channel"
    and rest :: "'f list"
  assumes eval_power: "clength * scale = 2 ^ N"
    and trace_count: "length f_fl \<le> N"
    and composition_count: "length fl \<le> N"
    and controlled: "staged_adversary_controlled budgets A"
    and bound: "i + n \<le> length (query_opening_budgets budgets)"
    and builder_out:
      "Some ((raws, query_states, chunks), sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots builder i n)
            builder)"
    and sent_ext: "sent \<le> verifier_state"
    and state_eq: "PState verifier_state = PState builder"
    and counter_eq:
      "PQueryCounter verifier_state = PQueryCounter builder"
    and transcript_prefix:
      "PTranscript verifier_state = List.concat chunks @ rest"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and verifier_out:
      "Some (results, verifier_final) \<in>
        set_dist
          (execute
            (ntimes
              (ro_verifier_query_round_program
                fr f_fl f_final as fl final)
              n)
            verifier_state)"
    and trace_round_layers_len: "length trace_round_layers = n"
    and composition_round_layers_len:
      "length composition_round_layers = n"
    and round_layers:
      "\<forall>j < n.
        query_round_fri_layer_transcripts
          (index (to_nat (raws ! j)))
          trace_roots composition_roots (chunks ! j)
          (trace_round_layers ! j) (composition_round_layers ! j)"
  shows
    "verifier_state \<le> verifier_final \<and>
     length raws = n \<and>
     length query_states = n \<and>
     length chunks = n \<and>
     (\<forall>j < n.
       ro_recorded_query_fri_accepted_evidence
         fr f_fl f_final as fl final (raws ! j)
         (trace_round_layers ! j) (composition_round_layers ! j)
         verifier_final)"
  using bound builder_out sent_ext state_eq counter_eq transcript_prefix
    verifier_out trace_round_layers_len composition_round_layers_len
    round_layers
proof (induction n arbitrary: i builder sent verifier_state verifier_final
    raws query_states chunks results trace_round_layers
    composition_round_layers)
  case 0
  then show ?case
    by (auto intro: hash_ext_refl)
next
  case (Suc n)
  let ?round =
    "ro_verifier_query_round_program fr f_fl f_final as fl final"
  from Suc.prems(2)
  obtain witness_raw witness_chunk raws_tail query_states_tail chunks_tail
      ws1 ws2 ws_assert ws3 where
    witness_challenge:
      "Some (witness_raw, ws1) \<in>
        set_dist (execute receive_query_index_challenge builder)"
    and witness_stage:
      "Some (witness_chunk, ws2) \<in>
        set_dist (execute (query_opening_stage A i witness_raw) ws1)"
    and witness_assert:
      "Some ((), ws_assert) \<in>
        set_dist
          (execute
            (assert
              (verifier_query_round_chunk (index (to_nat witness_raw))
                trace_roots composition_roots witness_chunk))
            ws2)"
    and witness_record:
      "Some ((), ws3) \<in>
        set_dist (execute (ro_record_staged_messages witness_chunk) ws_assert)"
    and witness_tail:
      "Some ((raws_tail, query_states_tail, chunks_tail), sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program_with_witnesses A trace_roots
              composition_roots ws3 (Suc i) n)
            ws3)"
    and raws_eq: "raws = witness_raw # raws_tail"
    and query_states_eq:
      "query_states = builder # query_states_tail"
    and chunks_eq: "chunks = witness_chunk # chunks_tail"
    unfolding ro_checked_staged_query_program_with_witnesses.simps Let_def
    by (auto elim!: set_dist_bindE split: prod.splits)
  have witness_assert_props:
      "ws_assert = ws2 \<and>
       verifier_query_round_chunk (index (to_nat witness_raw))
         trace_roots composition_roots witness_chunk"
    using witness_assert
    unfolding assert_def
    by (cases
        "verifier_query_round_chunk (index (to_nat witness_raw))
          trace_roots composition_roots witness_chunk")
      (simp_all add: throw_no_outcome)
  have ws_assert_eq: "ws_assert = ws2"
    using witness_assert_props by simp
  have witness_record':
      "Some ((), ws3) \<in>
        set_dist (execute (ro_record_staged_messages witness_chunk) ws2)"
    using witness_record ws_assert_eq by simp

  from Suc.prems(7)
  obtain verifier_mid results_tail where
    verifier_head:
      "Some ((), verifier_mid) \<in>
        set_dist (execute ?round verifier_state)"
    and verifier_tail:
      "Some (results_tail, verifier_final) \<in>
        set_dist (execute (ntimes ?round n) verifier_mid)"
    and results_eq: "results = () # results_tail"
    by (auto elim!: set_dist_bindE)

  have ordinary:
      "Some (chunks, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots
              composition_roots i (Suc n))
            builder)"
    by (rule
        ro_checked_staged_query_program_with_witnesses_projection_outcome[
          OF Suc.prems(2)])

  from ro_checked_staged_query_program_Suc_verifier_round_sync_lookupE[
      where budgets=budgets and A=A and i=i and n=n
        and builder=builder and sent=sent
        and verifier_state=verifier_state and verifier_state'=verifier_mid
        and chunks=chunks and rest=rest
        and trace_roots=trace_roots and composition_roots=composition_roots
        and f_fl=f_fl and fl=fl and fr=fr and f_final=f_final
        and as=as and final=final,
      OF controlled Suc.prems(1) ordinary Suc.prems(3) Suc.prems(4)
        Suc.prems(5) Suc.prems(6) trace_roots_eq composition_roots_eq
        verifier_head]
  obtain sync_raw sync_chunk sync_chunks ss1 ss2 ss3 where
    sync_challenge:
      "Some (sync_raw, ss1) \<in>
        set_dist (execute receive_query_index_challenge builder)"
    and sync_stage:
      "Some (sync_chunk, ss2) \<in>
        set_dist (execute (query_opening_stage A i sync_raw) ss1)"
    and sync_chunk_shape:
      "verifier_query_round_chunk (index (to_nat sync_raw))
        trace_roots composition_roots sync_chunk"
    and sync_record:
      "Some ((), ss3) \<in>
        set_dist (execute (ro_record_staged_messages sync_chunk) ss2)"
    and sync_tail:
      "Some (sync_chunks, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n)
            ss3)"
    and sync_chunks_eq: "chunks = sync_chunk # sync_chunks"
    and state_mid_sync: "PState verifier_mid = PState ss3"
    and transcript_mid:
      "PTranscript verifier_mid = List.concat sync_chunks @ rest"
    and verifier_step_ext: "verifier_state \<le> verifier_mid"
    and counter_mid:
      "PQueryCounter verifier_mid = Suc (PQueryCounter builder)"
    and sync_head_chain:
      "ro_absorb_lookup_chain sent (PState builder) sync_chunk (PState ss3)"
    and sync_recorded:
      "fmlookup (HashMap sent)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some sync_raw"
    .

  have i_bound: "i < length (query_opening_budgets budgets)"
    using Suc.prems(1) by simp
  have tail_bound:
      "Suc i + n \<le> length (query_opening_budgets budgets)"
  proof -
    have eq: "Suc i + n = i + Suc n"
      by simp
    show ?thesis
      by (subst eq) (rule Suc.prems(1))
  qed
  have witness_stage_controlled:
      "controlled_ro_program (query_opening_budgets budgets ! i)
        (query_opening_stage A i witness_raw)"
    using controlled i_bound
    unfolding staged_adversary_controlled_def by blast
  have witness_challenge_props:
      "builder \<le> ws1 \<and>
       PState ws1 = PState builder \<and>
       PTranscript ws1 = PTranscript builder \<and>
       fmlookup (HashMap ws1)
         (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
         Some witness_raw"
    by (rule receive_query_index_challenge_outcome[OF witness_challenge])
  have witness_challenge_state: "PState ws1 = PState builder"
    using witness_challenge_props by simp
  have witness_stage_ext: "ws1 \<le> ws2"
    using controlled_ro_program_extension[OF witness_stage_controlled]
      witness_stage
    unfolding hash_extension_preserving_def by blast
  have witness_stage_state: "PState ws2 = PState ws1"
    using controlled_stage_outcome_fields[
      OF witness_stage_controlled witness_stage]
    by simp
  have witness_record_chain:
      "ro_absorb_lookup_chain ws3 (PState ws2)
        witness_chunk (PState ws3) \<and>
       ws2 \<le> ws3"
    by (rule ro_record_staged_messages_absorb_lookup_chain[
          OF witness_record'])
  have witness_tail_ordinary:
      "Some (chunks_tail, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n)
            ws3)"
    by (rule
        ro_checked_staged_query_program_with_witnesses_projection_outcome[
          OF witness_tail])
  have witness_tail_ext: "ws3 \<le> sent"
    using ro_checked_staged_query_program_absorb_lookup_chain[
      OF controlled tail_bound witness_tail_ordinary]
    by simp
  have ws1_sent: "ws1 \<le> sent"
    by (rule hash_ext_trans[OF witness_stage_ext])
      (rule hash_ext_trans[
        OF conjunct2[OF witness_record_chain] witness_tail_ext])
  have witness_recorded:
      "fmlookup (HashMap sent)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some witness_raw"
    by (rule hash_extension_lookup)
      (use witness_challenge_props ws1_sent in simp_all)
  have sync_raw_eq: "sync_raw = witness_raw"
    using sync_recorded witness_recorded by simp
  have sync_chunk_eq: "sync_chunk = witness_chunk"
    and sync_chunks_tail_eq: "sync_chunks = chunks_tail"
    using sync_chunks_eq chunks_eq by simp_all

  have witness_head_chain:
      "ro_absorb_lookup_chain sent (PState builder)
        witness_chunk (PState ws3)"
  proof -
    have chain:
        "ro_absorb_lookup_chain sent (PState ws2)
          witness_chunk (PState ws3)"
      by (rule ro_absorb_lookup_chain_mono[
            OF conjunct1[OF witness_record_chain] witness_tail_ext])
    show ?thesis
      using chain witness_challenge_state witness_stage_state by simp
  qed
  have head_state_eq: "PState ss3 = PState ws3"
  proof -
    have sync_chain:
        "ro_absorb_lookup_chain sent (PState builder)
          witness_chunk (PState ss3)"
      using sync_head_chain sync_chunk_eq by simp
    show ?thesis
      by (rule ro_absorb_lookup_chain_functional[
            OF sync_chain witness_head_chain])
  qed
  have witness_counter_ws3:
      "PQueryCounter ws3 = Suc (PQueryCounter builder)"
    by (rule ro_checked_staged_query_record_state_counter[
          OF controlled i_bound witness_challenge witness_stage
            witness_record'])
  have sent_mid: "sent \<le> verifier_mid"
    by (rule hash_ext_trans[OF Suc.prems(3) verifier_step_ext])
  have tail_state_eq: "PState verifier_mid = PState ws3"
    using state_mid_sync head_state_eq by simp
  have tail_counter_eq:
      "PQueryCounter verifier_mid = PQueryCounter ws3"
    using counter_mid witness_counter_ws3 by simp
  have tail_transcript:
      "PTranscript verifier_mid = List.concat chunks_tail @ rest"
    using transcript_mid sync_chunks_tail_eq by simp

  have tail_trace_layers_len:
      "length (tl trace_round_layers) = n"
    using Suc.prems(8) by simp
  have tail_composition_layers_len:
      "length (tl composition_round_layers) = n"
    using Suc.prems(9) by simp
  have tail_round_layers:
      "\<forall>j < n.
        query_round_fri_layer_transcripts
          (index (to_nat (raws_tail ! j)))
          trace_roots composition_roots (chunks_tail ! j)
          (tl trace_round_layers ! j)
          (tl composition_round_layers ! j)"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < n"
    have at_suc:
        "query_round_fri_layer_transcripts
          (index (to_nat (raws ! Suc j)))
          trace_roots composition_roots (chunks ! Suc j)
          (trace_round_layers ! Suc j)
          (composition_round_layers ! Suc j)"
      by (rule Suc.prems(10)[rule_format])
        (use j_bound in simp)
    show
      "query_round_fri_layer_transcripts
        (index (to_nat (raws_tail ! j)))
        trace_roots composition_roots (chunks_tail ! j)
        (tl trace_round_layers ! j)
        (tl composition_round_layers ! j)"
      using at_suc raws_eq chunks_eq Suc.prems(8) Suc.prems(9)
      by (cases trace_round_layers; cases composition_round_layers)
        simp_all
  qed

  have tail_result:
      "verifier_mid \<le> verifier_final \<and>
       length raws_tail = n \<and>
       length query_states_tail = n \<and>
       length chunks_tail = n \<and>
       (\<forall>j < n.
         ro_recorded_query_fri_accepted_evidence
           fr f_fl f_final as fl final (raws_tail ! j)
           (tl trace_round_layers ! j)
           (tl composition_round_layers ! j)
           verifier_final)"
    by (rule Suc.IH[OF tail_bound witness_tail sent_mid tail_state_eq
          tail_counter_eq tail_transcript verifier_tail
          tail_trace_layers_len tail_composition_layers_len
          tail_round_layers])
  have verifier_mid_final: "verifier_mid \<le> verifier_final"
    using tail_result by simp

  have head_layers:
      "query_round_fri_layer_transcripts
        (index (to_nat witness_raw))
        (map snd f_fl) (map snd fl) witness_chunk
        (trace_round_layers ! 0) (composition_round_layers ! 0)"
  proof -
    have at_zero:
        "query_round_fri_layer_transcripts
          (index (to_nat (raws ! 0)))
          trace_roots composition_roots (chunks ! 0)
          (trace_round_layers ! 0) (composition_round_layers ! 0)"
      by (rule Suc.prems(10)[rule_format]) simp
    show ?thesis
      using at_zero raws_eq chunks_eq trace_roots_eq composition_roots_eq
      by simp
  qed
  have head_transcript:
      "PTranscript verifier_state =
        witness_chunk @ PTranscript verifier_mid"
    using Suc.prems(6) transcript_mid chunks_eq sync_chunks_tail_eq
    by simp
  have sync_lookup_mid:
      "fmlookup (HashMap verifier_mid)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some sync_raw"
    by (rule hash_extension_lookup[OF sync_recorded sent_mid])
  have head_lookup_mid:
      "fmlookup (HashMap verifier_mid)
        (QueryIndexChallenge
          (PQueryCounter verifier_state) (PState verifier_state)) =
        Some witness_raw"
    using sync_lookup_mid sync_raw_eq Suc.prems(4) Suc.prems(5)
    by simp
  have head_evidence:
      "ro_recorded_query_fri_accepted_evidence
        fr f_fl f_final as fl final witness_raw
        (trace_round_layers ! 0) (composition_round_layers ! 0)
        verifier_final"
    by (rule
        ro_verifier_query_round_program_recorded_fri_accepted_evidence[
          OF eval_power trace_count composition_count verifier_head
            head_lookup_mid head_layers head_transcript verifier_mid_final])

  have verifier_ext_final: "verifier_state \<le> verifier_final"
    by (rule hash_ext_trans[OF verifier_step_ext verifier_mid_final])
  have lengths:
      "length raws = Suc n \<and>
       length query_states = Suc n \<and>
       length chunks = Suc n"
    using tail_result raws_eq query_states_eq chunks_eq by simp
  have all_evidence:
      "\<forall>j < Suc n.
        ro_recorded_query_fri_accepted_evidence
          fr f_fl f_final as fl final (raws ! j)
          (trace_round_layers ! j) (composition_round_layers ! j)
          verifier_final"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show
      "ro_recorded_query_fri_accepted_evidence
        fr f_fl f_final as fl final (raws ! j)
        (trace_round_layers ! j) (composition_round_layers ! j)
        verifier_final"
    proof (cases j)
      case 0
      then show ?thesis
        using head_evidence raws_eq by simp
    next
      case (Suc k)
      then have k_bound: "k < n"
        using j_bound by simp
      have tail_at:
          "ro_recorded_query_fri_accepted_evidence
            fr f_fl f_final as fl final (raws_tail ! k)
            (tl trace_round_layers ! k)
            (tl composition_round_layers ! k)
            verifier_final"
        using tail_result k_bound by simp
      show ?thesis
        using tail_at raws_eq Suc Suc.prems(8) Suc.prems(9)
        by (cases trace_round_layers; cases composition_round_layers)
          simp_all
    qed
  qed
  show ?case
    using verifier_ext_final lengths all_evidence by simp
qed

end
end
