theory Staged_Security_Experiment_RO_Query_Round_Replay
  imports Staged_Security_Experiment_RO_Query_Synchronization
begin

context soundness
begin

text \<open>
  Outcome facts for the absorbing verifier are phrased as random-oracle lookup
  chains in the final map.  They deliberately avoid the legacy deterministic
  transcript-state fold.
\<close>

lemma protocol_absorb_read_outcome_with_lookup_chain:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some (y, t) \<in> set_dist (execute protocol_absorb_read s)"
  obtains xs where
    "PTranscript s = y # xs"
    "PTranscript t = xs"
    "ro_absorb_lookup_chain t (PState s) [y] (PState t)"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
proof -
  have transcript_nonempty: "PTranscript s \<noteq> []"
    using outcome
    unfolding protocol_absorb_read_def assert_def
    by (auto simp: throw_no_outcome elim!: set_dist_bindE)
  then obtain x xs where transcript_s: "PTranscript s = x # xs"
    by (cases "PTranscript s") auto
  let ?base = "s\<lparr>PTranscript := []\<rparr>"
  have start_eq: "?base\<lparr>PTranscript := x # xs\<rparr> = s"
    using transcript_s by simp
  have outcome':
    "Some (y, t) \<in>
      set_dist
        (execute protocol_absorb_read
          (?base\<lparr>PTranscript := x # xs\<rparr>))"
    using outcome start_eq by simp
  from protocol_absorb_read_cons_outcome[OF outcome']
  obtain h u where
    y_eq: "y = x"
    and hash_out:
      "Some (h, u) \<in>
        set_dist
          (execute (hash (TranscriptAbsorb (PState ?base) x))
            (?base\<lparr>PTranscript := x # xs\<rparr>))"
    and t_eq: "t = u\<lparr>PState := h, PTranscript := xs\<rparr>"
    and state_u: "PState u = PState ?base"
    and transcript_u: "PTranscript u = x # xs"
    and ext_start_u: "?base\<lparr>PTranscript := x # xs\<rparr> \<le> u"
    .
  have ext_s_u: "s \<le> u"
    using ext_start_u start_eq by simp
  have ext_u_t: "u \<le> t"
    unfolding t_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have ext_s_t: "s \<le> t"
    by (rule hash_ext_trans[OF ext_s_u ext_u_t])
  have lookup_u:
    "fmlookup (HashMap u)
      (TranscriptAbsorb (PState s) y) = Some h"
    using protocol_merkle.hash_outcome(2)[OF hash_out] y_eq start_eq by simp
  have lookup_t:
    "fmlookup (HashMap t)
      (TranscriptAbsorb (PState s) y) = Some h"
    by (rule hash_extension_lookup[OF lookup_u ext_u_t])
  have chain:
    "ro_absorb_lookup_chain t (PState s) [y] (PState t)"
    using lookup_t t_eq by simp
  have counter_u: "PQueryCounter u = PQueryCounter s"
    using protocol_hash_channel_preserves(6)[OF hash_out] start_eq by simp
  have counter_t: "PQueryCounter t = PQueryCounter s"
    using counter_u t_eq by simp
  have transcript_t: "PTranscript t = xs"
    using t_eq by simp
  show ?thesis
    by (rule that[of xs])
      (use transcript_s y_eq transcript_t chain ext_s_t counter_t in simp_all)
qed


lemma ntimes_protocol_absorb_read_outcome_with_lookup_chain:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some (ys, t) \<in>
      set_dist (execute (ntimes protocol_absorb_read n) s)"
  obtains rest where
    "length ys = n"
    "PTranscript s = ys @ rest"
    "PTranscript t = rest"
    "ro_absorb_lookup_chain t (PState s) ys (PState t)"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
proof -
  have result:
    "\<exists>rest.
      length ys = n \<and>
      PTranscript s = ys @ rest \<and>
      PTranscript t = rest \<and>
      ro_absorb_lookup_chain t (PState s) ys (PState t) \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s"
    using outcome
  proof (induction n arbitrary: s ys t)
    case 0
    then have ys_eq: "ys = []" and t_eq: "t = s"
      by simp_all
    show ?case
      by (intro exI[of _ "PTranscript t"] conjI)
        (use ys_eq t_eq in \<open>simp_all add: hash_ext_refl\<close>)
  next
    case (Suc n)
    from Suc.prems obtain y s1 ys_tail where
      head:
        "Some (y, s1) \<in>
          set_dist (execute protocol_absorb_read s)"
      and tail:
        "Some (ys_tail, t) \<in>
          set_dist (execute (ntimes protocol_absorb_read n) s1)"
      and ys_eq: "ys = y # ys_tail"
      by (auto elim!: set_dist_bindE)
    from protocol_absorb_read_outcome_with_lookup_chain[OF head]
    obtain rest1 where
      transcript_s: "PTranscript s = y # rest1"
      and transcript_s1: "PTranscript s1 = rest1"
      and head_chain_s1:
        "ro_absorb_lookup_chain s1 (PState s) [y] (PState s1)"
      and ext_s_s1: "s \<le> s1"
      and counter_s1: "PQueryCounter s1 = PQueryCounter s"
      .
    from Suc.IH[OF tail]
    obtain rest where
      length_tail: "length ys_tail = n"
      and transcript_tail: "PTranscript s1 = ys_tail @ rest"
      and transcript_t: "PTranscript t = rest"
      and tail_chain:
        "ro_absorb_lookup_chain t (PState s1) ys_tail (PState t)"
      and ext_s1_t: "s1 \<le> t"
      and counter_t: "PQueryCounter t = PQueryCounter s1"
      by blast
    have head_chain_t:
      "ro_absorb_lookup_chain t (PState s) [y] (PState s1)"
      by (rule ro_absorb_lookup_chain_mono[OF head_chain_s1 ext_s1_t])
    have chain_append:
      "ro_absorb_lookup_chain t (PState s) ([y] @ ys_tail) (PState t)"
      by (rule ro_absorb_lookup_chain_append[OF head_chain_t tail_chain])
    have chain:
      "ro_absorb_lookup_chain t (PState s) ys (PState t)"
      using chain_append ys_eq by simp
    have transcript:
      "PTranscript s = ys @ rest"
      using transcript_s transcript_s1 transcript_tail ys_eq by simp
    have ext_s_t: "s \<le> t"
      by (rule hash_ext_trans[OF ext_s_s1 ext_s1_t])
    have counter: "PQueryCounter t = PQueryCounter s"
      using counter_t counter_s1 by simp
    show ?case
      by (intro exI[of _ rest] conjI)
        (use length_tail transcript transcript_t chain ext_s_t counter
          ys_eq in simp_all)
  qed
  then obtain rest where
    "length ys = n"
    "PTranscript s = ys @ rest"
    "PTranscript t = rest"
    "ro_absorb_lookup_chain t (PState s) ys (PState t)"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
    by blast
  then show ?thesis
    by (rule that)
qed

lemma ro_check_authentication_path_hash_extends:
  assumes outcome:
    "Some (hh, t) \<in>
      set_dist (execute (check_authentication_path len i v path) s)"
  shows "s \<le> t"
  using outcome
  unfolding check_authentication_path_def protocol_check_authentication_path_def
proof (induction path arbitrary: len i v s hh t)
  case Nil
  then have hash_step:
    "Some (hh, t) \<in> set_dist (execute (hash (MerkleLeaf v)) s)"
    by simp
  show ?case
    by (rule hash_outcome(1)[OF hash_step])
next
  case (Cons a path)
  show ?case
  proof (cases "i < len div 2")
    case True
    from Cons.prems obtain x u where
      rec:
        "Some (x, u) \<in>
          set_dist (execute
            (protocol_merkle.check_authentication_path
              (len div 2) i (MerkleLeaf v) path) s)"
      and hash:
        "Some (hh, t) \<in> set_dist (execute (hash (MerkleNode x a)) u)"
      using True by (auto elim!: set_dist_bindE)
    have "s \<le> u"
      by (rule Cons.IH[OF rec])
    moreover have "u \<le> t"
      using hash_outcome(1)[OF hash] .
    ultimately show ?thesis
      by (rule hash_ext_trans)
  next
    case False
    from Cons.prems obtain x u where
      rec:
        "Some (x, u) \<in>
          set_dist (execute
            (protocol_merkle.check_authentication_path
              (len div 2) (i - len div 2) (MerkleLeaf v) path) s)"
      and hash:
        "Some (hh, t) \<in> set_dist (execute (hash (MerkleNode a x)) u)"
      using False by (auto elim!: set_dist_bindE)
    have "s \<le> u"
      by (rule Cons.IH[OF rec])
    moreover have "u \<le> t"
      using hash_outcome(1)[OF hash] .
    ultimately show ?thesis
      by (rule hash_ext_trans)
  qed
qed

lemma ro_query_decommitment_step_outcome_with_lookup_chain:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some (qh, t) \<in>
      set_dist (execute (ro_query_decommitment_step fr i) s)"
  obtains path chunk where
    "length path = floor_log (scale * clength)"
    "chunk = [qh] @ path"
    "PTranscript s = chunk @ PTranscript t"
    "ro_absorb_lookup_chain t (PState s) chunk (PState t)"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
proof -
  let ?len = "scale * clength"
  from outcome obtain s1 path s2 ap s3 s4 where
    read_qh:
      "Some (qh, s1) \<in> set_dist (execute protocol_absorb_read s)"
    and read_path:
      "Some (path, s2) \<in>
        set_dist (execute (ntimes protocol_absorb_read (floor_log ?len)) s1)"
    and check:
      "Some (ap, s3) \<in>
        set_dist (execute (check_authentication_path ?len i qh path) s2)"
    and assert_ap: "Some ((), s4) \<in> set_dist (execute (assert (ap = fr)) s3)"
    and ret_qh: "Some (qh, t) \<in> set_dist (execute (return qh) s4)"
    unfolding ro_query_decommitment_step_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  from protocol_absorb_read_outcome_with_lookup_chain[OF read_qh]
  obtain rest1 where
    transcript_s: "PTranscript s = qh # rest1"
    and transcript_s1: "PTranscript s1 = rest1"
    and head_chain_s1:
      "ro_absorb_lookup_chain s1 (PState s) [qh] (PState s1)"
    and ext_s_s1: "s \<le> s1"
    and counter_s1: "PQueryCounter s1 = PQueryCounter s"
    .
  from ntimes_protocol_absorb_read_outcome_with_lookup_chain[OF read_path]
  obtain rest2 where
    path_len: "length path = floor_log ?len"
    and transcript_path: "PTranscript s1 = path @ rest2"
    and transcript_s2: "PTranscript s2 = rest2"
    and path_chain_s2:
      "ro_absorb_lookup_chain s2 (PState s1) path (PState s2)"
    and ext_s1_s2: "s1 \<le> s2"
    and counter_s2: "PQueryCounter s2 = PQueryCounter s1"
    .
  have ext_s2_s3: "s2 \<le> s3"
    by (rule ro_check_authentication_path_hash_extends[OF check])
  have state_s3: "PState s3 = PState s2"
    using check_authentication_path_preserves_channel(1)[OF check] .
  have transcript_s3: "PTranscript s3 = PTranscript s2"
    using check_authentication_path_preserves_channel(2)[OF check] .
  have counter_s3: "PQueryCounter s3 = PQueryCounter s2"
    using check_authentication_path_preserves_channel(6)[OF check] .
  have ap_eq: "ap = fr"
    using assert_ap unfolding assert_def
    by (cases "ap = fr") (auto simp: throw_no_outcome)
  have s4_eq: "s4 = s3"
    using assert_ap ap_eq unfolding assert_def by simp
  have t_eq: "t = s4"
    using ret_qh by simp
  have ext_s2_t: "s2 \<le> t"
    using ext_s2_s3 s4_eq t_eq by simp
  have ext_s1_t: "s1 \<le> t"
    using ext_s1_s2 ext_s2_t by (rule hash_ext_trans)
  have ext_s_t: "s \<le> t"
    using ext_s_s1 ext_s1_t by (rule hash_ext_trans)
  have state_t: "PState t = PState s2"
    using state_s3 s4_eq t_eq by simp
  have transcript_t: "PTranscript t = PTranscript s2"
    using transcript_s3 s4_eq t_eq by simp
  have counter_t: "PQueryCounter t = PQueryCounter s"
    using counter_s1 counter_s2 counter_s3 s4_eq t_eq by simp
  have head_chain_t:
    "ro_absorb_lookup_chain t (PState s) [qh] (PState s1)"
    by (rule ro_absorb_lookup_chain_mono[OF head_chain_s1 ext_s1_t])
  have path_chain_t:
    "ro_absorb_lookup_chain t (PState s1) path (PState t)"
    using ro_absorb_lookup_chain_mono[OF path_chain_s2 ext_s2_t] state_t
    by simp
  have chain:
    "ro_absorb_lookup_chain t (PState s) ([qh] @ path) (PState t)"
    by (rule ro_absorb_lookup_chain_append[OF head_chain_t path_chain_t])
  have transcript:
    "PTranscript s = ([qh] @ path) @ PTranscript t"
    using transcript_s transcript_s1 transcript_path transcript_s2 transcript_t
    by simp
  show ?thesis
    by (rule that[of path "[qh] @ path"])
      (use path_len transcript chain ext_s_t counter_t in simp_all)
qed

lemma mmap_ro_query_decommitment_steps_outcome_with_lookup_chain:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some (leaves, t) \<in>
      set_dist (execute
        (mmap (map (ro_query_decommitment_step fr) idxs)) s)"
  obtains paths chunk where
    "length leaves = length idxs"
    "length paths = length idxs"
    "chunk = List.concat (map (\<lambda>(leaf, path). [leaf] @ path) (zip leaves paths))"
    "\<forall>path \<in> set paths. length path = floor_log (scale * clength)"
    "PTranscript s = chunk @ PTranscript t"
    "ro_absorb_lookup_chain t (PState s) chunk (PState t)"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
proof -
  have result:
    "\<exists>paths chunk.
      length leaves = length idxs \<and>
      length paths = length idxs \<and>
      chunk = List.concat (map (\<lambda>(leaf, path). [leaf] @ path) (zip leaves paths)) \<and>
      (\<forall>path \<in> set paths. length path = floor_log (scale * clength)) \<and>
      PTranscript s = chunk @ PTranscript t \<and>
      ro_absorb_lookup_chain t (PState s) chunk (PState t) \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s"
    using outcome
  proof (induction idxs arbitrary: s leaves t)
    case Nil
    then show ?case
      by (intro exI[of _ "[]"] conjI)
        (simp_all add: hash_ext_refl)
  next
    case (Cons i idxs)
    from Cons.prems obtain leaf leaves' s1 where
      head:
        "Some (leaf, s1) \<in>
          set_dist (execute (ro_query_decommitment_step fr i) s)"
      and tail:
        "Some (leaves', t) \<in>
          set_dist (execute
            (mmap (map (ro_query_decommitment_step fr) idxs)) s1)"
      and leaves_eq: "leaves = leaf # leaves'"
      by (auto elim!: set_dist_bindE)
    from ro_query_decommitment_step_outcome_with_lookup_chain[OF head]
    obtain path head_chunk where
      path_len: "length path = floor_log (scale * clength)"
      and head_chunk_eq: "head_chunk = [leaf] @ path"
      and transcript_s: "PTranscript s = head_chunk @ PTranscript s1"
      and head_chain_s1:
        "ro_absorb_lookup_chain s1 (PState s) head_chunk (PState s1)"
      and ext_s_s1: "s \<le> s1"
      and counter_s1: "PQueryCounter s1 = PQueryCounter s"
      .
    from Cons.IH[OF tail]
    obtain paths tail_chunk where
      len_leaves': "length leaves' = length idxs"
      and len_paths: "length paths = length idxs"
      and tail_chunk_eq:
        "tail_chunk =
          List.concat (map (\<lambda>(leaf, path). [leaf] @ path) (zip leaves' paths))"
      and paths_len:
        "\<forall>path \<in> set paths. length path = floor_log (scale * clength)"
      and transcript_s1: "PTranscript s1 = tail_chunk @ PTranscript t"
      and tail_chain:
        "ro_absorb_lookup_chain t (PState s1) tail_chunk (PState t)"
      and ext_s1_t: "s1 \<le> t"
      and counter_t: "PQueryCounter t = PQueryCounter s1"
      by blast
    let ?paths = "path # paths"
    let ?chunk = "head_chunk @ tail_chunk"
    have head_chain_t:
      "ro_absorb_lookup_chain t (PState s) head_chunk (PState s1)"
      by (rule ro_absorb_lookup_chain_mono[OF head_chain_s1 ext_s1_t])
    have chain:
      "ro_absorb_lookup_chain t (PState s) ?chunk (PState t)"
      by (rule ro_absorb_lookup_chain_append[OF head_chain_t tail_chain])
    have transcript: "PTranscript s = ?chunk @ PTranscript t"
      using transcript_s transcript_s1 by simp
    have ext_s_t: "s \<le> t"
      using ext_s_s1 ext_s1_t by (rule hash_ext_trans)
    have counter: "PQueryCounter t = PQueryCounter s"
      using counter_t counter_s1 by simp
    show ?case
      apply (intro exI[of _ ?paths] exI[of _ ?chunk] conjI)
      using leaves_eq path_len head_chunk_eq len_leaves' len_paths tail_chunk_eq
        paths_len transcript chain ext_s_t counter
      by simp_all
  qed
  then obtain paths chunk where
    "length leaves = length idxs"
    "length paths = length idxs"
    "chunk = List.concat (map (\<lambda>(leaf, path). [leaf] @ path) (zip leaves paths))"
    "\<forall>path \<in> set paths. length path = floor_log (scale * clength)"
    "PTranscript s = chunk @ PTranscript t"
    "ro_absorb_lookup_chain t (PState s) chunk (PState t)"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
    by blast
  then show ?thesis
    by (rule that)
qed

lemma ro_check_decommit_on_query_outcome_with_lookup_chain:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some (leaves, t) \<in>
      set_dist (execute (mmap (ro_check_decommit_on_query fr idx)) s)"
  obtains paths chunk where
    "query_decommitment_transcript idx leaves paths chunk"
    "PTranscript s = chunk @ PTranscript t"
    "ro_absorb_lookup_chain t (PState s) chunk (PState t)"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
proof -
  have map_eq:
    "ro_check_decommit_on_query fr idx =
      map (ro_query_decommitment_step fr) (powers_scaled idx)"
    unfolding ro_check_decommit_on_query_def by simp
  from mmap_ro_query_decommitment_steps_outcome_with_lookup_chain
      [OF outcome[unfolded map_eq]]
  obtain paths chunk where
    len_leaves: "length leaves = length (powers_scaled idx)"
    and len_paths: "length paths = length (powers_scaled idx)"
    and chunk_eq:
      "chunk = List.concat
        (map (\<lambda>(leaf, path). [leaf] @ path) (zip leaves paths))"
    and paths_len:
      "\<forall>path \<in> set paths. length path = floor_log (scale * clength)"
    and transcript: "PTranscript s = chunk @ PTranscript t"
    and chain:
      "ro_absorb_lookup_chain t (PState s) chunk (PState t)"
    and ext: "s \<le> t"
    and counter: "PQueryCounter t = PQueryCounter s"
    .
  have qtr: "query_decommitment_transcript idx leaves paths chunk"
    using len_leaves len_paths chunk_eq paths_len
    unfolding query_decommitment_transcript_def
    by (simp add: mult.commute case_prod_unfold)
  show ?thesis
    by (rule that[OF qtr transcript chain ext counter])
qed

lemma ro_fri_layer_opening_step_outcome_with_lookup_chain:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some (out, t) \<in>
      set_dist (execute (ro_fri_layer_opening_step (b, f) (i, x, len, pw)) s)"
  obtains xp xp_path xn xn_path folded chunk where
    "out = (i mod (len div 2), folded, len div 2, pw + pw)"
    "xp = x"
    "folded = fri_fold_value b xp xn
      (fri_fold_denominator ((h ^ i) * shift) pw)"    "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    "PTranscript s = chunk @ PTranscript t"
    "ro_absorb_lookup_chain t (PState s) chunk (PState t)"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
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
        set_dist (execute (check_authentication_path len i xp xp_path) s5)"
    and assert_ap1:
      "Some ((), s7) \<in> set_dist (execute (assert (ap1 = f)) s6)"
    and check2:
      "Some (ap2, s8) \<in>
        set_dist (execute
          (check_authentication_path len ((i + len div 2) mod len) xn
            xn_path) s7)"
    and assert_ap2:
      "Some ((), s9) \<in> set_dist (execute (assert (ap2 = f)) s8)"
    and ret:
      "Some (out, t) \<in>
        set_dist
          (execute
            (return (i mod (len div 2),
              (xp + xn) div 2 +
                b * ((xp - xn) div (2 * ((h ^ i) * shift) ^ pw)),
              len div 2, pw + pw)) s9)"
    unfolding ro_fri_layer_opening_step_def fri_layer_opening_finish_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  from protocol_absorb_read_outcome_with_lookup_chain[OF read_xp]
  obtain rest1 where
    transcript_s: "PTranscript s = xp # rest1"
    and transcript_s1: "PTranscript s1 = rest1"
    and xp_chain_s1:
      "ro_absorb_lookup_chain s1 (PState s) [xp] (PState s1)"
    and ext_s_s1: "s \<le> s1"
    and counter_s1: "PQueryCounter s1 = PQueryCounter s"
    .
  from ntimes_protocol_absorb_read_outcome_with_lookup_chain[OF read_xp_path]
  obtain rest2 where
    xp_path_len: "length xp_path = floor_log len"
    and transcript_xp_path: "PTranscript s1 = xp_path @ rest2"
    and transcript_s2: "PTranscript s2 = rest2"
    and xp_path_chain_s2:
      "ro_absorb_lookup_chain s2 (PState s1) xp_path (PState s2)"
    and ext_s1_s2: "s1 \<le> s2"
    and counter_s2: "PQueryCounter s2 = PQueryCounter s1"
    .
  from protocol_absorb_read_outcome_with_lookup_chain[OF read_xn]
  obtain rest3 where
    transcript_s2_xn: "PTranscript s2 = xn # rest3"
    and transcript_s3: "PTranscript s3 = rest3"
    and xn_chain_s3:
      "ro_absorb_lookup_chain s3 (PState s2) [xn] (PState s3)"
    and ext_s2_s3: "s2 \<le> s3"
    and counter_s3: "PQueryCounter s3 = PQueryCounter s2"
    .
  from ntimes_protocol_absorb_read_outcome_with_lookup_chain[OF read_xn_path]
  obtain rest4 where
    xn_path_len: "length xn_path = floor_log len"
    and transcript_xn_path: "PTranscript s3 = xn_path @ rest4"
    and transcript_s4: "PTranscript s4 = rest4"
    and xn_path_chain_s4:
      "ro_absorb_lookup_chain s4 (PState s3) xn_path (PState s4)"
    and ext_s3_s4: "s3 \<le> s4"
    and counter_s4: "PQueryCounter s4 = PQueryCounter s3"
    .
  have xp_eq: "xp = x"
    using assert_xp unfolding assert_def
    by (cases "xp = x") (auto simp: throw_no_outcome)
  have s5_eq: "s5 = s4"
    using assert_xp xp_eq unfolding assert_def by simp
  have ext_s5_s6: "s5 \<le> s6"
    by (rule ro_check_authentication_path_hash_extends[OF check1])
  have state_s6: "PState s6 = PState s5"
    using check_authentication_path_preserves_channel(1)[OF check1] .
  have transcript_s6: "PTranscript s6 = PTranscript s5"
    using check_authentication_path_preserves_channel(2)[OF check1] .
  have counter_s6: "PQueryCounter s6 = PQueryCounter s5"
    using check_authentication_path_preserves_channel(6)[OF check1] .
  have ap1_eq: "ap1 = f"
    using assert_ap1 unfolding assert_def
    by (cases "ap1 = f") (auto simp: throw_no_outcome)
  have s7_eq: "s7 = s6"
    using assert_ap1 ap1_eq unfolding assert_def by simp
  have ext_s7_s8: "s7 \<le> s8"
    by (rule ro_check_authentication_path_hash_extends[OF check2])
  have state_s8: "PState s8 = PState s7"
    using check_authentication_path_preserves_channel(1)[OF check2] .
  have transcript_s8: "PTranscript s8 = PTranscript s7"
    using check_authentication_path_preserves_channel(2)[OF check2] .
  have counter_s8: "PQueryCounter s8 = PQueryCounter s7"
    using check_authentication_path_preserves_channel(6)[OF check2] .
  have ap2_eq: "ap2 = f"
    using assert_ap2 unfolding assert_def
    by (cases "ap2 = f") (auto simp: throw_no_outcome)
  have s9_eq: "s9 = s8"
    using assert_ap2 ap2_eq unfolding assert_def by simp
  let ?x' =
    "(xp + xn) div 2 +
      b * ((xp - xn) div (2 * ((h ^ i) * shift) ^ pw))"
  have out_t: "out = (i mod (len div 2), ?x', len div 2, pw + pw) \<and> t = s9"
    using ret by simp
  have x'_fold:
    "?x' = fri_fold_value b xp xn
      (fri_fold_denominator ((h ^ i) * shift) pw)"
    unfolding fri_fold_value_def fri_fold_denominator_def by simp
  have ext_s4_s6: "s4 \<le> s6"
    using ext_s5_s6 s5_eq by simp
  have ext_s6_s8: "s6 \<le> s8"
    using ext_s7_s8 s7_eq by simp
  have ext_s4_s8: "s4 \<le> s8"
    using ext_s4_s6 ext_s6_s8 by (rule hash_ext_trans)
  have ext_s4_t: "s4 \<le> t"
    using ext_s4_s8 s9_eq out_t by simp
  have ext_s3_t: "s3 \<le> t"
    using ext_s3_s4 ext_s4_t by (rule hash_ext_trans)
  have ext_s2_t: "s2 \<le> t"
    using ext_s2_s3 ext_s3_t by (rule hash_ext_trans)
  have ext_s1_t: "s1 \<le> t"
    using ext_s1_s2 ext_s2_t by (rule hash_ext_trans)
  have ext_s_t: "s \<le> t"
    using ext_s_s1 ext_s1_t by (rule hash_ext_trans)
  have state_t: "PState t = PState s4"
    using state_s6 state_s8 s5_eq s7_eq s9_eq out_t by simp
  have transcript_t: "PTranscript t = PTranscript s4"
    using transcript_s6 transcript_s8 s5_eq s7_eq s9_eq out_t by simp
  have counter_t: "PQueryCounter t = PQueryCounter s"
    using counter_s1 counter_s2 counter_s3 counter_s4 counter_s6 counter_s8
      s5_eq s7_eq s9_eq out_t
    by simp
  have xp_chain_t:
    "ro_absorb_lookup_chain t (PState s) [xp] (PState s1)"
    by (rule ro_absorb_lookup_chain_mono[OF xp_chain_s1 ext_s1_t])
  have xp_path_chain_t:
    "ro_absorb_lookup_chain t (PState s1) xp_path (PState s2)"
    by (rule ro_absorb_lookup_chain_mono[OF xp_path_chain_s2 ext_s2_t])
  have xn_chain_t:
    "ro_absorb_lookup_chain t (PState s2) [xn] (PState s3)"
    by (rule ro_absorb_lookup_chain_mono[OF xn_chain_s3 ext_s3_t])
  have xn_path_chain_t:
    "ro_absorb_lookup_chain t (PState s3) xn_path (PState t)"
    using ro_absorb_lookup_chain_mono[OF xn_path_chain_s4 ext_s4_t] state_t
    by simp
  have chain_xp:
    "ro_absorb_lookup_chain t (PState s) ([xp] @ xp_path) (PState s2)"
    by (rule ro_absorb_lookup_chain_append[OF xp_chain_t xp_path_chain_t])
  have chain_xn:
    "ro_absorb_lookup_chain t (PState s2) ([xn] @ xn_path) (PState t)"
    by (rule ro_absorb_lookup_chain_append[OF xn_chain_t xn_path_chain_t])
  have chain:
    "ro_absorb_lookup_chain t (PState s)
      (([xp] @ xp_path) @ ([xn] @ xn_path)) (PState t)"
    by (rule ro_absorb_lookup_chain_append[OF chain_xp chain_xn])
  let ?chunk = "[xp] @ xp_path @ [xn] @ xn_path"
  have chunk_shape:
    "fri_layer_opening_chunk len xp xp_path xn xn_path ?chunk"
    using xp_path_len xn_path_len unfolding fri_layer_opening_chunk_def by simp
  have transcript:
    "PTranscript s = ?chunk @ PTranscript t"
    using transcript_s transcript_s1 transcript_xp_path transcript_s2
      transcript_s2_xn transcript_s3 transcript_xn_path transcript_s4
      transcript_t
    by simp
  have chain_chunk:
    "ro_absorb_lookup_chain t (PState s) ?chunk (PState t)"
    using chain by simp
  show ?thesis
    apply (rule that)
    using out_t xp_eq x'_fold chunk_shape transcript chain_chunk ext_s_t counter_t
    by auto
qed

lemma ro_fri_layer_opening_step_outcome_extends_counter:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some (out, t) \<in>
      set_dist (execute (ro_fri_layer_opening_step bf st) s)"
  shows "s \<le> t \<and> PQueryCounter t = PQueryCounter s"
proof -
  obtain b f where bf_eq: "bf = (b, f)"
    by (cases bf)
  obtain i x len pw where st_eq: "st = (i, x, len, pw)"
    by (cases st)
  from ro_fri_layer_opening_step_outcome_with_lookup_chain
      [OF outcome[unfolded bf_eq st_eq]]
  show ?thesis
    by blast
qed

lemma mfold_ro_fri_layer_opening_steps_outcome_extends_counter:
  fixes st :: "nat \<times> 'f \<times> nat \<times> nat"
    and s t :: "'f protocol_channel"
  assumes outcome:
    "Some (out, t) \<in>
      set_dist
        (execute (mfold st (map ro_fri_layer_opening_step fl)) s)"
  shows "s \<le> t \<and> PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction fl arbitrary: st s out t)
  case Nil
  then have ret: "out = st \<and> t = s"
    by simp
  then show ?case
    using hash_ext_refl by simp
next
  case (Cons bf fl)
  then obtain st' u where
    head:
      "Some (st', u) \<in>
        set_dist (execute (ro_fri_layer_opening_step bf st) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist
          (execute (mfold st' (map ro_fri_layer_opening_step fl)) u)"
    by (auto elim!: set_dist_bindE)
  have head_props: "s \<le> u \<and> PQueryCounter u = PQueryCounter s"
    by (rule ro_fri_layer_opening_step_outcome_extends_counter[OF head])
  have tail_props: "u \<le> t \<and> PQueryCounter t = PQueryCounter u"
    by (rule Cons.IH[OF tail])
  have "s \<le> t"
    using head_props tail_props by (meson hash_ext_trans)
  moreover have "PQueryCounter t = PQueryCounter s"
    using head_props tail_props by simp
  ultimately show ?case
    by simp
qed

lemma ro_receive_query_commits_outcome_extends_counter:
  fixes st :: "nat \<times> 'f \<times> nat \<times> nat"
    and s t :: "'f protocol_channel"
  assumes outcome:
    "Some (out, t) \<in>
      set_dist (execute (mfold st (ro_receive_query_commits fl)) s)"
  shows "s \<le> t \<and> PQueryCounter t = PQueryCounter s"
  using outcome
  unfolding ro_receive_query_commits_def
  by (rule mfold_ro_fri_layer_opening_steps_outcome_extends_counter)

lemma mfold_ro_fri_layer_opening_steps_outcome_with_lookup_chain_exists:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some (out, t) \<in>
      set_dist
        (execute
          (mfold (i, x, len, pw) (map ro_fri_layer_opening_step bfs)) s)"
  shows
    "\<exists>layer_chunks chunk.
      fri_layers_transcript (length bfs) len layer_chunks chunk \<and>
      PTranscript s = chunk @ PTranscript t \<and>
      ro_absorb_lookup_chain t (PState s) chunk (PState t) \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction bfs arbitrary: i x len pw s out t)
  case Nil
  then show ?case
    by (intro exI[of _ "[]"])
      (simp add: fri_layers_transcript_def hash_ext_refl)
next
  case (Cons bf bfs)
  obtain b f where bf_eq: "bf = (b, f)"
    by (cases bf)
  from Cons.prems obtain out1 s1 where
    head:
      "Some (out1, s1) \<in>
        set_dist
          (execute (ro_fri_layer_opening_step bf (i, x, len, pw)) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist
          (execute (mfold out1 (map ro_fri_layer_opening_step bfs)) s1)"
    by (auto elim!: set_dist_bindE)
  from ro_fri_layer_opening_step_outcome_with_lookup_chain
      [OF head[unfolded bf_eq]]
  obtain xp xp_path xn xn_path folded head_chunk where
    out1_eq:
      "out1 = (i mod (len div 2), folded, len div 2, pw + pw)"
    and xp_eq: "xp = x"
    and folded_eq:
      "folded = fri_fold_value b xp xn
        (fri_fold_denominator ((h ^ i) * shift) pw)"
    and head_shape:
      "fri_layer_opening_chunk len xp xp_path xn xn_path head_chunk"
    and head_transcript:
      "PTranscript s = head_chunk @ PTranscript s1"
    and head_chain:
      "ro_absorb_lookup_chain s1 (PState s) head_chunk (PState s1)"
    and head_ext: "s \<le> s1"
    and head_counter: "PQueryCounter s1 = PQueryCounter s"
    .
  from Cons.IH[OF tail[unfolded out1_eq]] obtain layer_chunks tail_chunk where
    tail_layers:
      "fri_layers_transcript (length bfs) (len div 2) layer_chunks tail_chunk"
    and tail_transcript:
      "PTranscript s1 = tail_chunk @ PTranscript t"
    and tail_chain:
      "ro_absorb_lookup_chain t (PState s1) tail_chunk (PState t)"
    and tail_ext: "s1 \<le> t"
    and tail_counter: "PQueryCounter t = PQueryCounter s1"
    by blast
  let ?chunks = "head_chunk # layer_chunks"
  let ?chunk = "head_chunk @ tail_chunk"
  have layers:
    "fri_layers_transcript (length (bf # bfs)) len ?chunks ?chunk"
    using head_shape tail_layers
    unfolding fri_layers_transcript_def
    by auto
  have head_chain_t:
    "ro_absorb_lookup_chain t (PState s) head_chunk (PState s1)"
    by (rule ro_absorb_lookup_chain_mono[OF head_chain tail_ext])
  have chain:
    "ro_absorb_lookup_chain t (PState s) ?chunk (PState t)"
    by (rule ro_absorb_lookup_chain_append[OF head_chain_t tail_chain])
  have ext: "s \<le> t"
    by (rule hash_ext_trans[OF head_ext tail_ext])
  have transcript: "PTranscript s = ?chunk @ PTranscript t"
    using head_transcript tail_transcript by simp
  have counter: "PQueryCounter t = PQueryCounter s"
    using head_counter tail_counter by simp
  show ?case
    by (intro exI[of _ ?chunks] exI[of _ ?chunk])
      (use layers transcript chain ext counter in simp)
qed

lemma mfold_ro_fri_layer_opening_steps_outcome_with_lookup_chain:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some (out, t) \<in>
      set_dist
        (execute
          (mfold (i, x, len, pw) (map ro_fri_layer_opening_step bfs)) s)"
  obtains layer_chunks chunk where
    "fri_layers_transcript (length bfs) len layer_chunks chunk"
    "PTranscript s = chunk @ PTranscript t"
    "ro_absorb_lookup_chain t (PState s) chunk (PState t)"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
proof -
  from mfold_ro_fri_layer_opening_steps_outcome_with_lookup_chain_exists
      [OF outcome]
  obtain layer_chunks chunk where
    layers: "fri_layers_transcript (length bfs) len layer_chunks chunk"
    and transcript: "PTranscript s = chunk @ PTranscript t"
    and chain: "ro_absorb_lookup_chain t (PState s) chunk (PState t)"
    and ext: "s \<le> t"
    and counter: "PQueryCounter t = PQueryCounter s"
    by blast
  show ?thesis
    by (rule that[OF layers transcript chain ext counter])
qed

lemma ro_receive_query_commits_layers_outcome_with_lookup_chain:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some (out, t) \<in>
      set_dist (execute (mfold (i, x, len, pw) (ro_receive_query_commits bfs)) s)"
  obtains layer_chunks chunk where
    "fri_layers_transcript (length bfs) len layer_chunks chunk"
    "PTranscript s = chunk @ PTranscript t"
    "ro_absorb_lookup_chain t (PState s) chunk (PState t)"
    "s \<le> t"
    "PQueryCounter t = PQueryCounter s"
  using outcome
  unfolding ro_receive_query_commits_def
  by (rule mfold_ro_fri_layer_opening_steps_outcome_with_lookup_chain)

lemma ro_verifier_query_round_program_outcome_extends_counter:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some ((), t) \<in>
      set_dist
        (execute (ro_verifier_query_round_program fr f_fl f_final as fl final) s)"
  shows "s \<le> t \<and> PQueryCounter t = Suc (PQueryCounter s)"
proof -
  from outcome obtain raw s1 fv s2 f_i f_x f_len f_pow s3 s4
      i x len pw s5 where
    challenge:
      "Some (raw, s1) \<in> set_dist (execute receive_query_index_challenge s)"
    and decommit:
      "Some (fv, s2) \<in>
        set_dist
          (execute
            (mmap (ro_check_decommit_on_query fr (index (to_nat raw)))) s1)"
    and trace_fri:
      "Some ((f_i, f_x, f_len, f_pow), s3) \<in>
        set_dist
          (execute
            (mfold (index (to_nat raw), hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl)) s2)"
    and trace_assert:
      "Some ((), s4) \<in> set_dist (execute (assert (f_x = f_final)) s3)"
    and composition_fri:
      "Some ((i, x, len, pw), s5) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat raw), cp_eval as fv (h ^ index (to_nat raw) * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl)) s4)"
    and composition_assert:
      "Some ((), t) \<in> set_dist (execute (assert (x = final)) s5)"
    unfolding ro_verifier_query_round_program_def
    by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)
  have challenge_props:
    "s \<le> s1 \<and> PQueryCounter s1 = Suc (PQueryCounter s)"
    using receive_query_index_challenge_outcome[OF challenge]
      receive_query_index_challenge_counter_outcome[OF challenge]
    by simp
  have decommit_props:
    "s1 \<le> s2 \<and> PQueryCounter s2 = PQueryCounter s1"
    using ro_check_decommit_on_query_outcome_with_lookup_chain[OF decommit]
    by blast
  have trace_props:
    "s2 \<le> s3 \<and> PQueryCounter s3 = PQueryCounter s2"
    by (rule ro_receive_query_commits_outcome_extends_counter[OF trace_fri])
  have s4_eq: "s4 = s3"
    using trace_assert unfolding assert_def
    by (cases "f_x = f_final") (auto simp: throw_no_outcome)
  have composition_props:
    "s4 \<le> s5 \<and> PQueryCounter s5 = PQueryCounter s4"
    by (rule ro_receive_query_commits_outcome_extends_counter[OF composition_fri])
  have t_eq: "t = s5"
    using composition_assert unfolding assert_def
    by (cases "x = final") (auto simp: throw_no_outcome)
  have "s \<le> t"
    using challenge_props decommit_props trace_props composition_props s4_eq t_eq
    by (meson hash_ext_trans)
  moreover have "PQueryCounter t = Suc (PQueryCounter s)"
    using challenge_props decommit_props trace_props composition_props s4_eq t_eq
    by simp
  ultimately show ?thesis
    by simp
qed

lemma ro_verifier_query_round_program_outcome_with_lookup_chain:
  fixes s t :: "'f protocol_channel"
  assumes outcome:
    "Some ((), t) \<in>
      set_dist
        (execute (ro_verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw s1 chunk where
    "Some (raw, s1) \<in> set_dist (execute receive_query_index_challenge s)"
    "PState s1 = PState s"
    "PTranscript s1 = PTranscript s"
    "s \<le> s1"
    "PQueryCounter s1 = Suc (PQueryCounter s)"
    "verifier_query_round_chunk (index (to_nat raw)) (map snd f_fl) (map snd fl) chunk"
    "PTranscript s = chunk @ PTranscript t"
    "ro_absorb_lookup_chain t (PState s) chunk (PState t)"
    "s \<le> t"
    "PQueryCounter t = Suc (PQueryCounter s)"
proof -
  from outcome obtain raw s1 fv s2 f_i f_x f_len f_pow s3 s4
      i x len pw s5 where
    challenge:
      "Some (raw, s1) \<in> set_dist (execute receive_query_index_challenge s)"
    and decommit:
      "Some (fv, s2) \<in>
        set_dist
          (execute
            (mmap (ro_check_decommit_on_query fr (index (to_nat raw)))) s1)"
    and trace_fri:
      "Some ((f_i, f_x, f_len, f_pow), s3) \<in>
        set_dist
          (execute
            (mfold (index (to_nat raw), hd fv, clength * scale, 1)
              (ro_receive_query_commits f_fl)) s2)"
    and trace_assert:
      "Some ((), s4) \<in> set_dist (execute (assert (f_x = f_final)) s3)"
    and composition_fri:
      "Some ((i, x, len, pw), s5) \<in>
        set_dist
          (execute
            (mfold
              (index (to_nat raw), cp_eval as fv (h ^ index (to_nat raw) * shift),
                clength * scale, 1)
              (ro_receive_query_commits fl)) s4)"
    and composition_assert:
      "Some ((), t) \<in> set_dist (execute (assert (x = final)) s5)"
    unfolding ro_verifier_query_round_program_def
    by (auto simp: Let_def elim!: set_dist_bindE split: prod.splits)
  have challenge_ext: "s \<le> s1"
    and challenge_state: "PState s1 = PState s"
    and challenge_transcript: "PTranscript s1 = PTranscript s"
    using receive_query_index_challenge_outcome[OF challenge]
    by simp_all
  have challenge_counter: "PQueryCounter s1 = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF challenge]
    by simp
  from ro_check_decommit_on_query_outcome_with_lookup_chain[OF decommit]
  obtain paths query_chunk where
    query_shape:
      "query_decommitment_transcript (index (to_nat raw)) fv paths query_chunk"
    and query_transcript:
      "PTranscript s1 = query_chunk @ PTranscript s2"
    and query_chain:
      "ro_absorb_lookup_chain s2 (PState s1) query_chunk (PState s2)"
    and query_ext: "s1 \<le> s2"
    and query_counter: "PQueryCounter s2 = PQueryCounter s1"
    .
  from ro_receive_query_commits_layers_outcome_with_lookup_chain[OF trace_fri]
  obtain trace_layer_chunks trace_chunk where
    trace_layers:
      "fri_layers_transcript (length f_fl) (clength * scale)
        trace_layer_chunks trace_chunk"
    and trace_transcript:
      "PTranscript s2 = trace_chunk @ PTranscript s3"
    and trace_chain:
      "ro_absorb_lookup_chain s3 (PState s2) trace_chunk (PState s3)"
    and trace_ext: "s2 \<le> s3"
    and trace_counter: "PQueryCounter s3 = PQueryCounter s2"
    .
  have s4_eq: "s4 = s3"
    using trace_assert unfolding assert_def
    by (cases "f_x = f_final") (auto simp: throw_no_outcome)
  from ro_receive_query_commits_layers_outcome_with_lookup_chain[OF composition_fri]
  obtain composition_layer_chunks composition_chunk where
    composition_layers:
      "fri_layers_transcript (length fl) (clength * scale)
        composition_layer_chunks composition_chunk"
    and composition_transcript:
      "PTranscript s4 = composition_chunk @ PTranscript s5"
    and composition_chain:
      "ro_absorb_lookup_chain s5 (PState s4) composition_chunk (PState s5)"
    and composition_ext: "s4 \<le> s5"
    and composition_counter: "PQueryCounter s5 = PQueryCounter s4"
    .
  have t_eq: "t = s5"
    using composition_assert unfolding assert_def
    by (cases "x = final") (auto simp: throw_no_outcome)
  let ?chunk = "query_chunk @ trace_chunk @ composition_chunk"
  have chunk_shape:
    "verifier_query_round_chunk (index (to_nat raw)) (map snd f_fl) (map snd fl) ?chunk"
    unfolding verifier_query_round_chunk_def
    apply (rule exI[where x=query_chunk])
    apply (rule exI[where x=trace_chunk])
    apply (rule exI[where x=composition_chunk])
    apply (rule exI[where x=fv])
    apply (rule exI[where x=paths])
    apply (rule exI[where x=trace_layer_chunks])
    apply (rule exI[where x=composition_layer_chunks])
    using query_shape trace_layers composition_layers
    by simp
  have composition_ext_s3_t: "s3 \<le> t"
    using composition_ext s4_eq t_eq by simp
  have trace_ext_s2_t: "s2 \<le> t"
    by (rule hash_ext_trans[OF trace_ext composition_ext_s3_t])
  have query_ext_s1_t: "s1 \<le> t"
    by (rule hash_ext_trans[OF query_ext trace_ext_s2_t])
  have ext: "s \<le> t"
    by (rule hash_ext_trans[OF challenge_ext query_ext_s1_t])
  have query_chain_t:
    "ro_absorb_lookup_chain t (PState s) query_chunk (PState s2)"
  proof -
    have "ro_absorb_lookup_chain t (PState s1) query_chunk (PState s2)"
      by (rule ro_absorb_lookup_chain_mono[OF query_chain trace_ext_s2_t])
    then show ?thesis
      using challenge_state by simp
  qed
  have trace_chain_t:
    "ro_absorb_lookup_chain t (PState s2) trace_chunk (PState s3)"
    by (rule ro_absorb_lookup_chain_mono[OF trace_chain composition_ext_s3_t])
  have composition_chain_t:
    "ro_absorb_lookup_chain t (PState s3) composition_chunk (PState t)"
    using composition_chain s4_eq t_eq by simp
  have query_trace_chain:
    "ro_absorb_lookup_chain t (PState s) (query_chunk @ trace_chunk)
      (PState s3)"
    by (rule ro_absorb_lookup_chain_append[OF query_chain_t trace_chain_t])
  have chain:
    "ro_absorb_lookup_chain t (PState s) ?chunk (PState t)"
    using ro_absorb_lookup_chain_append[OF query_trace_chain composition_chain_t]
    by simp
  have transcript: "PTranscript s = ?chunk @ PTranscript t"
    using challenge_transcript query_transcript trace_transcript
      composition_transcript s4_eq t_eq
    by simp
  have counter: "PQueryCounter t = Suc (PQueryCounter s)"
    using challenge_counter query_counter trace_counter composition_counter
      s4_eq t_eq
    by simp
  show ?thesis
    by (rule that[OF challenge challenge_state challenge_transcript
          challenge_ext challenge_counter chunk_shape transcript chain ext counter])
qed

lemma ro_absorb_lookup_chain_snoc:
  assumes chain:
    "ro_absorb_lookup_chain s start (xs @ [x]) final"
  shows
    "\<exists>mid.
      ro_absorb_lookup_chain s start xs mid \<and>
      fmlookup (HashMap s) (TranscriptAbsorb mid x) = Some final"
  using chain
proof (induction xs arbitrary: start)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then obtain nxt where
    lookup:
      "fmlookup (HashMap s) (TranscriptAbsorb start a) = Some nxt"
    and tail:
      "ro_absorb_lookup_chain s nxt (xs @ [x]) final"
    by auto
  from Cons.IH[OF tail] obtain mid where
    prefix: "ro_absorb_lookup_chain s nxt xs mid"
    and last:
      "fmlookup (HashMap s) (TranscriptAbsorb mid x) = Some final"
    by blast
  have full_prefix: "ro_absorb_lookup_chain s start (a # xs) mid"
    using lookup prefix by auto
  show ?case
    using full_prefix last by blast
qed

lemma ro_absorb_lookup_chain_nonempty_final_in_output_values:
  assumes chain: "ro_absorb_lookup_chain s start xs final"
    and nonempty: "xs \<noteq> []"
  shows "final \<in> hash_map_output_values s"
proof -
  obtain ys y where xs_eq: "xs = ys @ [y]"
    using nonempty by (cases xs rule: rev_cases) auto
  from ro_absorb_lookup_chain_snoc[OF chain[unfolded xs_eq]]
  obtain mid where
    "fmlookup (HashMap s) (TranscriptAbsorb mid y) = Some final"
    by blast
  then show ?thesis
    unfolding hash_map_output_values_def by blast
qed

lemma hash_map_lookup_key_unique_if_no_output_collision:
  assumes clean: "\<not> hash_map_output_collision s"
    and left: "fmlookup (HashMap s) x = Some z"
    and right: "fmlookup (HashMap s) y = Some z"
  shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  then have "hash_map_output_collision s"
    unfolding hash_map_output_collision_def
    using left right by blast
  then show False
    using clean by contradiction
qed

lemma ro_absorb_lookup_chain_injective_if_clean_and_no_initial_target:
  assumes clean: "\<not> hash_map_output_collision s"
    and no_initial_target: "start \<notin> hash_map_output_values s"
    and left: "ro_absorb_lookup_chain s start xs final"
    and right: "ro_absorb_lookup_chain s start ys final"
  shows "xs = ys"
  using left right
proof (induction xs arbitrary: ys final rule: rev_induct)
  case Nil
  have final_eq: "final = start"
    using Nil.prems(1) by simp
  have ys_empty: "ys = []"
  proof (rule ccontr)
    assume ys_nonempty: "ys \<noteq> []"
    have target: "start \<in> hash_map_output_values s"
      by (rule ro_absorb_lookup_chain_nonempty_final_in_output_values[
            OF Nil.prems(2)[unfolded final_eq] ys_nonempty])
    show False
      by (metis no_initial_target target)
  qed
  show ?case
    using ys_empty by simp
next
  case (snoc x xs)
  have ys_nonempty: "ys \<noteq> []"
  proof
    assume ys_empty: "ys = []"
    have final_eq: "final = start"
      using snoc.prems(2) ys_empty by simp
    have left_nonempty: "xs @ [x] \<noteq> []"
      by simp
    have target: "start \<in> hash_map_output_values s"
      by (rule ro_absorb_lookup_chain_nonempty_final_in_output_values[
            OF snoc.prems(1)[unfolded final_eq] left_nonempty])
    show False
      by (metis no_initial_target target)
  qed
  obtain ys' y where ys_eq: "ys = ys' @ [y]"
    using ys_nonempty by (cases ys rule: rev_cases) auto
  from ro_absorb_lookup_chain_snoc[OF snoc.prems(1)]
  obtain mid_left where
    prefix_left: "ro_absorb_lookup_chain s start xs mid_left"
    and lookup_left:
      "fmlookup (HashMap s) (TranscriptAbsorb mid_left x) = Some final"
    by blast
  from ro_absorb_lookup_chain_snoc[
      OF snoc.prems(2)[unfolded ys_eq]]
  obtain mid_right where
    prefix_right: "ro_absorb_lookup_chain s start ys' mid_right"
    and lookup_right:
      "fmlookup (HashMap s) (TranscriptAbsorb mid_right y) = Some final"
    by blast
  have key_eq:
    "TranscriptAbsorb mid_left x = TranscriptAbsorb mid_right y"
    by (rule hash_map_lookup_key_unique_if_no_output_collision[
          OF clean lookup_left lookup_right])
  have mid_eq: "mid_left = mid_right"
    and x_eq: "x = y"
    using key_eq by simp_all
  have prefix_eq: "xs = ys'"
    by (rule snoc.IH[OF prefix_left])
      (use prefix_right mid_eq in simp)
  show ?case
    unfolding ys_eq
    using prefix_eq x_eq by simp
qed


lemma ro_absorb_lookup_chain_functional:
  assumes left: "ro_absorb_lookup_chain s start xs final_left"
    and right: "ro_absorb_lookup_chain s start xs final_right"
  shows "final_left = final_right"
  using left right
proof (induction xs arbitrary: start)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then obtain next_left next_right where
    lookup_left:
      "fmlookup (HashMap s) (TranscriptAbsorb start x) = Some next_left"
    and tail_left:
      "ro_absorb_lookup_chain s next_left xs final_left"
    and lookup_right:
      "fmlookup (HashMap s) (TranscriptAbsorb start x) = Some next_right"
    and tail_right:
      "ro_absorb_lookup_chain s next_right xs final_right"
    by auto
  have next_eq: "next_left = next_right"
    using lookup_left lookup_right by simp
  have tail_right':
    "ro_absorb_lookup_chain s next_left xs final_right"
    using tail_right next_eq by simp
  show ?case
    by (rule Cons.IH[OF tail_left tail_right'])
qed

lemma ro_absorb_lookup_chain_same_final_state:
  assumes builder_chain:
    "ro_absorb_lookup_chain sent start xs builder_final"
    and verifier_chain:
      "ro_absorb_lookup_chain final_state start xs verifier_final"
    and ext: "sent \<le> final_state"
  shows "builder_final = verifier_final"
proof -
  have builder_chain_final:
    "ro_absorb_lookup_chain final_state start xs builder_final"
    by (rule ro_absorb_lookup_chain_mono[OF builder_chain ext])
  show ?thesis
    by (rule ro_absorb_lookup_chain_functional
        [OF builder_chain_final verifier_chain])
qed


lemma ro_checked_staged_query_program_Suc_verifier_round_syncE:
  fixes builder sent verifier_state verifier_state' :: "'f protocol_channel"
    and rest :: "'f list"
  assumes controlled: "staged_adversary_controlled budgets A"
    and bound: "i + Suc n \<le> length (query_opening_budgets budgets)"
    and builder_out:
      "Some (chunks, sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              i (Suc n)) builder)"
    and sent_ext: "sent \<le> verifier_state"
    and state_eq: "PState verifier_state = PState builder"
    and counter_eq: "PQueryCounter verifier_state = PQueryCounter builder"
    and transcript_prefix:
      "PTranscript verifier_state = List.concat chunks @ rest"
    and trace_roots_eq: "trace_roots = map snd f_fl"
    and composition_roots_eq: "composition_roots = map snd fl"
    and verifier_out:
      "Some ((), verifier_state') \<in>
        set_dist
          (execute
            (ro_verifier_query_round_program fr f_fl f_final as fl final)
            verifier_state)"
  obtains raw chunk chunks' s1 s2 s3 where
    "Some (raw, s1) \<in> set_dist (execute receive_query_index_challenge builder)"
    "Some (chunk, s2) \<in> set_dist (execute (query_opening_stage A i raw) s1)"
    "verifier_query_round_chunk (index (to_nat raw)) trace_roots composition_roots chunk"
    "Some ((), s3) \<in> set_dist (execute (ro_record_staged_messages chunk) s2)"
    "Some (chunks', sent) \<in>
      set_dist
        (execute
          (ro_checked_staged_query_program A trace_roots composition_roots
            (Suc i) n) s3)"
    "chunks = chunk # chunks'"
    "PState verifier_state' = PState s3"
    "PTranscript verifier_state' = List.concat chunks' @ rest"
    "verifier_state \<le> verifier_state'"
    "PQueryCounter verifier_state' = Suc (PQueryCounter builder)"
    "ro_absorb_lookup_chain sent (PState builder) chunk (PState s3)"
proof -
  from ro_checked_staged_query_program_Suc_synchronizationE
      [OF controlled bound builder_out]
  obtain raw chunk chunks' s1 s2 s3 where
    builder_challenge:
      "Some (raw, s1) \<in>
        set_dist (execute receive_query_index_challenge builder)"
    and stage:
      "Some (chunk, s2) \<in>
        set_dist (execute (query_opening_stage A i raw) s1)"
    and chunk_shape:
      "verifier_query_round_chunk (index (to_nat raw))
        trace_roots composition_roots chunk"
    and record_out:
      "Some ((), s3) \<in>
        set_dist (execute (ro_record_staged_messages chunk) s2)"
    and rest:
      "Some (chunks', sent) \<in>
        set_dist
          (execute
            (ro_checked_staged_query_program A trace_roots composition_roots
              (Suc i) n) s3)"
    and chunks_eq: "chunks = chunk # chunks'"
    and builder_ext: "builder \<le> s1"
    and builder_state_s1: "PState s1 = PState builder"
    and builder_counter_s1:
      "PQueryCounter s1 = Suc (PQueryCounter builder)"
    and s3_sent: "s3 \<le> sent"
    and counter_s3: "PQueryCounter s3 = Suc (PQueryCounter builder)"
    and builder_chain:
      "ro_absorb_lookup_chain sent (PState builder) chunk (PState s3)"
    and recorded:
      "fmlookup (HashMap sent)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) = Some raw"
    .
  from ro_verifier_query_round_program_outcome_with_lookup_chain[OF verifier_out]
  obtain vraw vs1 vchunk where
    verifier_challenge:
      "Some (vraw, vs1) \<in>
        set_dist (execute receive_query_index_challenge verifier_state)"
    and verifier_challenge_state:
      "PState vs1 = PState verifier_state"
    and verifier_challenge_transcript:
      "PTranscript vs1 = PTranscript verifier_state"
    and verifier_challenge_ext: "verifier_state \<le> vs1"
    and verifier_challenge_counter:
      "PQueryCounter vs1 = Suc (PQueryCounter verifier_state)"
    and verifier_chunk_shape:
      "verifier_query_round_chunk (index (to_nat vraw))
        (map snd f_fl) (map snd fl) vchunk"
    and verifier_transcript:
      "PTranscript verifier_state = vchunk @ PTranscript verifier_state'"
    and verifier_chain:
      "ro_absorb_lookup_chain verifier_state' (PState verifier_state) vchunk
        (PState verifier_state')"
    and verifier_ext: "verifier_state \<le> verifier_state'"
    and verifier_counter:
      "PQueryCounter verifier_state' = Suc (PQueryCounter verifier_state)"
    .
  have challenge_match:
    "vraw = raw \<and>
      PState vs1 = PState builder \<and>
      PTranscript vs1 = PTranscript verifier_state \<and>
      verifier_state \<le> vs1 \<and>
      PQueryCounter vs1 = Suc (PQueryCounter builder) \<and>
      fmlookup (HashMap vs1)
        (QueryIndexChallenge (PQueryCounter builder) (PState builder)) =
        Some raw"
    by (rule receive_query_index_challenge_matches_extended_recorded_lookup
        [OF recorded sent_ext state_eq counter_eq verifier_challenge])
  have vraw_eq: "vraw = raw"
    using challenge_match by simp
  have chunk_len:
    "length chunk =
      verifier_query_round_transcript_length (index (to_nat raw))
        trace_roots composition_roots"
    by (rule verifier_query_round_chunk_length[OF chunk_shape])
  have vchunk_len:
    "length vchunk =
      verifier_query_round_transcript_length (index (to_nat vraw))
        (map snd f_fl) (map snd fl)"
    by (rule verifier_query_round_chunk_length[OF verifier_chunk_shape])
  have len_eq: "length vchunk = length chunk"
    using vchunk_len chunk_len vraw_eq trace_roots_eq composition_roots_eq
    by simp
  have builder_prefix:
    "PTranscript verifier_state = chunk @ List.concat chunks' @ rest"
    using transcript_prefix chunks_eq by simp
  have vchunk_take:
    "vchunk = take (length vchunk) (PTranscript verifier_state)"
    using verifier_transcript by simp
  have chunk_take:
    "chunk = take (length chunk) (PTranscript verifier_state)"
    using builder_prefix by simp
  have vchunk_eq: "vchunk = chunk"
    using vchunk_take chunk_take len_eq by simp
  have tail_transcript:
    "PTranscript verifier_state' = List.concat chunks' @ rest"
    using verifier_transcript builder_prefix vchunk_eq by simp
  have sent_ext_final: "sent \<le> verifier_state'"
    by (rule hash_ext_trans[OF sent_ext verifier_ext])
  have verifier_chain_builder:
    "ro_absorb_lookup_chain verifier_state' (PState builder) chunk
      (PState verifier_state')"
    using verifier_chain state_eq vchunk_eq by simp
  have state_sync:
    "PState s3 = PState verifier_state'"
    by (rule ro_absorb_lookup_chain_same_final_state
        [OF builder_chain verifier_chain_builder sent_ext_final])
  have state_sync': "PState verifier_state' = PState s3"
    using state_sync by simp
  have verifier_counter_builder:
    "PQueryCounter verifier_state' = Suc (PQueryCounter builder)"
    using verifier_counter counter_eq by simp
  show ?thesis
    by (rule that[OF builder_challenge stage chunk_shape record_out rest
          chunks_eq state_sync' tail_transcript verifier_ext
          verifier_counter_builder builder_chain])
qed

end

end
