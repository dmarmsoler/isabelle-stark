(*  Title:      Stark/Soundness_Execution_Query.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Execution_Query
  imports Soundness_Merkle
begin

text \<open>Verifier query-round and authenticated-opening execution lemmas.\<close>

context soundness
begin

lemma receive_random_field_element_outcome:
  assumes outcome: "Some (a, t) \<in> set_dist (execute receive_random_field_element s)"
  shows
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t) (FiatShamirChallenge (PState s)) = Some a"
  using protocol_receive_random_field_element_outcome
      [OF outcome[unfolded receive_random_field_element_def]]
  by simp

lemma throw_no_outcome:
  "Some (x, t) \<notin> set_dist (execute throw s)"
  unfolding set_dist_def throw.rep_eq dist_throw_def dist_delta_dist delta_map_def
  by simp

lemma read_outcome:
  assumes outcome: "Some (x, t) \<in> set_dist (execute read s)"
  shows
    "\<exists>rest.
      PTranscript s = x # rest \<and>
      PState t = concat (PState s) x \<and>
      PTranscript t = rest \<and>
      s \<le> t \<and>
      PTraceFriCounter t = PTraceFriCounter s \<and>
      PCompositionFriCounter t = PCompositionFriCounter s \<and>
      PAlphaCounter t = PAlphaCounter s \<and>
      PQueryCounter t = PQueryCounter s"
proof -
  obtain rest where tr_s: "PTranscript s = x # rest"
  proof -
    have "PTranscript s \<noteq> []"
      using outcome unfolding read_def protocol_read_def assert_def
      by (cases "PTranscript s") (auto simp: throw_no_outcome elim!: set_dist_bindE)
    then obtain y ys where ys: "PTranscript s = y # ys"
      by (cases "PTranscript s") auto
    have x_y: "x = y"
      using read_nonempty_outcome[OF outcome ys] by simp
    show ?thesis
      using that ys x_y by auto
  qed
  have t_res:
    "t = s\<lparr>PState := concat (PState s) x, PTranscript := rest\<rparr>"
    using read_nonempty_outcome[OF outcome tr_s] by simp
  have "s \<le> t"
    unfolding t_res less_eq_hash_ext_def less_eq_fmap_def by simp
  then show ?thesis
    using tr_s t_res by auto
qed

lemma read_preserves_hash_map:
  assumes outcome: "Some (x, t) \<in> set_dist (execute read s)"
  shows "HashMap t = HashMap s"
proof -
  obtain rest where tr_s: "PTranscript s = x # rest"
  proof -
    have "PTranscript s \<noteq> []"
      using outcome unfolding read_def protocol_read_def assert_def
      by (cases "PTranscript s") (auto simp: throw_no_outcome elim!: set_dist_bindE)
    then obtain y ys where ys: "PTranscript s = y # ys"
      by (cases "PTranscript s") auto
    have x_y: "x = y"
      using read_nonempty_outcome[OF outcome ys] by simp
    show ?thesis
      using that ys x_y by auto
  qed
  show ?thesis
    using read_nonempty_outcome[OF outcome tr_s] by simp
qed

lemma read_preserves_alpha_future_fresh:
  assumes future: "alpha_future_fresh s"
    and outcome: "Some (x, t) \<in> set_dist (execute read s)"
  shows "alpha_future_fresh t"
proof -
  have hash_eq: "HashMap t = HashMap s"
    by (rule read_preserves_hash_map[OF outcome])
  from read_outcome[OF outcome] have counter_eq:
    "PAlphaCounter t = PAlphaCounter s"
    by blast
  show ?thesis
    using future hash_eq counter_eq
    unfolding alpha_future_fresh_def by simp
qed

lemma read_preserves_trace_fri_future_fresh:
  assumes future: "trace_fri_future_fresh s"
    and outcome: "Some (x, t) \<in> set_dist (execute read s)"
  shows "trace_fri_future_fresh t"
proof -
  have hash_eq: "HashMap t = HashMap s"
    by (rule read_preserves_hash_map[OF outcome])
  from read_outcome[OF outcome] have counter_eq:
    "PTraceFriCounter t = PTraceFriCounter s"
    by blast
  show ?thesis
    using future hash_eq counter_eq
    unfolding trace_fri_future_fresh_def by simp
qed

lemma read_preserves_composition_fri_future_fresh:
  assumes future: "composition_fri_future_fresh s"
    and outcome: "Some (x, t) \<in> set_dist (execute read s)"
  shows "composition_fri_future_fresh t"
proof -
  have hash_eq: "HashMap t = HashMap s"
    by (rule read_preserves_hash_map[OF outcome])
  from read_outcome[OF outcome] have counter_eq:
    "PCompositionFriCounter t = PCompositionFriCounter s"
    by blast
  show ?thesis
    using future hash_eq counter_eq
    unfolding composition_fri_future_fresh_def by simp
qed

lemma read_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome: "Some (x, t) \<in> set_dist (execute read s)"
  shows "query_future_fresh t"
proof -
  have hash_eq: "HashMap t = HashMap s"
    by (rule read_preserves_hash_map[OF outcome])
  from read_outcome[OF outcome] have counter_eq:
    "PQueryCounter t = PQueryCounter s"
    by blast
  show ?thesis
    using future hash_eq counter_eq
    unfolding query_future_fresh_def by simp
qed

lemma ntimes_read_any_outcome:
  assumes outcome: "Some (xs, t) \<in> set_dist (execute (ntimes read n) s)"
  shows
    "length xs = n \<and>
     PTranscript s = xs @ PTranscript t \<and>
     PState t = foldl concat (PState s) xs \<and>
     s \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction n arbitrary: s xs t)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain x xs' s1 where
    read_x: "Some (x, s1) \<in> set_dist (execute read s)"
    and reads:
      "Some (xs', t) \<in> set_dist (execute (ntimes read n) s1)"
    and xs_eq: "xs = x # xs'"
    by (auto elim!: set_dist_bindE)
  from read_outcome[OF read_x] obtain rest1 where
    tr_s: "PTranscript s = x # rest1"
    and st_s1: "PState s1 = concat (PState s) x"
    and tr_s1: "PTranscript s1 = rest1"
    and ext_s_s1: "s \<le> s1"
    and trace_count_s1: "PTraceFriCounter s1 = PTraceFriCounter s"
    and comp_count_s1: "PCompositionFriCounter s1 = PCompositionFriCounter s"
    and alpha_count_s1: "PAlphaCounter s1 = PAlphaCounter s"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  have tail:
    "length xs' = n \<and>
     PTranscript s1 = xs' @ PTranscript t \<and>
     PState t = foldl concat (PState s1) xs' \<and>
     s1 \<le> t \<and>
     PTraceFriCounter t = PTraceFriCounter s1 \<and>
     PCompositionFriCounter t = PCompositionFriCounter s1 \<and>
     PAlphaCounter t = PAlphaCounter s1 \<and>
     PQueryCounter t = PQueryCounter s1"
    using Suc.IH[OF reads] .
  have "s \<le> t"
    using ext_s_s1 tail by (meson hash_ext_trans)
  then show ?case
    using tr_s st_s1 tr_s1 tail xs_eq trace_count_s1 comp_count_s1
      alpha_count_s1 query_count_s1
    by simp
qed

lemma ntimes_read_preserves_lookup:
  assumes outcome: "Some (xs, t) \<in> set_dist (execute (ntimes read n) s)"
  shows "fmlookup (HashMap t) key = fmlookup (HashMap s) key"
proof (rule ntimes_preserves_lookup[OF _ outcome])
  fix x s t
  assume read_x: "Some (x, t) \<in> set_dist (execute read s)"
  show "fmlookup (HashMap t) key = fmlookup (HashMap s) key"
    using read_preserves_hash_map[OF read_x] by simp
qed

lemma check_authentication_path_hash_extends:
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

lemma check_decommit_on_query_step_outcome:
  assumes outcome:
    "Some (qh, t) \<in> set_dist (execute
      (do {
        qh \<leftarrow> read;
        let len = scale * clength;
        qh_path \<leftarrow> ntimes read (floor_log len);
        ap \<leftarrow> check_authentication_path len i qh qh_path;
        assert (ap = fr);
        return qh
      }) s)"
  shows
    "\<exists>path.
      length path = floor_log (scale * clength) \<and>
      PTranscript s = ([qh] @ path) @ PTranscript t \<and>
      PState t = foldl concat (PState s) ([qh] @ path) \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s"
proof -
  let ?len = "scale * clength"
  from outcome obtain s1 path s2 ap s3 s4 where
    read_qh: "Some (qh, s1) \<in> set_dist (execute read s)"
    and read_path:
      "Some (path, s2) \<in>
        set_dist (execute (ntimes read (floor_log ?len)) s1)"
    and check:
      "Some (ap, s3) \<in>
        set_dist (execute (check_authentication_path ?len i qh path) s2)"
    and assert_ap: "Some ((), s4) \<in> set_dist (execute (assert (ap = fr)) s3)"
    and ret_qh: "Some (qh, t) \<in> set_dist (execute (return qh) s4)"
    by (auto simp: Let_def elim!: set_dist_bindE)
  from read_outcome[OF read_qh] obtain rest1 where
    tr_s: "PTranscript s = qh # rest1"
    and st_s1: "PState s1 = concat (PState s) qh"
    and tr_s1: "PTranscript s1 = rest1"
    and ext_s_s1: "s \<le> s1"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  have path_res:
    "length path = floor_log ?len \<and>
     PTranscript s1 = path @ PTranscript s2 \<and>
     PState s2 = foldl concat (PState s1) path \<and>
     s1 \<le> s2 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    using ntimes_read_any_outcome[OF read_path] by simp
  have s2_s3: "s2 \<le> s3"
    by (rule check_authentication_path_hash_extends[OF check])
  have st_s3: "PState s3 = PState s2"
    using check_authentication_path_preserves_channel(1)[OF check] .
  have tr_s3: "PTranscript s3 = PTranscript s2"
    using check_authentication_path_preserves_channel(2)[OF check] .
  have query_count_s3: "PQueryCounter s3 = PQueryCounter s2"
    using check_authentication_path_preserves_channel(6)[OF check] .
  have ap_eq: "ap = fr"
    using assert_ap unfolding assert_def
    by (cases "ap = fr") (auto simp: throw_no_outcome)
  have s4_eq: "s4 = s3"
    using assert_ap ap_eq unfolding assert_def by simp
  have t_eq: "t = s4"
    using ret_qh by simp
  have "s \<le> t"
    using ext_s_s1 path_res s2_s3 unfolding t_eq s4_eq
    by (meson hash_ext_trans)
  then show ?thesis
    using tr_s st_s1 tr_s1 path_res st_s3 tr_s3 query_count_s1
      query_count_s3 s4_eq t_eq
    by auto
qed

definition query_decommitment_step
  where
    "query_decommitment_step fr i =
      (do {
        qh \<leftarrow> read;
        let len = scale * clength;
        qh_path \<leftarrow> ntimes read (floor_log len);
        ap \<leftarrow> check_authentication_path len i qh qh_path;
        assert (ap = fr);
        return qh
      })"

lemma query_decommitment_step_outcome:
  assumes outcome:
    "Some (qh, t) \<in> set_dist (execute (query_decommitment_step fr i) s)"
  shows
    "\<exists>path.
      length path = floor_log (scale * clength) \<and>
      PTranscript s = ([qh] @ path) @ PTranscript t \<and>
      PState t = foldl concat (PState s) ([qh] @ path) \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s"
  using check_decommit_on_query_step_outcome[OF outcome[unfolded query_decommitment_step_def]] .

lemma mmap_query_decommitment_steps_outcome:
  assumes outcome:
    "Some (leaves, t) \<in>
      set_dist (execute (mmap (map (query_decommitment_step fr) idxs)) s)"
  shows
    "\<exists>paths chunk.
      length leaves = length idxs \<and>
      length paths = length idxs \<and>
      chunk = List.concat (map (\<lambda>(leaf, path). [leaf] @ path) (zip leaves paths)) \<and>
      (\<forall>path \<in> set paths. length path = floor_log (scale * clength)) \<and>
      PTranscript s = chunk @ PTranscript t \<and>
      PState t = foldl concat (PState s) chunk \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction idxs arbitrary: s leaves t)
  case Nil
  then show ?case
    by (intro exI[of _ "[]"]) (simp add: hash_ext_refl)
next
  case (Cons i idxs)
  from Cons.prems obtain leaf leaves' s1 where
    head:
      "Some (leaf, s1) \<in>
        set_dist (execute (query_decommitment_step fr i) s)"
    and tail:
      "Some (leaves', t) \<in>
        set_dist (execute (mmap (map (query_decommitment_step fr) idxs)) s1)"
    and leaves_eq: "leaves = leaf # leaves'"
    by (auto elim!: set_dist_bindE)
  from query_decommitment_step_outcome[OF head] obtain path where
    path_len: "length path = floor_log (scale * clength)"
    and tr_s: "PTranscript s = ([leaf] @ path) @ PTranscript s1"
    and st_s1: "PState s1 = foldl concat (PState s) ([leaf] @ path)"
    and ext_s_s1: "s \<le> s1"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  from Cons.IH[OF tail] obtain paths chunk_tail where
    len_leaves': "length leaves' = length idxs"
    and len_paths: "length paths = length idxs"
    and chunk_tail:
      "chunk_tail =
        List.concat (map (\<lambda>(leaf, path). [leaf] @ path) (zip leaves' paths))"
    and paths_len:
      "\<forall>path \<in> set paths. length path = floor_log (scale * clength)"
    and tr_s1: "PTranscript s1 = chunk_tail @ PTranscript t"
    and st_t: "PState t = foldl concat (PState s1) chunk_tail"
    and ext_s1_t: "s1 \<le> t"
    and query_count_t: "PQueryCounter t = PQueryCounter s1"
    by blast
  let ?paths = "path # paths"
  let ?chunk = "([leaf] @ path) @ chunk_tail"
  have "s \<le> t"
    using ext_s_s1 ext_s1_t by (rule hash_ext_trans)
  then show ?case
    apply (intro exI[of _ ?paths] exI[of _ ?chunk])
    using leaves_eq path_len tr_s tr_s1 st_s1 st_t len_leaves' len_paths
      chunk_tail paths_len query_count_s1 query_count_t
    by simp
qed

lemma check_decommit_on_query_outcome:
  assumes outcome:
    "Some (leaves, t) \<in>
      set_dist (execute (mmap (check_decommit_on_query fr idx)) s)"
  shows
    "\<exists>paths chunk.
      query_decommitment_transcript idx leaves paths chunk \<and>
      PTranscript s = chunk @ PTranscript t \<and>
      PState t = foldl concat (PState s) chunk \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s"
proof -
  have map_eq:
    "check_decommit_on_query fr idx =
      map (query_decommitment_step fr) (powers_scaled idx)"
    unfolding check_decommit_on_query_def query_decommitment_step_def by simp
  from mmap_query_decommitment_steps_outcome[OF outcome[unfolded map_eq]]
  obtain paths chunk where
    len_leaves: "length leaves = length (powers_scaled idx)"
    and len_paths: "length paths = length (powers_scaled idx)"
    and chunk:
      "chunk = List.concat
        (map (\<lambda>(leaf, path). [leaf] @ path) (zip leaves paths))"
    and paths_len:
      "\<forall>path \<in> set paths. length path = floor_log (scale * clength)"
    and tr_s: "PTranscript s = chunk @ PTranscript t"
    and st_t: "PState t = foldl concat (PState s) chunk"
    and ext: "s \<le> t"
    and query_count_t: "PQueryCounter t = PQueryCounter s"
    by blast
  have qtr: "query_decommitment_transcript idx leaves paths chunk"
    using len_leaves len_paths chunk paths_len
    unfolding query_decommitment_transcript_def
    by (simp add: mult.commute case_prod_unfold)
  show ?thesis
    using qtr tr_s st_t ext query_count_t by blast
qed

lemma query_decommitment_step_preserves_query_lookup:
  assumes outcome:
    "Some (qh, t) \<in> set_dist (execute (query_decommitment_step fr i) s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
proof -
  let ?len = "scale * clength"
  from outcome obtain s1 path s2 ap s3 s4 where
    read_qh: "Some (qh, s1) \<in> set_dist (execute read s)"
    and read_path:
      "Some (path, s2) \<in>
        set_dist (execute (ntimes read (floor_log ?len)) s1)"
    and check:
      "Some (ap, s3) \<in>
        set_dist (execute (check_authentication_path ?len i qh path) s2)"
    and assert_ap: "Some ((), s4) \<in> set_dist (execute (assert (ap = fr)) s3)"
    and ret_qh: "Some (qh, t) \<in> set_dist (execute (return qh) s4)"
    unfolding query_decommitment_step_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  have lookup_s1:
    "fmlookup (HashMap s1) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
    using read_preserves_hash_map[OF read_qh] by simp
  have lookup_s2:
    "fmlookup (HashMap s2) (QueryIndexChallenge j x) =
      fmlookup (HashMap s1) (QueryIndexChallenge j x)"
    by (rule ntimes_read_preserves_lookup[OF read_path])
  have lookup_s3:
    "fmlookup (HashMap s3) (QueryIndexChallenge j x) =
      fmlookup (HashMap s2) (QueryIndexChallenge j x)"
    by (rule check_authentication_path_preserves_challenge_lookups(2)
        [OF check])
  have s4_eq: "s4 = s3"
    using assert_ap unfolding assert_def
    by (cases "ap = fr") (auto simp: throw_no_outcome)
  have t_eq: "t = s4"
    using ret_qh by simp
  show ?thesis
    using lookup_s1 lookup_s2 lookup_s3 s4_eq t_eq by simp
qed

lemma mmap_query_decommitment_steps_preserves_query_lookup:
  assumes outcome:
    "Some (leaves, t) \<in>
      set_dist (execute (mmap (map (query_decommitment_step fr) idxs)) s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
  using outcome
proof (induction idxs arbitrary: s leaves t)
  case Nil
  then show ?case
    by simp
next
  case (Cons i idxs)
  from Cons.prems obtain leaf leaves' s1 where
    head:
      "Some (leaf, s1) \<in>
        set_dist (execute (query_decommitment_step fr i) s)"
    and tail:
      "Some (leaves', t) \<in>
        set_dist (execute (mmap (map (query_decommitment_step fr) idxs)) s1)"
    by (auto elim!: set_dist_bindE)
  have head_pres:
    "fmlookup (HashMap s1) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
    by (rule query_decommitment_step_preserves_query_lookup[OF head])
  have tail_pres:
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s1) (QueryIndexChallenge j x)"
    by (rule Cons.IH[OF tail])
  show ?case
    using head_pres tail_pres by simp
qed

lemma check_decommit_on_query_preserves_query_lookup:
  assumes outcome:
    "Some (leaves, t) \<in>
      set_dist (execute (mmap (check_decommit_on_query fr idx)) s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
proof -
  have map_eq:
    "check_decommit_on_query fr idx =
      map (query_decommitment_step fr) (powers_scaled idx)"
    unfolding check_decommit_on_query_def query_decommitment_step_def by simp
  show ?thesis
    by (rule mmap_query_decommitment_steps_preserves_query_lookup
        [OF outcome[unfolded map_eq]])
qed

definition fri_layer_opening_step
  where
    "fri_layer_opening_step bf st =
      (case bf of (b, f) \<Rightarrow>
        case st of (i, x, len, pw) \<Rightarrow>
          do {
            xp \<leftarrow> read;
            xp' \<leftarrow> ntimes read (floor_log len);
            xn \<leftarrow> read;
            xn' \<leftarrow> ntimes read (floor_log len);
            assert (xp = x);
            ap \<leftarrow> check_authentication_path len i xp xp';
            assert (ap = f);
            let sidx = (i + len div 2) mod len;
            ap \<leftarrow> check_authentication_path len sidx xn xn';
            assert (ap = f);
            let gp = (xp + xn) div 2;
            let hp = (xp - xn) div (2*((h^i) * shift)^pw);
            let x = gp + b * hp;
            return (i mod (len div 2), x, len div 2, pw+pw)
          })"

definition fri_layer_opening_finish
  where
    "fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path =
      do {
        assert (xp = x);
        ap \<leftarrow> check_authentication_path len i xp xp_path;
        assert (ap = f);
        let sidx = (i + len div 2) mod len;
        ap \<leftarrow> check_authentication_path len sidx xn xn_path;
        assert (ap = f);
        let gp = (xp + xn) div 2;
        let hp = (xp - xn) div (2*((h^i) * shift)^pw);
        let x = gp + b * hp;
        return (i mod (len div 2), x, len div 2, pw+pw)
      }"

lemma fri_layer_opening_step_unfold_finish:
  "fri_layer_opening_step (b, f) (i, x, len, pw) =
    do {
      xp \<leftarrow> read;
      xp_path \<leftarrow> ntimes read (floor_log len);
      xn \<leftarrow> read;
      xn_path \<leftarrow> ntimes read (floor_log len);
      fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path
    }"
  unfolding fri_layer_opening_step_def fri_layer_opening_finish_def
  by simp

lemma fri_layer_opening_step_outcome:
  assumes outcome:
    "Some (out, t) \<in>
      set_dist (execute (fri_layer_opening_step (b, f) (i, x, len, pw)) s)"
  shows
    "\<exists>xp xp_path xn xn_path x'.
      out = (i mod (len div 2), x', len div 2, pw + pw) \<and>
      xp = x \<and>
      x' = fri_fold_value b xp xn
        (fri_fold_denominator ((h ^ i) * shift) pw) \<and>
      fri_layer_opening_chunk len xp xp_path xn xn_path
        ([xp] @ xp_path @ [xn] @ xn_path) \<and>
      PTranscript s = ([xp] @ xp_path @ [xn] @ xn_path) @ PTranscript t \<and>
      PState t = foldl concat (PState s) ([xp] @ xp_path @ [xn] @ xn_path) \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s"
proof -
  from outcome obtain xp s1 xp_path s2 xn s3 xn_path s4 s5 ap1 s6 s7
      ap2 s8 s9 where
    read_xp: "Some (xp, s1) \<in> set_dist (execute read s)"
    and read_xp_path:
      "Some (xp_path, s2) \<in>
        set_dist (execute (ntimes read (floor_log len)) s1)"
    and read_xn: "Some (xn, s3) \<in> set_dist (execute read s2)"
    and read_xn_path:
      "Some (xn_path, s4) \<in>
        set_dist (execute (ntimes read (floor_log len)) s3)"
    and assert_xp: "Some ((), s5) \<in> set_dist (execute (assert (xp = x)) s4)"
    and check1:
      "Some (ap1, s6) \<in>
        set_dist (execute (check_authentication_path len i xp xp_path) s5)"
    and assert_ap1: "Some ((), s7) \<in> set_dist (execute (assert (ap1 = f)) s6)"
    and check2:
      "Some (ap2, s8) \<in>
        set_dist (execute
          (check_authentication_path len ((i + len div 2) mod len) xn xn_path) s7)"
    and assert_ap2: "Some ((), s9) \<in> set_dist (execute (assert (ap2 = f)) s8)"
    and ret:
      "Some (out, t) \<in>
        set_dist (execute
          (return
            (i mod (len div 2),
              (xp + xn) div 2 +
                b * ((xp - xn) div (2 * ((h ^ i) * shift) ^ pw)),
              len div 2, pw + pw)) s9)"
    unfolding fri_layer_opening_step_def
    by (auto simp: Let_def elim!: set_dist_bindE)
  from read_outcome[OF read_xp] obtain rest1 where
    tr_s: "PTranscript s = xp # rest1"
    and st_s1: "PState s1 = concat (PState s) xp"
    and tr_s1: "PTranscript s1 = rest1"
    and ext_s_s1: "s \<le> s1"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  have xp_path_res:
    "length xp_path = floor_log len \<and>
     PTranscript s1 = xp_path @ PTranscript s2 \<and>
     PState s2 = foldl concat (PState s1) xp_path \<and>
     s1 \<le> s2 \<and>
     PQueryCounter s2 = PQueryCounter s1"
    using ntimes_read_any_outcome[OF read_xp_path] by simp
  from read_outcome[OF read_xn] obtain rest3 where
    tr_s2: "PTranscript s2 = xn # rest3"
    and st_s3: "PState s3 = concat (PState s2) xn"
    and tr_s3: "PTranscript s3 = rest3"
    and ext_s2_s3: "s2 \<le> s3"
    and query_count_s3: "PQueryCounter s3 = PQueryCounter s2"
    by blast
  have xn_path_res:
    "length xn_path = floor_log len \<and>
     PTranscript s3 = xn_path @ PTranscript s4 \<and>
     PState s4 = foldl concat (PState s3) xn_path \<and>
     s3 \<le> s4 \<and>
     PQueryCounter s4 = PQueryCounter s3"
    using ntimes_read_any_outcome[OF read_xn_path] by simp
  have xp_eq: "xp = x"
    using assert_xp unfolding assert_def
    by (cases "xp = x") (auto simp: throw_no_outcome)
  have s5_eq: "s5 = s4"
    using assert_xp xp_eq unfolding assert_def by simp
  have s5_s6: "s5 \<le> s6"
    by (rule check_authentication_path_hash_extends[OF check1])
  have st_s6: "PState s6 = PState s5"
    using check_authentication_path_preserves_channel(1)[OF check1] .
  have tr_s6: "PTranscript s6 = PTranscript s5"
    using check_authentication_path_preserves_channel(2)[OF check1] .
  have query_count_s6: "PQueryCounter s6 = PQueryCounter s5"
    using check_authentication_path_preserves_channel(6)[OF check1] .
  have ap1_eq: "ap1 = f"
    using assert_ap1 unfolding assert_def
    by (cases "ap1 = f") (auto simp: throw_no_outcome)
  have s7_eq: "s7 = s6"
    using assert_ap1 ap1_eq unfolding assert_def by simp
  have s7_s8: "s7 \<le> s8"
    by (rule check_authentication_path_hash_extends[OF check2])
  have st_s8: "PState s8 = PState s7"
    using check_authentication_path_preserves_channel(1)[OF check2] .
  have tr_s8: "PTranscript s8 = PTranscript s7"
    using check_authentication_path_preserves_channel(2)[OF check2] .
  have query_count_s8: "PQueryCounter s8 = PQueryCounter s7"
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
  have chunk_shape:
    "fri_layer_opening_chunk len xp xp_path xn xn_path
      ([xp] @ xp_path @ [xn] @ xn_path)"
    using xp_path_res xn_path_res unfolding fri_layer_opening_chunk_def by simp
  have tr_t:
    "PTranscript s = ([xp] @ xp_path @ [xn] @ xn_path) @ PTranscript t"
    using tr_s tr_s1 xp_path_res tr_s2 tr_s3 xn_path_res s5_eq tr_s6
      s7_eq tr_s8 s9_eq out_t
    by simp
  have st_t:
    "PState t = foldl concat (PState s) ([xp] @ xp_path @ [xn] @ xn_path)"
    using st_s1 xp_path_res st_s3 xn_path_res s5_eq st_s6 s7_eq st_s8
      s9_eq out_t
    by simp
  have s_t: "s \<le> t"
    using ext_s_s1 xp_path_res ext_s2_s3 xn_path_res s5_s6 s7_s8 out_t
    unfolding s5_eq s7_eq s9_eq
    by (meson hash_ext_trans)
  have query_count_t: "PQueryCounter t = PQueryCounter s"
    using out_t query_count_s1
      xp_path_res query_count_s3 xn_path_res query_count_s6 query_count_s8
      s5_eq s7_eq s9_eq
    by simp
  show ?thesis
    apply (rule exI[where x=xp])
    apply (rule exI[where x=xp_path])
    apply (rule exI[where x=xn])
    apply (rule exI[where x=xn_path])
    apply (rule exI[where x="?x'"])
    using out_t xp_eq x'_fold chunk_shape tr_t st_t s_t query_count_t
    by simp
qed

lemma mfold_fri_layer_openings_outcome:
  assumes outcome:
    "Some (out, t) \<in>
      set_dist (execute (mfold (i, x, len, pw) (map fri_layer_opening_step bfs)) s)"
  shows
    "\<exists>layer_chunks chunk.
      fri_layers_transcript (length bfs) len layer_chunks chunk \<and>
      PTranscript s = chunk @ PTranscript t \<and>
      PState t = foldl concat (PState s) chunk \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction bfs arbitrary: i x len pw s out t)
  case Nil
  then show ?case
    by (intro exI[of _ "[]"]) (simp add: fri_layers_transcript_def hash_ext_refl)
next
  case (Cons bf bfs)
  obtain b f where bf_eq: "bf = (b, f)"
    by (cases bf)
  from Cons.prems obtain out1 s1 where
    head:
      "Some (out1, s1) \<in>
        set_dist (execute (fri_layer_opening_step bf (i, x, len, pw)) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist (execute (mfold out1 (map fri_layer_opening_step bfs)) s1)"
    by (auto elim!: set_dist_bindE)
  from fri_layer_opening_step_outcome[OF head[unfolded bf_eq]]
  obtain xp xp_path xn xn_path x' where
    out1_eq: "out1 = (i mod (len div 2), x', len div 2, pw + pw)"
    and head_chunk:
      "fri_layer_opening_chunk len xp xp_path xn xn_path
        ([xp] @ xp_path @ [xn] @ xn_path)"
    and tr_s: "PTranscript s = ([xp] @ xp_path @ [xn] @ xn_path) @ PTranscript s1"
    and st_s1:
      "PState s1 = foldl concat (PState s) ([xp] @ xp_path @ [xn] @ xn_path)"
    and ext_s_s1: "s \<le> s1"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  from Cons.IH[OF tail[unfolded out1_eq]]
  obtain layer_chunks chunk_tail where
    tail_layers:
      "fri_layers_transcript (length bfs) (len div 2) layer_chunks chunk_tail"
    and tr_s1: "PTranscript s1 = chunk_tail @ PTranscript t"
    and st_t: "PState t = foldl concat (PState s1) chunk_tail"
    and ext_s1_t: "s1 \<le> t"
    and query_count_t: "PQueryCounter t = PQueryCounter s1"
    by blast
  let ?head_chunk = "[xp] @ xp_path @ [xn] @ xn_path"
  let ?chunks = "?head_chunk # layer_chunks"
  let ?chunk = "?head_chunk @ chunk_tail"
  have layers:
    "fri_layers_transcript (length (bf # bfs)) len ?chunks ?chunk"
    using head_chunk tail_layers
    unfolding fri_layers_transcript_def
    by auto
  have "s \<le> t"
    using ext_s_s1 ext_s1_t by (rule hash_ext_trans)
  then show ?case
    apply (intro exI[of _ ?chunks] exI[of _ ?chunk])
    using layers tr_s tr_s1 st_s1 st_t query_count_s1 query_count_t
    by simp
qed

lemma receive_query_commits_layers_outcome:
  assumes outcome:
    "Some (out, t) \<in>
      set_dist (execute (mfold (i, x, len, pw) (receive_query_commits bfs)) s)"
  shows
    "\<exists>layer_chunks chunk.
      fri_layers_transcript (length bfs) len layer_chunks chunk \<and>
      PTranscript s = chunk @ PTranscript t \<and>
      PState t = foldl concat (PState s) chunk \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s"
proof -
  have map_eq: "receive_query_commits bfs = map fri_layer_opening_step bfs"
    unfolding receive_query_commits_def fri_layer_opening_step_def
    by (simp add: fun_eq_iff split: prod.splits)
  show ?thesis
    using mfold_fri_layer_openings_outcome[OF outcome[unfolded map_eq]] .
qed

lemma fri_layer_opening_step_preserves_query_lookup:
  assumes outcome:
    "Some (out, t) \<in> set_dist (execute (fri_layer_opening_step bf st) s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
proof -
  obtain b f where bf_eq: "bf = (b, f)"
    by (cases bf)
  obtain i0 x0 len pw where st_eq: "st = (i0, x0, len, pw)"
    by (cases st)
  from outcome[unfolded bf_eq st_eq fri_layer_opening_step_def]
  obtain xp s1 xp_path s2 xn s3 xn_path s4 s5 ap1 s6 s7 ap2 s8 s9 where
    read_xp: "Some (xp, s1) \<in> set_dist (execute read s)"
    and read_xp_path:
      "Some (xp_path, s2) \<in>
        set_dist (execute (ntimes read (floor_log len)) s1)"
    and read_xn: "Some (xn, s3) \<in> set_dist (execute read s2)"
    and read_xn_path:
      "Some (xn_path, s4) \<in>
        set_dist (execute (ntimes read (floor_log len)) s3)"
    and assert_xp:
      "Some ((), s5) \<in> set_dist (execute (assert (xp = x0)) s4)"
    and check1:
      "Some (ap1, s6) \<in>
        set_dist (execute (check_authentication_path len i0 xp xp_path) s5)"
    and assert_ap1:
      "Some ((), s7) \<in> set_dist (execute (assert (ap1 = f)) s6)"
    and check2:
      "Some (ap2, s8) \<in>
        set_dist (execute
          (check_authentication_path len ((i0 + len div 2) mod len) xn
            xn_path) s7)"
    and assert_ap2:
      "Some ((), s9) \<in> set_dist (execute (assert (ap2 = f)) s8)"
    and ret:
      "Some (out, t) \<in>
        set_dist
          (execute
            (return (i0 mod (len div 2),
              (xp + xn) div 2 +
                b * ((xp - xn) div (2 * ((h ^ i0) * shift) ^ pw)),
              len div 2, pw + pw)) s9)"
    by (auto elim!: set_dist_bindE)
  have lookup_s1:
    "fmlookup (HashMap s1) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
    using read_preserves_hash_map[OF read_xp] by simp
  have lookup_s2:
    "fmlookup (HashMap s2) (QueryIndexChallenge j x) =
      fmlookup (HashMap s1) (QueryIndexChallenge j x)"
    by (rule ntimes_read_preserves_lookup[OF read_xp_path])
  have lookup_s3:
    "fmlookup (HashMap s3) (QueryIndexChallenge j x) =
      fmlookup (HashMap s2) (QueryIndexChallenge j x)"
    using read_preserves_hash_map[OF read_xn] by simp
  have lookup_s4:
    "fmlookup (HashMap s4) (QueryIndexChallenge j x) =
      fmlookup (HashMap s3) (QueryIndexChallenge j x)"
    by (rule ntimes_read_preserves_lookup[OF read_xn_path])
  have s5_eq: "s5 = s4"
    using assert_xp unfolding assert_def
    by (cases "xp = x0") (auto simp: throw_no_outcome)
  have lookup_s6:
    "fmlookup (HashMap s6) (QueryIndexChallenge j x) =
      fmlookup (HashMap s5) (QueryIndexChallenge j x)"
    by (rule check_authentication_path_preserves_challenge_lookups(2)
        [OF check1])
  have s7_eq: "s7 = s6"
    using assert_ap1 unfolding assert_def
    by (cases "ap1 = f") (auto simp: throw_no_outcome)
  have lookup_s8:
    "fmlookup (HashMap s8) (QueryIndexChallenge j x) =
      fmlookup (HashMap s7) (QueryIndexChallenge j x)"
    by (rule check_authentication_path_preserves_challenge_lookups(2)
        [OF check2])
  have s9_eq: "s9 = s8"
    using assert_ap2 unfolding assert_def
    by (cases "ap2 = f") (auto simp: throw_no_outcome)
  have t_eq: "t = s9"
    using ret by simp
  show ?thesis
    using lookup_s1 lookup_s2 lookup_s3 lookup_s4 lookup_s6 lookup_s8
      s5_eq s7_eq s9_eq t_eq
    by simp
qed

lemma mfold_fri_layer_openings_preserves_query_lookup:
  assumes outcome:
    "Some (out, t) \<in>
      set_dist (execute (mfold st (map fri_layer_opening_step bfs)) s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
  using outcome
proof (induction bfs arbitrary: st s out t)
  case Nil
  then show ?case
    by simp
next
  case (Cons bf bfs)
  from Cons.prems obtain out1 s1 where
    head:
      "Some (out1, s1) \<in>
        set_dist (execute (fri_layer_opening_step bf st) s)"
    and tail:
      "Some (out, t) \<in>
        set_dist (execute (mfold out1 (map fri_layer_opening_step bfs)) s1)"
    by (auto elim!: set_dist_bindE)
  have head_pres:
    "fmlookup (HashMap s1) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
    by (rule fri_layer_opening_step_preserves_query_lookup[OF head])
  have tail_pres:
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s1) (QueryIndexChallenge j x)"
    by (rule Cons.IH[OF tail])
  show ?case
    using head_pres tail_pres by simp
qed

lemma receive_query_commits_layers_preserves_query_lookup:
  assumes outcome:
    "Some (out, t) \<in>
      set_dist (execute (mfold st (receive_query_commits bfs)) s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
proof -
  have map_eq: "receive_query_commits bfs = map fri_layer_opening_step bfs"
    unfolding receive_query_commits_def fri_layer_opening_step_def
    by (simp add: fun_eq_iff split: prod.splits)
  show ?thesis
    by (rule mfold_fri_layer_openings_preserves_query_lookup
        [OF outcome[unfolded map_eq]])
qed

definition verifier_query_round_after_index_program
  where
    "verifier_query_round_after_index_program fr f_fl f_final as fl final raw =
      (let idx' = index (to_nat raw) in
        do {
          fv \<leftarrow> mmap (check_decommit_on_query fr idx');

          (f_i, f_x, f_len, f_pow) \<leftarrow>
            mfold (idx', hd fv, clength * scale, 1)
              (receive_query_commits f_fl);
          assert (f_x = f_final);

          (i, x, len, pow) \<leftarrow>
            mfold (idx', cp_eval as fv (h^idx' * shift), clength * scale, 1)
              (receive_query_commits fl);

          assert (x = final)
        })"

definition verifier_query_round_program
  where
    "verifier_query_round_program fr f_fl f_final as fl final =
      (do {
        idx \<leftarrow> receive_query_index_challenge;
        let idx' = index (to_nat idx);
        fv \<leftarrow> mmap (check_decommit_on_query fr idx');

        (f_i, f_x, f_len, f_pow) \<leftarrow>
          mfold (idx', hd fv, clength * scale, 1) (receive_query_commits f_fl);
        assert (f_x = f_final);

        (i, x, len, pow) \<leftarrow>
          mfold (idx', cp_eval as fv (h^idx' * shift), clength * scale, 1)
            (receive_query_commits fl);

        assert (x = final)
      })"

lemma verifier_query_round_program_alt_def:
  "verifier_query_round_program fr f_fl f_final as fl final =
    (receive_query_index_challenge \<bind>
      verifier_query_round_after_index_program fr f_fl f_final as fl final)"
  unfolding verifier_query_round_program_def
    verifier_query_round_after_index_program_def
  by (simp add: Let_def)

lemma verifier_query_round_after_index_program_outcome:
  assumes outcome:
    "Some ((), t) \<in>
      set_dist (execute
        (verifier_query_round_after_index_program fr f_fl f_final as fl final raw) s)"
  shows "s \<le> t \<and> PQueryCounter t = PQueryCounter s"
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
  from check_decommit_on_query_outcome[OF query_decommit]
  obtain query_paths query_chunk where
    ext_s_s1: "s \<le> s1"
    and query_count_s1: "PQueryCounter s1 = PQueryCounter s"
    by blast
  from receive_query_commits_layers_outcome[OF trace_fri]
  obtain trace_layer_chunks trace_fri_chunk where
    ext_s1_s2: "s1 \<le> s2"
    and query_count_s2: "PQueryCounter s2 = PQueryCounter s1"
    by blast
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  from receive_query_commits_layers_outcome[OF comp_fri]
  obtain comp_layer_chunks comp_fri_chunk where
    ext_s3_s4: "s3 \<le> s4"
    and query_count_s4: "PQueryCounter s4 = PQueryCounter s3"
    by blast
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  have "s \<le> t"
    using ext_s_s1 ext_s1_s2 ext_s3_s4 t_eq unfolding s3_eq
    by (meson hash_ext_trans)
  moreover have "PQueryCounter t = PQueryCounter s"
    using query_count_s1 query_count_s2 query_count_s4 s3_eq t_eq by simp
  ultimately show ?thesis
    by simp
qed

lemma verifier_query_round_after_index_program_preserves_query_lookup:
  assumes outcome:
    "Some ((), t) \<in>
      set_dist (execute
        (verifier_query_round_after_index_program fr f_fl f_final as fl final raw) s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
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
  have lookup_s1:
    "fmlookup (HashMap s1) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
    by (rule check_decommit_on_query_preserves_query_lookup
        [OF query_decommit])
  have lookup_s2:
    "fmlookup (HashMap s2) (QueryIndexChallenge j x) =
      fmlookup (HashMap s1) (QueryIndexChallenge j x)"
    by (rule receive_query_commits_layers_preserves_query_lookup
        [OF trace_fri])
  have s3_eq: "s3 = s2"
    using assert_trace unfolding assert_def
    by (cases "case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final")
      (auto simp: throw_no_outcome)
  have lookup_s4:
    "fmlookup (HashMap s4) (QueryIndexChallenge j x) =
      fmlookup (HashMap s3) (QueryIndexChallenge j x)"
    by (rule receive_query_commits_layers_preserves_query_lookup
        [OF comp_fri])
  have t_eq: "t = s4"
    using assert_comp unfolding assert_def
    by (cases "case c_out of (_, x, _, _) \<Rightarrow> x = final")
      (auto simp: throw_no_outcome)
  show ?thesis
    using lookup_s1 lookup_s2 lookup_s4 s3_eq t_eq by simp
qed

lemma receive_query_index_challenge_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some (raw, t) \<in> set_dist (execute receive_query_index_challenge s)"
  shows "query_future_fresh t"
proof -
  have counter_t: "PQueryCounter t = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF outcome] by simp
  show ?thesis
    unfolding query_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge_t: "PQueryCounter t \<le> i"
    have i_ge_s: "PQueryCounter s \<le> i"
      using i_ge_t counter_t by simp
    have neq:
      "QueryIndexChallenge i x \<noteq>
        QueryIndexChallenge (PQueryCounter s) (PState s)"
      using i_ge_t counter_t by auto
    have "fmlookup (HashMap t) (QueryIndexChallenge i x) =
        fmlookup (HashMap s) (QueryIndexChallenge i x)"
      by (rule receive_query_index_challenge_preserves_other_lookup
          [OF outcome neq])
    also have "... = None"
      using future i_ge_s unfolding query_future_fresh_def by blast
    finally show "fmlookup (HashMap t) (QueryIndexChallenge i x) = None" .
  qed
qed

lemma verifier_query_round_program_preserves_query_future_fresh:
  assumes future: "query_future_fresh s"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  shows "query_future_fresh t"
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
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final raw) s0)"
    by (auto elim!: set_dist_bindE)
  have future_s0: "query_future_fresh s0"
    by (rule receive_query_index_challenge_preserves_query_future_fresh
        [OF future rand])
  have counter_t: "PQueryCounter t = PQueryCounter s0"
    using verifier_query_round_after_index_program_outcome[OF tail] by simp
  show ?thesis
    unfolding query_future_fresh_def
  proof (intro allI impI)
    fix i x
    assume i_ge_t: "PQueryCounter t \<le> i"
    have i_ge_s0: "PQueryCounter s0 \<le> i"
      using i_ge_t counter_t by simp
    have "fmlookup (HashMap t) (QueryIndexChallenge i x) =
        fmlookup (HashMap s0) (QueryIndexChallenge i x)"
      by (rule verifier_query_round_after_index_program_preserves_query_lookup
          [OF tail])
    also have "... = None"
      using future_s0 i_ge_s0 unfolding query_future_fresh_def by blast
    finally show "fmlookup (HashMap t) (QueryIndexChallenge i x) = None" .
  qed
qed

lemma ntimes_verifier_query_round_program_preserves_query_future_fresh:
  assumes outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
              n) s)"
    and future: "query_future_fresh s"
  shows "query_future_fresh t"
  using outcome future
proof (induction n arbitrary: s results t)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems obtain u results' s1 where
    head:
      "Some (u, s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and tail:
      "Some (results', t) \<in>
        set_dist
          (execute
            (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
              n) s1)"
    by (auto elim!: set_dist_bindE)
  have u_eq: "u = ()"
    by (cases u) simp
  have future_s1: "query_future_fresh s1"
    by (rule verifier_query_round_program_preserves_query_future_fresh
        [OF Suc.prems(2) head[unfolded u_eq]])
  show ?case
    by (rule Suc.IH[OF tail future_s1])
qed

lemma verifier_query_round_program_outcome:
  assumes outcome:
    "Some ((), t) \<in>
      set_dist (execute (verifier_query_round_program fr f_fl f_final as fl final) s)"
  obtains raw_idx idx chunk
  where
    "idx = index (to_nat raw_idx)"
    and "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    and "PTranscript s = chunk @ PTranscript t"
    and "PState t = foldl concat (PState s) chunk"
    and "s \<le> t"
    and "PQueryCounter t = Suc (PQueryCounter s)"
    and "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw_idx"
proof -
  from outcome obtain raw_idx s0 idx fv s1 f_out s2 s3 c_out s4 where
    rand:
      "Some (raw_idx, s0) \<in>
        set_dist (execute receive_query_index_challenge s)"
    and idx_def: "idx = index (to_nat raw_idx)"
    and query_decommit:
      "Some (fv, s1) \<in>
        set_dist (execute (mmap (check_decommit_on_query fr idx)) s0)"
    and trace_fri:
      "Some (f_out, s2) \<in>
        set_dist (execute
          (mfold (idx, hd fv, clength * scale, 1) (receive_query_commits f_fl)) s1)"
    and assert_trace:
      "Some ((), s3) \<in> set_dist (execute (assert (case f_out of (_, f_x, _, _) \<Rightarrow> f_x = f_final)) s2)"
    and comp_fri:
      "Some (c_out, s4) \<in>
        set_dist (execute
          (mfold
            (idx, cp_eval as fv (h ^ idx * shift), clength * scale, 1)
            (receive_query_commits fl)) s3)"
    and assert_comp:
      "Some ((), t) \<in> set_dist (execute (assert (case c_out of (_, x, _, _) \<Rightarrow> x = final)) s4)"
    unfolding verifier_query_round_program_def
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have rand_res:
    "s \<le> s0 \<and>
     PState s0 = PState s \<and>
     PTranscript s0 = PTranscript s \<and>
     fmlookup (HashMap s0) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw_idx"
    using receive_query_index_challenge_outcome[OF rand] .
  have rand_counter:
    "PQueryCounter s0 = Suc (PQueryCounter s)"
    using receive_query_index_challenge_counter_outcome[OF rand] by simp
  from check_decommit_on_query_outcome[OF query_decommit]
  obtain query_paths query_chunk where
    query_chunk_shape:
      "query_decommitment_transcript idx fv query_paths query_chunk"
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
    "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) ?chunk"
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
  have lookup_t: "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw_idx"
    using rand_res hash_extension_lookup[OF conjunct2[OF conjunct2[OF conjunct2[OF rand_res]]] ext_s0_t]
    by simp
  have query_count_t: "PQueryCounter t = Suc (PQueryCounter s)"
    using rand_counter query_count_s1 query_count_s2 query_count_s4 s3_eq t_eq
    by simp
  show ?thesis
    by (rule that[OF idx_def round_chunk tr_t st_t ext_s_t query_count_t lookup_t])
qed

lemma ntimes_verifier_query_rounds_outcome:
  assumes outcome:
    "Some (results, t) \<in>
      set_dist (execute
        (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n) s)"
  shows
    "\<exists>raw_idxs query_idxs query_chunks.
      length raw_idxs = n \<and>
      query_idxs = map (\<lambda>raw. index (to_nat raw)) raw_idxs \<and>
      length query_chunks = n \<and>
      PTranscript s = List.concat query_chunks @ PTranscript t \<and>
      PState t = state_after_query_chunks (PState s) query_chunks n \<and>
      s \<le> t \<and>
      PQueryCounter t = PQueryCounter s + n \<and>
      (\<forall>i < n.
        verifier_query_round_chunk (query_idxs ! i)
          (map snd f_fl) (map snd fl) (query_chunks ! i)) \<and>
      (\<forall>i < n.
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s + i)
            (state_after_query_chunks (PState s) query_chunks i)) =
          Some (raw_idxs ! i)) \<and>
      (\<forall>idx \<in> set query_idxs. idx < clength * scale)"
  using outcome
proof (induction n arbitrary: s results t)
  case 0
  then show ?case
    by (intro exI[of _ "[]"]) (simp add: state_after_query_chunks_def hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain u results' s1 where
    head:
      "Some (u, s1) \<in>
        set_dist (execute (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and tail:
      "Some (results', t) \<in>
        set_dist (execute
          (ntimes (verifier_query_round_program fr f_fl f_final as fl final) n) s1)"
    and results_eq: "results = u # results'"
    by (auto elim!: set_dist_bindE)
  have u_unit: "u = ()"
    by (cases u) simp
  from verifier_query_round_program_outcome[OF head[unfolded u_unit]]
  obtain raw idx chunk where
    idx_def: "idx = index (to_nat raw)"
    and round_chunk:
      "verifier_query_round_chunk idx (map snd f_fl) (map snd fl) chunk"
    and tr_s: "PTranscript s = chunk @ PTranscript s1"
    and st_s1: "PState s1 = foldl concat (PState s) chunk"
    and ext_s_s1: "s \<le> s1"
    and query_count_s1: "PQueryCounter s1 = Suc (PQueryCounter s)"
    and lookup_s1: "fmlookup (HashMap s1) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    by this
  from Suc.IH[OF tail] obtain raw_tail idx_tail chunk_tail where
    len_raw_tail: "length raw_tail = n"
    and idx_tail_def: "idx_tail = map (\<lambda>raw. index (to_nat raw)) raw_tail"
    and len_chunk_tail: "length chunk_tail = n"
    and tr_s1: "PTranscript s1 = List.concat chunk_tail @ PTranscript t"
    and st_t_tail:
      "PState t = state_after_query_chunks (PState s1) chunk_tail n"
    and ext_s1_t: "s1 \<le> t"
    and query_count_t: "PQueryCounter t = PQueryCounter s1 + n"
    and round_tail:
      "\<And>i. i < n \<Longrightarrow>
        verifier_query_round_chunk (idx_tail ! i)
          (map snd f_fl) (map snd fl) (chunk_tail ! i)"
    and lookup_tail:
      "\<And>i. i < n \<Longrightarrow>
        fmlookup (HashMap t)
          (QueryIndexChallenge (PQueryCounter s1 + i)
            (state_after_query_chunks (PState s1) chunk_tail i)) =
        Some (raw_tail ! i)"
    and idx_tail_bound:
      "\<forall>idx \<in> set idx_tail. idx < clength * scale"
    by blast
  let ?raws = "raw # raw_tail"
  let ?idxs = "idx # idx_tail"
  let ?chunks = "chunk # chunk_tail"
  have idxs_def: "?idxs = map (\<lambda>raw. index (to_nat raw)) ?raws"
    using idx_def idx_tail_def by simp
  have tr_all: "PTranscript s = List.concat ?chunks @ PTranscript t"
    using tr_s tr_s1 by simp
  have state_shift:
    "\<And>i. state_after_query_chunks (PState s) ?chunks (Suc i) =
      state_after_query_chunks (PState s1) chunk_tail i"
    using st_s1 unfolding state_after_query_chunks_def by simp
  have st_all:
    "PState t = state_after_query_chunks (PState s) ?chunks (Suc n)"
    using st_t_tail state_shift[of n] by simp
  have ext_s_t: "s \<le> t"
    using ext_s_s1 ext_s1_t by (rule hash_ext_trans)
  have query_count_all: "PQueryCounter t = PQueryCounter s + Suc n"
    using query_count_s1 query_count_t by simp
  have round_all:
    "\<And>i. i < Suc n \<Longrightarrow>
      verifier_query_round_chunk (?idxs ! i)
        (map snd f_fl) (map snd fl) (?chunks ! i)"
  proof -
    fix i
    assume i_bound: "i < Suc n"
    show "verifier_query_round_chunk (?idxs ! i)
        (map snd f_fl) (map snd fl) (?chunks ! i)"
    proof (cases i)
      case 0
      then show ?thesis
        using round_chunk by simp
    next
      case (Suc j)
      then show ?thesis
        using round_tail[of j] i_bound by simp
    qed
  qed
  have lookup_head_t:
    "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some raw"
    using hash_extension_lookup[OF lookup_s1 ext_s1_t] .
  have lookup_all:
    "\<And>i. i < Suc n \<Longrightarrow>
      fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s + i)
          (state_after_query_chunks (PState s) ?chunks i)) =
      Some (?raws ! i)"
  proof -
    fix i
    assume i_bound: "i < Suc n"
    show "fmlookup (HashMap t)
        (QueryIndexChallenge (PQueryCounter s + i)
          (state_after_query_chunks (PState s) ?chunks i)) =
      Some (?raws ! i)"
    proof (cases i)
      case 0
      then show ?thesis
        using lookup_head_t unfolding state_after_query_chunks_def by simp
    next
      case (Suc j)
      then show ?thesis
        using lookup_tail[of j] i_bound state_shift[of j] query_count_s1 by simp
    qed
  qed
  have idx_bound_all:
    "\<forall>idx \<in> set ?idxs. idx < clength * scale"
    using idx_tail_bound idx_def index_less_domain by auto
  show ?case
    apply (intro exI[of _ ?raws] exI[of _ ?idxs] exI[of _ ?chunks] conjI)
            apply (simp add: len_raw_tail)
           apply (rule idxs_def)
          apply (simp add: len_chunk_tail)
         apply (rule tr_all)
       apply (rule st_all)
      apply (rule ext_s_t)
     apply (rule query_count_all)
      apply (intro allI impI, rule round_all, assumption)
     apply (intro allI impI, rule lookup_all, assumption)
    using idx_bound_all by simp
qed

lemma verifier_query_round_program_preserves_past_query_lookup:
  assumes past: "j < PQueryCounter s"
    and outcome:
      "Some ((), t) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
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
            (verifier_query_round_after_index_program fr f_fl f_final as fl
              final raw) s0)"
    by (auto elim!: set_dist_bindE)
  have neq:
    "QueryIndexChallenge j x \<noteq>
      QueryIndexChallenge (PQueryCounter s) (PState s)"
    using past by auto
  have lookup_s0:
    "fmlookup (HashMap s0) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
    by (rule receive_query_index_challenge_preserves_other_lookup
        [OF rand neq])
  have lookup_t:
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s0) (QueryIndexChallenge j x)"
    by (rule verifier_query_round_after_index_program_preserves_query_lookup
        [OF tail])
  show ?thesis
    using lookup_s0 lookup_t by simp
qed

lemma ntimes_verifier_query_round_program_preserves_past_query_lookup:
  assumes past: "j < PQueryCounter s"
    and outcome:
      "Some (results, t) \<in>
        set_dist
          (execute
            (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
              n) s)"
  shows
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
  using outcome past
proof (induction n arbitrary: s results t)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems obtain u results' s1 where
    head:
      "Some (u, s1) \<in>
        set_dist
          (execute
            (verifier_query_round_program fr f_fl f_final as fl final) s)"
    and tail:
      "Some (results', t) \<in>
        set_dist
          (execute
            (ntimes (verifier_query_round_program fr f_fl f_final as fl final)
              n) s1)"
    by (auto elim!: set_dist_bindE)
  have u_eq: "u = ()"
    by (cases u) simp
  have head_pres:
    "fmlookup (HashMap s1) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
    by (rule verifier_query_round_program_preserves_past_query_lookup
        [OF Suc.prems(2) head[unfolded u_eq]])
  have counter_s1:
    "PQueryCounter s1 = Suc (PQueryCounter s)"
    using verifier_query_round_program_outcome[OF head[unfolded u_eq]]
    by blast
  have past_s1: "j < PQueryCounter s1"
    using Suc.prems(2) counter_s1 by simp
  have tail_pres:
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s1) (QueryIndexChallenge j x)"
    by (rule Suc.IH[OF tail past_s1])
  show ?case
    using head_pres tail_pres by simp
qed

lemma receive_fri_commits_outcome:
  assumes outcome: "Some ((b, r), t) \<in> set_dist (execute receive_fri_commits s)"
  shows
    "\<exists>rest.
      PTranscript s = r # rest \<and>
      PState t = concat (PState s) r \<and>
      PTranscript t = rest \<and>
      s \<le> t \<and>
      fmlookup (HashMap t) (FiatShamirChallenge (concat (PState s) r)) = Some b"
proof -
  from outcome obtain s_read where
    read_r: "Some (r, s_read) \<in> set_dist (execute read s)"
    and rand_b:
      "Some (b, t) \<in> set_dist (execute receive_random_field_element s_read)"
    unfolding receive_fri_commits_def
    by (auto elim!: set_dist_bindE)
  obtain rest where tr_s: "PTranscript s = r # rest"
  proof -
    have "PTranscript s \<noteq> []"
      using read_r unfolding read_def protocol_read_def assert_def
      by (cases "PTranscript s") (auto simp: throw_no_outcome elim!: set_dist_bindE)
    then obtain x xs where xs: "PTranscript s = x # xs"
      by (cases "PTranscript s") auto
    have r_x: "r = x"
      using read_nonempty_outcome[OF read_r xs] by simp
    show ?thesis
      using that xs r_x by auto
  qed
  have read_res:
    "r = r \<and>
     s_read = s\<lparr>PState := concat (PState s) r, PTranscript := rest\<rparr>"
    using read_nonempty_outcome[OF read_r tr_s] by simp
  have rand_res:
    "s_read \<le> t \<and>
     PState t = PState s_read \<and>
     PTranscript t = PTranscript s_read \<and>
     fmlookup (HashMap t) (FiatShamirChallenge (PState s_read)) = Some b"
    using receive_random_field_element_outcome[OF rand_b] .
  have s_read_ext: "s \<le> s_read"
    using read_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s_t: "s \<le> t"
    using s_read_ext rand_res by (meson hash_ext_trans)
  show ?thesis
    using tr_s read_res rand_res s_t by auto
qed

lemma ntimes_receive_fri_commits_outcome:
  assumes outcome:
    "Some (brs, t) \<in>
      set_dist (execute (ntimes receive_fri_commits n) s)"
  shows
    "length brs = n \<and>
     PTranscript s = map snd brs @ PTranscript t \<and>
     PState t = foldl concat (PState s) (map snd brs) \<and>
     s \<le> t \<and>
     (\<forall>i < n.
        fmlookup (HashMap t)
          (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) (map snd brs)))) =
          Some (fst (brs ! i)))"
  using outcome
proof (induction n arbitrary: s brs t)
  case 0
  then show ?case
    by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain br brs' s1 where
    head: "Some (br, s1) \<in> set_dist (execute receive_fri_commits s)"
    and tail:
      "Some (brs', t) \<in>
        set_dist (execute (ntimes receive_fri_commits n) s1)"
    and brs_eq: "brs = br # brs'"
    by (auto elim!: set_dist_bindE)
  obtain b r where br_eq: "br = (b, r)"
    by (cases br)
  from receive_fri_commits_outcome[OF head[unfolded br_eq]]
  obtain rest1 where
    tr_s: "PTranscript s = r # rest1"
    and st_s1: "PState s1 = concat (PState s) r"
    and tr_s1: "PTranscript s1 = rest1"
    and ext_head: "s \<le> s1"
    and lookup_head:
      "fmlookup (HashMap s1) (FiatShamirChallenge (concat (PState s) r)) = Some b"
    by blast
  have tail_res:
    "length brs' = n \<and>
     PTranscript s1 = map snd brs' @ PTranscript t \<and>
     PState t = foldl concat (PState s1) (map snd brs') \<and>
     s1 \<le> t \<and>
     (\<forall>i<n.
        fmlookup (HashMap t)
          (FiatShamirChallenge (foldl concat (PState s1) (take (Suc i) (map snd brs')))) =
          Some (fst (brs' ! i)))"
    using Suc.IH[OF tail] .
  have ext_s1_t: "s1 \<le> t"
    using tail_res by simp
  have lookup_head_t:
    "fmlookup (HashMap t) (FiatShamirChallenge (concat (PState s) r)) = Some b"
    using hash_extension_lookup[OF lookup_head ext_s1_t] .
  have ext_combined: "s \<le> t"
    using ext_head ext_s1_t by (meson hash_ext_trans)
  have lookups:
    "\<forall>i < Suc n.
      fmlookup (HashMap t)
        (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) (map snd brs)))) =
        Some (fst (brs ! i))"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < Suc n"
    show "fmlookup (HashMap t)
        (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) (map snd brs)))) =
        Some (fst (brs ! i))"
    proof (cases i)
      case 0
      then show ?thesis
        using lookup_head_t brs_eq br_eq by simp
    next
      case (Suc j)
      then have j_bound: "j < n"
        using i_bound by simp
      have key_eq:
        "foldl concat (PState s) (take (Suc i) (map snd brs)) =
          foldl concat (PState s1) (take (Suc j) (map snd brs'))"
        using Suc brs_eq br_eq st_s1 by simp
      show ?thesis
        using tail_res j_bound Suc brs_eq key_eq by simp
    qed
  qed
  show ?case
    using tail_res tr_s tr_s1 st_s1 ext_combined lookups brs_eq br_eq
    by simp
qed

end

end
