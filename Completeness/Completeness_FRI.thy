(*  Title:      Stark/Completeness_FRI.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Completeness_FRI
  imports Completeness_Query
begin

section \<open>Honest FRI Checks\<close>

text \<open>Honest FRI decommitment, fold, degree-halving, and final-value facts.\<close>

context verification
begin

definition fri_layer_decommitment_transcript
  where
    "fri_layer_decommitment_transcript l m i len \<equiv>
      (let idx = i mod len;
           sidx = (idx + len div 2) mod len
       in l ! idx # get_authentication_path len idx m @
          l ! sidx # get_authentication_path len sidx m)"

fun fri_decommitment_transcript
where
  "fri_decommitment_transcript idx [] = []"
| "fri_decommitment_transcript idx ((l, m) # fs) =
    fri_layer_decommitment_transcript l m idx (length l) @
      fri_decommitment_transcript (idx mod length l) fs"

lemma fri_layer_decommitment_transcript_cong:
  assumes "idx mod len = idx' mod len"
  shows
    "fri_layer_decommitment_transcript l m idx len =
      fri_layer_decommitment_transcript l m idx' len"
  using assms
  unfolding fri_layer_decommitment_transcript_def by simp

lemma fri_decommitment_transcript_cong_mod_head:
  assumes "idx mod length l = idx' mod length l"
  shows
    "fri_decommitment_transcript idx ((l, m) # fs) =
      fri_decommitment_transcript idx' ((l, m) # fs)"
proof -
  have layer_eq:
    "fri_layer_decommitment_transcript l m idx (length l) =
      fri_layer_decommitment_transcript l m idx' (length l)"
    by (rule fri_layer_decommitment_transcript_cong[OF assms])
  have tail_eq:
    "fri_decommitment_transcript (idx mod length l) fs =
      fri_decommitment_transcript (idx' mod length l) fs"
    using assms by simp
  show ?thesis
    by (simp only: fri_decommitment_transcript.simps layer_eq tail_eq)
qed

lemma mod_mod_half_power:
  fixes len idx :: nat
  assumes "len = 2 ^ Suc n"
  shows "(idx mod len) mod (len div 2) = idx mod (len div 2)"
proof -
  have half: "len div 2 = 2 ^ n"
    using assms by (simp add: power_Suc)
  have dvd_half: "len div 2 dvd len"
    using assms half by (simp add: power_Suc)
  show ?thesis
    using mod_mod_cancel[of "len div 2" len idx] dvd_half by simp
qed

lemma fri_decommitment_transcript_half_index_tail:
  assumes len_pow: "len = 2 ^ Suc n"
    and next_len: "length l = len div 2"
  shows
    "fri_decommitment_transcript (idx mod len) ((l, m) # fs) =
      fri_decommitment_transcript (idx mod (len div 2)) ((l, m) # fs)"
proof -
  have "idx mod len mod length l = idx mod (len div 2) mod length l"
    using mod_mod_half_power[OF len_pow, of idx] next_len by simp
  then show ?thesis
    by (rule fri_decommitment_transcript_cong_mod_head)
qed

definition fri_fold_value
  where
    "fri_fold_value b l i len pw \<equiv>
      ((l ! i) + (l ! ((i + len div 2) mod len))) div 2 +
        b * (((l ! i) - (l ! ((i + len div 2) mod len))) div
          (2 * ((p.h^i) * shift)^pw))"

definition fri_verifier_layer
  where
    "fri_verifier_layer b fr i x len pw \<equiv>
      do {
        xp \<leftarrow> p.read;
        xp' \<leftarrow> ntimes p.read (floor_log len);
        xn \<leftarrow> p.read;
        xn' \<leftarrow> ntimes p.read (floor_log len);
        assert (xp = x);
        ap \<leftarrow> p.check_authentication_path len i xp xp';
        assert (ap = fr);
        let sidx = (i + len div 2) mod len;
        ap \<leftarrow> p.check_authentication_path len sidx xn xn';
        assert (ap = fr);
        let gp = (xp + xn) div 2;
        let hp = (xp - xn) div (2 * ((p.h^i) * shift)^pw);
        let x = gp + b * hp;
        return (i mod (len div 2), x, len div 2, pw + pw)
      }"

lemma receive_query_commits_step_eq:
  "m \<in> set (v.receive_query_commits fl) \<Longrightarrow>
    \<exists>b fr. (b, fr) \<in> set fl \<and>
      m = (\<lambda>(i, x, len, pw). fri_verifier_layer b fr i x len pw)"
  unfolding v.receive_query_commits_def fri_verifier_layer_def
  by auto

lemma receive_query_commits_Cons:
  "v.receive_query_commits ((b, fr) # fl) =
    (\<lambda>(i, x, len, pw). fri_verifier_layer b fr i x len pw) #
      v.receive_query_commits fl"
  unfolding v.receive_query_commits_def fri_verifier_layer_def by simp

lemma receive_query_commits_nth_apply:
  assumes "j < length fl"
  shows
    "((v.receive_query_commits fl) ! j) (i, x, len, pw) =
      fri_verifier_layer (fst (fl ! j)) (snd (fl ! j)) i x len pw"
proof -
  obtain bb rr where pair: "fl ! j = (bb, rr)"
    by (cases "fl ! j")
  have nth_eq:
    "((v.receive_query_commits fl) ! j) =
      (\<lambda>(i, x, len, pw). fri_verifier_layer bb rr i x len pw)"
    using assms pair
    unfolding v.receive_query_commits_def fri_verifier_layer_def
    by simp
  show ?thesis
    by (subst nth_eq, simp add: pair)
qed

lemma receive_query_commits_zip_nth_apply:
  assumes "j < length challenges"
    and "j < length roots"
  shows
    "((v.receive_query_commits (zip challenges roots)) ! j) (i, x, len, pw) =
      fri_verifier_layer (challenges ! j) (roots ! j) i x len pw"
  using assms receive_query_commits_nth_apply[
      of j "zip challenges roots" i x len pw]
  by simp

lemma butlast_zip_suc_lengths:
  assumes "length xs = Suc n"
    and "length ys = Suc n"
  shows "butlast (zip xs ys) = take n (zip xs ys)"
  using assms by (simp add: butlast_conv_take)

lemma butlast_zip_suc_nth:
  assumes "length xs = Suc n"
    and "length ys = Suc n"
    and "j < n"
  shows "butlast (zip xs ys) ! j = (xs ! j, ys ! j)"
proof -
  have "butlast (zip xs ys) ! j = zip xs ys ! j"
    using butlast_zip_suc_lengths[OF assms(1,2)] assms(3) by simp
  also have "... = (xs ! j, ys ! j)"
    using assms by (simp add: nth_zip)
  finally show ?thesis .
qed

lemma butlast_zip_suc_drop_nth:
  assumes "length xs = Suc n"
    and "length ys = Suc n"
    and "j < n"
  shows
    "drop j (butlast (zip xs ys)) =
      (xs ! j, ys ! j) # drop (Suc j) (butlast (zip xs ys))"
proof -
  have bl_len: "length (butlast (zip xs ys)) = n"
    using butlast_zip_suc_lengths[OF assms(1,2)] assms(1,2) by simp
  have drop_eq:
    "drop j (butlast (zip xs ys)) =
      butlast (zip xs ys) ! j # drop (Suc j) (butlast (zip xs ys))"
    using Cons_nth_drop_Suc[OF assms(3)[folded bl_len], symmetric] .
  show ?thesis
    using drop_eq butlast_zip_suc_nth[OF assms] by simp
qed

lemma fri_decommitment_transcript_drop_half_index:
  assumes len_ls: "length ls = Suc n"
    and len_ms: "length ms = Suc n"
    and j_bound: "j < n"
    and len_pow: "length (ls ! j) = 2 ^ Suc N"
    and next_len: "length (ls ! Suc j) = length (ls ! j) div 2"
  shows
    "fri_decommitment_transcript (idx mod length (ls ! j))
        (drop (Suc j) (butlast (zip ls ms))) =
      fri_decommitment_transcript (idx mod (length (ls ! j) div 2))
        (drop (Suc j) (butlast (zip ls ms)))"
proof (cases "Suc j < n")
  case True
  have bl_len: "length (butlast (zip ls ms)) = n"
    using butlast_zip_suc_lengths[OF len_ls len_ms] len_ls len_ms by simp
  have drop_eq:
    "drop (Suc j) (butlast (zip ls ms)) =
      butlast (zip ls ms) ! Suc j #
        drop (Suc (Suc j)) (butlast (zip ls ms))"
    using Cons_nth_drop_Suc[OF True[folded bl_len], symmetric] .
  have nth_eq:
    "butlast (zip ls ms) ! Suc j = (ls ! Suc j, ms ! Suc j)"
    by (rule butlast_zip_suc_nth[OF len_ls len_ms True])
  show ?thesis
    unfolding drop_eq nth_eq
    by (rule fri_decommitment_transcript_half_index_tail[
        OF len_pow next_len])
next
  case False
  have suc_eq: "Suc j = n"
    using False j_bound by simp
  have bl_len: "length (butlast (zip ls ms)) = n"
    using butlast_zip_suc_lengths[OF len_ls len_ms] len_ls len_ms by simp
  then show ?thesis
    using suc_eq by simp
qed

lemma decommit_on_fri_layer_transcript:
  assumes outcome:
    "Some (x, t) \<in>
      set_dist (execute
        (do {
          let len = length l;
          let idx' = idx mod len;
          let sidx = (idx' + (len div 2)) mod len;
          p.send (l ! idx');
          mfold2 p.send (get_authentication_path len idx' m);
          p.send (l ! sidx);
          mfold2 p.send (get_authentication_path len sidx m);
          return idx'
        }) s)"
  shows
    "x = idx mod length l \<and>
     PTranscript t =
       rev (fri_layer_decommitment_transcript l m idx (length l)) @ PTranscript s"
proof -
  let ?len = "length l"
  let ?idx = "idx mod ?len"
  let ?sidx = "(?idx + (?len div 2)) mod ?len"
  from outcome[unfolded Let_def] obtain u1 u2 u3 u4 where
    send_xp: "Some ((), u1) \<in> set_dist (execute (p.send (l ! ?idx)) s)"
    and path_xp:
      "Some ((), u2) \<in>
        set_dist (execute (mfold2 p.send (get_authentication_path ?len ?idx m)) u1)"
    and send_xn: "Some ((), u3) \<in> set_dist (execute (p.send (l ! ?sidx)) u2)"
    and path_xn:
      "Some ((), u4) \<in>
        set_dist (execute (mfold2 p.send (get_authentication_path ?len ?sidx m)) u3)"
    and ret: "Some (x, t) \<in> set_dist (execute (return ?idx) u4)"
    by (auto elim!: p.set_dist_bindE)
  have x_eq: "x = ?idx"
    using ret by simp
  have t_eq: "t = u4"
    using ret by simp
  have tr_u1: "PTranscript u1 = l ! ?idx # PTranscript s"
    using p.send_outcome[OF send_xp] by simp
  have tr_u2:
    "PTranscript u2 =
      rev (get_authentication_path ?len ?idx m) @ PTranscript u1"
    using p.mfold2_send_outcome[OF path_xp] by simp
  have tr_u3: "PTranscript u3 = l ! ?sidx # PTranscript u2"
    using p.send_outcome[OF send_xn] by simp
  have tr_u4:
    "PTranscript u4 =
      rev (get_authentication_path ?len ?sidx m) @ PTranscript u3"
    using p.mfold2_send_outcome[OF path_xn] by simp
  have tr:
    "PTranscript t =
      rev (fri_layer_decommitment_transcript l m idx ?len) @ PTranscript s"
    using tr_u1 tr_u2 tr_u3 tr_u4 t_eq
    unfolding fri_layer_decommitment_transcript_def
    by (simp add: Let_def)
	  show ?thesis
	    using x_eq tr by simp
	qed

lemma decommit_on_fri_layer_state:
  assumes outcome:
    "Some (x, t) \<in>
      set_dist (execute
        (do {
          let len = length l;
          let idx' = idx mod len;
          let sidx = (idx' + (len div 2)) mod len;
          p.send (l ! idx');
          mfold2 p.send (get_authentication_path len idx' m);
          p.send (l ! sidx);
          mfold2 p.send (get_authentication_path len sidx m);
          return idx'
        }) s)"
  shows
    "PState t =
      foldl concat (PState s)
        (fri_layer_decommitment_transcript l m idx (length l))"
proof -
  let ?len = "length l"
  let ?idx = "idx mod ?len"
  let ?sidx = "(?idx + (?len div 2)) mod ?len"
  from outcome[unfolded Let_def] obtain u1 u2 u3 u4 where
    send_xp: "Some ((), u1) \<in> set_dist (execute (p.send (l ! ?idx)) s)"
    and path_xp:
      "Some ((), u2) \<in>
        set_dist (execute (mfold2 p.send (get_authentication_path ?len ?idx m)) u1)"
    and send_xn: "Some ((), u3) \<in> set_dist (execute (p.send (l ! ?sidx)) u2)"
    and path_xn:
      "Some ((), u4) \<in>
        set_dist (execute (mfold2 p.send (get_authentication_path ?len ?sidx m)) u3)"
    and ret: "Some (x, t) \<in> set_dist (execute (return ?idx) u4)"
    by (auto elim!: p.set_dist_bindE)
  have t_eq: "t = u4"
    using ret by simp
  have st_u1: "PState u1 = concat (PState s) (l ! ?idx)"
    using p.send_outcome[OF send_xp] by simp
  have st_u2:
    "PState u2 =
      foldl concat (concat (PState s) (l ! ?idx))
        (get_authentication_path ?len ?idx m)"
    using p.mfold2_send_outcome[OF path_xp] st_u1 by simp
  have st_u3: "PState u3 = concat (PState u2) (l ! ?sidx)"
    using p.send_outcome[OF send_xn] by simp
  have st_u4:
    "PState u4 =
      foldl concat (concat (PState u2) (l ! ?sidx))
        (get_authentication_path ?len ?sidx m)"
    using p.mfold2_send_outcome[OF path_xn] st_u3 by simp
  show ?thesis
    using st_u2 st_u4 t_eq
    unfolding fri_layer_decommitment_transcript_def
    by (simp add: Let_def)
qed

lemma decommit_on_fri_layers_mfold_transcript:
  assumes outcome:
    "Some (idx', t) \<in>
      set_dist (execute
        (mfold idx
          (p.decommit_on_fri_layers fs)) s)"
  shows
    "PTranscript t =
      rev (fri_decommitment_transcript idx fs) @ PTranscript s"
  using outcome
proof (induction fs arbitrary: idx idx' s t)
  case Nil
  then have "t = s"
    unfolding p.decommit_on_fri_layers_def by simp
  then show ?case
    by simp
next
  case (Cons pair fs)
  obtain l m where pair_eq: "pair = (l, m)"
    by (cases pair)
  from Cons.prems obtain idx1 u where
    head:
      "Some (idx1, u) \<in>
        set_dist (execute
          ((\<lambda>(l, m) idx. do {
              let len = length l;
              let idx' = idx mod len;
              let sidx = (idx' + (len div 2)) mod len;
              p.send (l ! idx');
              mfold2 p.send (get_authentication_path len idx' m);
              p.send (l ! sidx);
              mfold2 p.send (get_authentication_path len sidx m);
              return idx'
            }) pair idx) s)"
    and tail:
      "Some (idx', t) \<in>
        set_dist (execute
          (mfold idx1 (p.decommit_on_fri_layers fs)) u)"
    unfolding p.decommit_on_fri_layers_def
    by (auto elim!: p.set_dist_bindE)
  have head':
    "Some (idx1, u) \<in>
      set_dist (execute
        (do {
          let len = length l;
          let idx' = idx mod len;
          let sidx = (idx' + (len div 2)) mod len;
          p.send (l ! idx');
          mfold2 p.send (get_authentication_path len idx' m);
          p.send (l ! sidx);
          mfold2 p.send (get_authentication_path len sidx m);
          return idx'
        }) s)"
    using head unfolding pair_eq by simp
  have head_res:
    "idx1 = idx mod length l \<and>
     PTranscript u =
       rev (fri_layer_decommitment_transcript l m idx (length l)) @ PTranscript s"
    by (rule decommit_on_fri_layer_transcript[OF head'])
  have tail_tr:
    "PTranscript t =
      rev (fri_decommitment_transcript idx1 fs) @ PTranscript u"
    using Cons.IH[OF tail] .
	  show ?case
	    using head_res tail_tr unfolding pair_eq by simp
	qed

lemma decommit_on_fri_layers_mfold_state:
  assumes outcome:
    "Some (idx', t) \<in>
      set_dist (execute
        (mfold idx
          (p.decommit_on_fri_layers fs)) s)"
  shows
    "PState t =
      foldl concat (PState s) (fri_decommitment_transcript idx fs)"
  using outcome
proof (induction fs arbitrary: idx idx' s t)
  case Nil
  then show ?case
    unfolding p.decommit_on_fri_layers_def by simp
next
  case (Cons pair fs)
  obtain l m where pair_eq: "pair = (l, m)"
    by (cases pair)
  from Cons.prems obtain idx1 u where
    head:
      "Some (idx1, u) \<in>
        set_dist (execute
          ((\<lambda>(l, m) idx. do {
              let len = length l;
              let idx' = idx mod len;
              let sidx = (idx' + (len div 2)) mod len;
              p.send (l ! idx');
              mfold2 p.send (get_authentication_path len idx' m);
              p.send (l ! sidx);
              mfold2 p.send (get_authentication_path len sidx m);
              return idx'
            }) pair idx) s)"
    and tail:
      "Some (idx', t) \<in>
        set_dist (execute
          (mfold idx1 (p.decommit_on_fri_layers fs)) u)"
    unfolding p.decommit_on_fri_layers_def
    by (auto elim!: p.set_dist_bindE)
  have head':
    "Some (idx1, u) \<in>
      set_dist (execute
        (do {
          let len = length l;
          let idx' = idx mod len;
          let sidx = (idx' + (len div 2)) mod len;
          p.send (l ! idx');
          mfold2 p.send (get_authentication_path len idx' m);
          p.send (l ! sidx);
          mfold2 p.send (get_authentication_path len sidx m);
          return idx'
        }) s)"
    using head unfolding pair_eq by simp
  have idx1_eq: "idx1 = idx mod length l"
    using decommit_on_fri_layer_transcript[OF head'] by simp
  have head_state:
    "PState u =
      foldl concat (PState s)
        (fri_layer_decommitment_transcript l m idx (length l))"
    by (rule decommit_on_fri_layer_state[OF head'])
  have tail_state:
    "PState t =
      foldl concat (PState u) (fri_decommitment_transcript idx1 fs)"
    using Cons.IH[OF tail] .
  show ?case
    using idx1_eq head_state tail_state unfolding pair_eq by simp
qed

lemma prover_query_round_transcript:
  assumes outcome:
    "Some (x, t) \<in> set_dist (execute (prover_query_round f_merkle f_ls f_ms ls ms) s)"
  obtains idx where
    "PTranscript t =
      rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip ls ms))) @
      rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip f_ls f_ms))) @
      rev (query_decommitment_transcript (p.index (to_nat idx)) f_merkle) @
      PTranscript s"
proof (rule prover_query_round_outcomeE[OF outcome])
  fix idx s1 qouts s2 f_fri_idx s3 fri_idx
  assume
    rand: "Some (idx, s1) \<in> set_dist (execute p.receive_query_index_challenge s)"
    and query:
      "Some (qouts, s2) \<in>
        set_dist (execute
          (mmap (p.decommit_on_query (p.index (to_nat idx)) f_merkle)) s1)"
    and trace_fri:
      "Some (f_fri_idx, s3) \<in>
        set_dist (execute
          (mfold (p.index (to_nat idx))
            (p.decommit_on_fri_layers (butlast (zip f_ls f_ms)))) s2)"
    and fri:
      "Some (fri_idx, t) \<in>
        set_dist (execute
          (mfold (p.index (to_nat idx))
            (p.decommit_on_fri_layers (butlast (zip ls ms)))) s3)"
    and unit: "x = ()"
  have tr_s1: "PTranscript s1 = PTranscript s"
    using receive_query_index_challenge_preserves_transcript[OF rand] .
  have tr_s2:
    "PTranscript s2 =
      rev (query_decommitment_transcript (p.index (to_nat idx)) f_merkle) @
      PTranscript s1"
    using decommit_on_query_mmap_transcript[OF query] .
  have tr_s3:
    "PTranscript s3 =
      rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip f_ls f_ms))) @
      PTranscript s2"
    using decommit_on_fri_layers_mfold_transcript[OF trace_fri] .
  have tr_t:
    "PTranscript t =
      rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip ls ms))) @
      PTranscript s3"
    using decommit_on_fri_layers_mfold_transcript[OF fri] .
  show ?thesis
    by (rule that[of idx]) (use tr_s1 tr_s2 tr_s3 tr_t in simp)
qed

lemma prover_query_round_lookup_transcript:
  assumes outcome:
    "Some (x, t) \<in> set_dist (execute (prover_query_round f_merkle f_ls f_ms ls ms) s)"
  obtains idx where
    "x = ()"
    "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some idx"
    "PTranscript t =
      rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip ls ms))) @
      rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip f_ls f_ms))) @
      rev (query_decommitment_transcript (p.index (to_nat idx)) f_merkle) @
      PTranscript s"
    "s \<le> t"
proof (rule prover_query_round_outcomeE[OF outcome])
  fix idx s1 qouts s2 f_fri_idx s3 fri_idx
  assume rand: "Some (idx, s1) \<in> set_dist (execute p.receive_query_index_challenge s)"
    and query:
      "Some (qouts, s2) \<in>
        set_dist (execute
          (mmap (p.decommit_on_query (p.index (to_nat idx)) f_merkle)) s1)"
    and trace_fri:
      "Some (f_fri_idx, s3) \<in>
        set_dist (execute
          (mfold (p.index (to_nat idx))
            (p.decommit_on_fri_layers (butlast (zip f_ls f_ms)))) s2)"
    and fri:
      "Some (fri_idx, t) \<in>
        set_dist (execute
          (mfold (p.index (to_nat idx))
            (p.decommit_on_fri_layers (butlast (zip ls ms)))) s3)"
    and x_unit: "x = ()"
  have rand_res:
    "s \<le> s1 \<and>
     PState s1 = PState s \<and>
     PTranscript s1 = PTranscript s \<and>
     fmlookup (HashMap s1) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some idx"
    using p.receive_query_index_challenge_outcome[OF rand] by simp
  have query_ext: "s1 \<le> s2"
    by (rule mmap_hash_extends[OF query])
      (rule decommit_on_query_step_hash_extends)
  have trace_fri_ext: "s2 \<le> s3"
    by (rule mfold_hash_extends[OF trace_fri])
      (rule decommit_on_fri_layers_step_hash_extends)
  have fri_ext: "s3 \<le> t"
    by (rule mfold_hash_extends[OF fri])
      (rule decommit_on_fri_layers_step_hash_extends)
  have s_t: "s \<le> t"
    using rand_res query_ext trace_fri_ext fri_ext by (meson p.hash_ext_trans)
  have s1_t: "s1 \<le> t"
    using query_ext trace_fri_ext fri_ext by (meson p.hash_ext_trans)
  have lookup_s1: "fmlookup (HashMap s1) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some idx"
    using rand_res by simp
  have lookup_t: "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some idx"
    by (rule p.hash_extension_lookup[OF lookup_s1 s1_t])
  have tr_s2:
    "PTranscript s2 =
      rev (query_decommitment_transcript (p.index (to_nat idx)) f_merkle) @
      PTranscript s1"
    by (rule decommit_on_query_mmap_transcript[OF query])
  have tr_s3:
    "PTranscript s3 =
      rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip f_ls f_ms))) @
      PTranscript s2"
    by (rule decommit_on_fri_layers_mfold_transcript[OF trace_fri])
  have tr_t:
    "PTranscript t =
      rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip ls ms))) @
      PTranscript s3"
    by (rule decommit_on_fri_layers_mfold_transcript[OF fri])
		  show ?thesis
		    by (rule that[OF x_unit lookup_t])
		      (use rand_res tr_s2 tr_s3 tr_t s_t in simp_all)
		qed

lemma prover_query_round_lookup_state_transcript:
  assumes outcome:
    "Some (x, t) \<in> set_dist (execute (prover_query_round f_merkle f_ls f_ms ls ms) s)"
  obtains idx where
    "x = ()"
    "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some idx"
    "PState t =
      foldl concat (PState s)
        (query_decommitment_transcript (p.index (to_nat idx)) f_merkle @
          fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip f_ls f_ms)) @
          fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip ls ms)))"
    "PTranscript t =
      rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip ls ms))) @
      rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip f_ls f_ms))) @
      rev (query_decommitment_transcript (p.index (to_nat idx)) f_merkle) @
      PTranscript s"
    "s \<le> t"
proof (rule prover_query_round_outcomeE[OF outcome])
  fix idx s1 qouts s2 f_fri_idx s3 fri_idx
  assume rand: "Some (idx, s1) \<in> set_dist (execute p.receive_query_index_challenge s)"
    and query:
      "Some (qouts, s2) \<in>
        set_dist (execute
          (mmap (p.decommit_on_query (p.index (to_nat idx)) f_merkle)) s1)"
    and trace_fri:
      "Some (f_fri_idx, s3) \<in>
        set_dist (execute
          (mfold (p.index (to_nat idx))
            (p.decommit_on_fri_layers (butlast (zip f_ls f_ms)))) s2)"
    and fri:
      "Some (fri_idx, t) \<in>
        set_dist (execute
          (mfold (p.index (to_nat idx))
            (p.decommit_on_fri_layers (butlast (zip ls ms)))) s3)"
    and x_unit: "x = ()"
  have rand_res:
    "s \<le> s1 \<and>
     PState s1 = PState s \<and>
     PTranscript s1 = PTranscript s \<and>
     fmlookup (HashMap s1) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some idx"
    using p.receive_query_index_challenge_outcome[OF rand] by simp
  have query_ext: "s1 \<le> s2"
    by (rule mmap_hash_extends[OF query])
      (rule decommit_on_query_step_hash_extends)
  have trace_fri_ext: "s2 \<le> s3"
    by (rule mfold_hash_extends[OF trace_fri])
      (rule decommit_on_fri_layers_step_hash_extends)
  have fri_ext: "s3 \<le> t"
    by (rule mfold_hash_extends[OF fri])
      (rule decommit_on_fri_layers_step_hash_extends)
  have s_t: "s \<le> t"
    using rand_res query_ext trace_fri_ext fri_ext by (meson p.hash_ext_trans)
  have s1_t: "s1 \<le> t"
    using query_ext trace_fri_ext fri_ext by (meson p.hash_ext_trans)
  have lookup_s1: "fmlookup (HashMap s1) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some idx"
    using rand_res by simp
  have lookup_t: "fmlookup (HashMap t) (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some idx"
    by (rule p.hash_extension_lookup[OF lookup_s1 s1_t])
  have query_state:
    "PState s2 =
      foldl concat (PState s)
        (query_decommitment_transcript (p.index (to_nat idx)) f_merkle)"
    using decommit_on_query_mmap_state[OF query] rand_res by simp
  have trace_fri_state:
    "PState s3 =
      foldl concat (PState s2)
        (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip f_ls f_ms)))"
    using decommit_on_fri_layers_mfold_state[OF trace_fri] .
  have fri_state:
    "PState t =
      foldl concat (PState s3)
        (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip ls ms)))"
    using decommit_on_fri_layers_mfold_state[OF fri] .
  have state_t:
    "PState t =
      foldl concat (PState s)
        (query_decommitment_transcript (p.index (to_nat idx)) f_merkle @
          fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip f_ls f_ms)) @
          fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip ls ms)))"
    using query_state trace_fri_state fri_state by simp
  have tr_s2:
    "PTranscript s2 =
      rev (query_decommitment_transcript (p.index (to_nat idx)) f_merkle) @
      PTranscript s1"
    by (rule decommit_on_query_mmap_transcript[OF query])
  have tr_s3:
    "PTranscript s3 =
      rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip f_ls f_ms))) @
      PTranscript s2"
    by (rule decommit_on_fri_layers_mfold_transcript[OF trace_fri])
  have tr_t:
    "PTranscript t =
      rev (fri_decommitment_transcript (p.index (to_nat idx)) (butlast (zip ls ms))) @
      PTranscript s3"
    by (rule decommit_on_fri_layers_mfold_transcript[OF fri])
  show ?thesis
    by (rule that[OF x_unit lookup_t state_t])
      (use rand_res tr_s2 tr_s3 tr_t s_t in simp_all)
qed

lemma prover_fri_decommitment_transcript_in_replay_state:
  assumes fri_decommit:
    "Some (fri_idx, s9) \<in>
      set_dist (execute
        (mfold idx' (p.decommit_on_fri_layers (butlast (zip ls ms)))) s8)"
    and prover_state_eq: "prover_state = s9"
    and replay: "replay_state = verifier_replay_state prover_state"
  shows
    "PTranscript replay_state =
      rev (PTranscript s8) @
        fri_decommitment_transcript idx' (butlast (zip ls ms))"
proof -
  have s9_tr:
    "PTranscript s9 =
      rev (fri_decommitment_transcript idx' (butlast (zip ls ms))) @
        PTranscript s8"
    by (rule decommit_on_fri_layers_mfold_transcript[OF fri_decommit])
  show ?thesis
    using s9_tr prover_state_eq replay
    unfolding verifier_replay_state_def by simp
qed

lemma prover_query_fri_decommitment_transcript_in_replay_state:
  assumes final_send:
    "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    and random_idx:
      "Some (idx, s7) \<in> set_dist (execute p.receive_query_index_challenge s_final)"
    and query_decommit:
      "Some (qouts, s8) \<in>
        set_dist (execute (mmap (p.decommit_on_query idx' f_merkle)) s7)"
    and fri_decommit:
      "Some (fri_idx, s9) \<in>
        set_dist (execute
          (mfold idx' (p.decommit_on_fri_layers (butlast (zip ls ms)))) s8)"
    and prover_state_eq: "prover_state = s9"
    and replay: "replay_state = verifier_replay_state prover_state"
  shows
    "PTranscript replay_state =
      rev (PTranscript s6) @ [hd (last ls)] @
        query_decommitment_transcript idx' f_merkle @
        fri_decommitment_transcript idx' (butlast (zip ls ms))"
proof -
  have final_tr:
    "PTranscript s_final = hd (last ls) # PTranscript s6"
    using p.send_outcome[OF final_send] by simp
  have s7_tr: "PTranscript s7 = PTranscript s_final"
    using receive_query_index_challenge_preserves_transcript[OF random_idx] .
  have s8_tr:
    "PTranscript s8 =
      rev (query_decommitment_transcript idx' f_merkle) @ PTranscript s7"
    using decommit_on_query_mmap_transcript[OF query_decommit] .
  have replay_tr:
    "PTranscript replay_state =
      rev (PTranscript s8) @
        fri_decommitment_transcript idx' (butlast (zip ls ms))"
    by (rule prover_fri_decommitment_transcript_in_replay_state[
        OF fri_decommit prover_state_eq replay])
  show ?thesis
    using replay_tr s8_tr s7_tr final_tr by simp
qed

lemma honest_query_prefix_initial_fri_value:
  assumes htv: "honest_trace_valid"
    and create_f:
      "Some (f_merkle, s1) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and send_f:
      "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
    and alphas:
      "Some (as, s3) \<in>
        set_dist (execute
          (mmap (replicate (length spec)
            (do {
              a \<leftarrow> p.receive_alpha_challenge;
              p.send a;
              return a
            }))) s2)"
    and cp'_def: "cp' = p.cp as p.f_powers"
    and send_degree:
      "Some ((), s4) \<in> set_dist (execute (p.send (of_nat (degree cp'))) s3)"
    and create_cp:
      "Some (cp_merkle, s5) \<in> set_dist (execute (p.create (p.cp_eval as)) s4)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.fri_commit nrounds [cp'] [p.eval_domain] [p.cp_eval as] [cp_merkle]) s5)"
    and final_send:
      "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    and random_idx:
      "Some (idx, s7) \<in> set_dist (execute p.receive_query_index_challenge s_final)"
    and idx_def: "idx' = p.index (to_nat idx)"
    and query_decommit:
      "Some (qouts, s8) \<in>
        set_dist (execute (mmap (p.decommit_on_query idx' f_merkle)) s7)"
    and fri_decommit:
      "Some (fri_idx, s9) \<in>
        set_dist (execute
          (mfold idx' (p.decommit_on_fri_layers (butlast (zip ls ms)))) s8)"
    and prover_state_eq: "prover_state = s9"
    and replay: "replay_state = verifier_replay_state prover_state"
    and outcome:
      "Some ((fr, as', dg, fl, final, idxv, fv), t) \<in>
        set_dist (execute
          (do {
            fr \<leftarrow> p.read;
            as' \<leftarrow> mmap (replicate (length spec)
              (do {
                a0 \<leftarrow> p.receive_alpha_challenge;
                let a0' = a0;
                a1 \<leftarrow> p.read;
                let a1' = a1;
                assert (a0' = a1');
                return a1'
              }));
            dg \<leftarrow> p.read;
            assert (to_nat dg \<le> p.maxDegree);
            fl \<leftarrow> ntimes v.receive_fri_commits nrounds;
            final \<leftarrow> p.read;
            idxv \<leftarrow> p.receive_query_index_challenge;
            let idxv' = p.index (to_nat idxv);
            fv \<leftarrow> mmap (v.check_decommit_on_query fr idxv');
            return (fr, as', dg, fl, final, idxv, fv)
          }) replay_state)"
  shows
    "v.cp_eval as' fv (p.h ^ idx' * shift) =
      poly (p.cp as p.f_powers) (p.h ^ idx' * shift)"
proof -
  have replay_values:
    "as' = as \<and>
     idxv = idx \<and>
     fv = map (\<lambda>i. p.f_eval ! i) (p.powers_scaled idx')"
    using honest_root_alpha_degree_fri_final_query_from_prover_outcome[
      OF htv create_f send_f alphas cp'_def send_degree create_cp fri
        final_send random_idx idx_def query_decommit fri_decommit
        prover_state_eq replay outcome]
    by blast
  have cp:
    "v.cp_eval as (map (\<lambda>i. p.f_eval ! i) (p.powers_scaled (p.index (to_nat idx))))
        (p.h ^ p.index (to_nat idx) * shift) =
      poly (p.cp as p.f_powers) (p.h ^ p.index (to_nat idx) * shift)"
    by (rule honest_query_cp_value[OF htv])
  show ?thesis
    using replay_values idx_def cp by simp
qed

lemma honest_query_prefix_leaves_fri_decommitment_transcript:
  assumes htv: "honest_trace_valid"
    and create_f:
      "Some (f_merkle, s1) \<in>
        set_dist (execute (p.create p.f_eval) init_state)"
    and send_f:
      "Some ((), s2) \<in> set_dist (execute (p.send (value f_merkle)) s1)"
    and alphas:
      "Some (as, s3) \<in>
        set_dist (execute
          (mmap (replicate (length spec)
            (do {
              a \<leftarrow> p.receive_alpha_challenge;
              p.send a;
              return a
            }))) s2)"
    and cp'_def: "cp' = p.cp as p.f_powers"
    and send_degree:
      "Some ((), s4) \<in> set_dist (execute (p.send (of_nat (degree cp'))) s3)"
    and create_cp:
      "Some (cp_merkle, s5) \<in> set_dist (execute (p.create (p.cp_eval as)) s4)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.fri_commit nrounds [cp'] [p.eval_domain] [p.cp_eval as] [cp_merkle]) s5)"
    and final_send:
      "Some ((), s_final) \<in> set_dist (execute (p.send (hd (last ls))) s6)"
    and random_idx:
      "Some (idx, s7) \<in> set_dist (execute p.receive_query_index_challenge s_final)"
    and idx_def: "idx' = p.index (to_nat idx)"
    and query_decommit:
      "Some (qouts, s8) \<in>
        set_dist (execute (mmap (p.decommit_on_query idx' f_merkle)) s7)"
    and fri_decommit:
      "Some (fri_idx, s9) \<in>
        set_dist (execute
          (mfold idx' (p.decommit_on_fri_layers (butlast (zip ls ms)))) s8)"
    and prover_state_eq: "prover_state = s9"
    and replay: "replay_state = verifier_replay_state prover_state"
    and outcome:
      "Some ((fr, as', dg, fl, final, idxv, fv), t) \<in>
        set_dist (execute
          (do {
            fr \<leftarrow> p.read;
            as' \<leftarrow> mmap (replicate (length spec)
              (do {
                a0 \<leftarrow> p.receive_alpha_challenge;
                let a0' = a0;
                a1 \<leftarrow> p.read;
                let a1' = a1;
                assert (a0' = a1');
                return a1'
              }));
            dg \<leftarrow> p.read;
            assert (to_nat dg \<le> p.maxDegree);
            fl \<leftarrow> ntimes v.receive_fri_commits nrounds;
            final \<leftarrow> p.read;
            idxv \<leftarrow> p.receive_query_index_challenge;
            let idxv' = p.index (to_nat idxv);
            fv \<leftarrow> mmap (v.check_decommit_on_query fr idxv');
            return (fr, as', dg, fl, final, idxv, fv)
          }) replay_state)"
  shows "PTranscript t = fri_decommitment_transcript idx' (butlast (zip ls ms))"
proof -
  from honest_root_alpha_degree_fri_final_query_from_prover_outcome[
      OF htv create_f send_f alphas cp'_def send_degree create_cp fri
        final_send random_idx idx_def query_decommit fri_decommit
        prover_state_eq replay outcome]
  obtain roots challenges rest where
    len_roots: "length roots = nrounds"
    and replay_prefix:
      "PTranscript replay_state =
        value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
          roots @ [hd (last ls)] @
          query_decommitment_transcript idx' f_merkle @ rest"
    and t_tr: "PTranscript t = rest"
    by blast
  have root_alpha_tr:
    "length as = length spec \<and>
     PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
    by (rule prover_root_alpha_degree_transcript[
        OF create_f send_f alphas cp'_def send_degree])
  from fri_commit_replay_data[OF fri] obtain roots0 challenges0 where
    len_roots0: "length roots0 = nrounds"
    and tr_s6: "PTranscript s6 = rev roots0 @ PTranscript s5"
    by blast
  have tr_s5: "PTranscript s5 = PTranscript s4"
    using create_preserves_transcript[OF create_cp] .
  have replay_fri_suffix:
    "PTranscript replay_state =
      value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))] @
        roots0 @ [hd (last ls)] @
        query_decommitment_transcript idx' f_merkle @
        fri_decommitment_transcript idx' (butlast (zip ls ms))"
    using prover_query_fri_decommitment_transcript_in_replay_state[
        OF final_send random_idx query_decommit fri_decommit prover_state_eq replay]
      tr_s6 tr_s5 root_alpha_tr cp'_def
    by simp
  let ?A = "value f_merkle # as @ [of_nat (degree (p.cp as p.f_powers))]"
  let ?B = "[hd (last ls)] @ query_decommitment_transcript idx' f_merkle"
  have eq:
    "?A @ roots @ ?B @ rest =
      ?A @ roots0 @ ?B @
        fri_decommitment_transcript idx' (butlast (zip ls ms))"
    using replay_prefix replay_fri_suffix by simp
  have after_A:
    "roots @ ?B @ rest =
      roots0 @ ?B @ fri_decommitment_transcript idx' (butlast (zip ls ms))"
    using arg_cong[OF eq, of "\<lambda>xs. drop (length ?A) xs"] by simp
  have after_roots:
    "?B @ rest =
      ?B @ fri_decommitment_transcript idx' (butlast (zip ls ms))"
    using arg_cong[OF after_A, of "\<lambda>xs. drop nrounds xs"]
      len_roots len_roots0 by simp
  have "rest = fri_decommitment_transcript idx' (butlast (zip ls ms))"
    using arg_cong[OF after_roots, of "\<lambda>xs. drop (length ?B) xs"] by simp
  then show ?thesis
    using t_tr by simp
qed

lemma created_tree_get_authentication_path_len:
  assumes created: "p.created_tree xs r s0"
    and len: "length xs = 2 ^ n"
    and i_bound: "i < length xs"
  shows "length (get_authentication_path (length xs) i r) = floor_log (length xs)"
  using created len i_bound
proof (induction n arbitrary: xs r i)
  case 0
  then obtain x where xs_eq: "xs = [x]"
    by (cases xs) auto
  then obtain h where r_eq: "r = \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>"
    using "0.prems"(1)
    by (auto simp: p.created_tree_def protocol_created_tree_def
        protocol_merkle.created_tree.simps)
  show ?case
    unfolding xs_eq r_eq by (simp add: floor_log_Suc_zero)
next
  case (Suc n)
  let ?m = "2 ^ n"
  let ?lxs = "take ?m xs"
  let ?rxs = "drop ?m xs"
  have len_xs: "length xs = 2 * ?m"
    using Suc.prems(2) by simp
  have mid: "length xs div 2 = ?m"
    using len_xs by simp
  obtain a b cs where xs_cons: "xs = a # b # cs"
    using len_xs by (cases xs; cases "tl xs") auto
  have m_eq: "?m = Suc (length cs div 2)"
    using mid unfolding xs_cons by simp
  have take_eq: "?lxs = a # take (length cs div 2) (b # cs)"
    unfolding xs_cons m_eq by simp
  have drop_eq: "?rxs = drop (length cs div 2) (b # cs)"
    unfolding xs_cons m_eq by simp
  have created_raw:
    "protocol_merkle.created_tree (map MerkleLeaf xs) r s0"
    using Suc.prems(1)
    unfolding p.created_tree_def protocol_created_tree_def .
  have raw_left_eq:
    "MerkleLeaf a #
        take (length cs div 2) (MerkleLeaf b # map MerkleLeaf cs) =
      map MerkleLeaf (a # take (length cs div 2) (b # cs))"
    by (metis list.simps(9) take_map)
  have raw_right_eq:
    "drop (length cs div 2) (MerkleLeaf b # map MerkleLeaf cs) =
      map MerkleLeaf (drop (length cs div 2) (b # cs))"
    by (metis list.simps(9) drop_map)
  from created_raw obtain l h rr where
    r_eq: "r = \<langle>l, h, rr\<rangle>"
    and l_created_raw0:
      "protocol_merkle.created_tree
        (MerkleLeaf a #
          take (length cs div 2) (MerkleLeaf b # map MerkleLeaf cs)) l s0"
    and r_created_raw0:
      "protocol_merkle.created_tree
        (drop (length cs div 2) (MerkleLeaf b # map MerkleLeaf cs)) rr s0"
    unfolding xs_cons
    by (auto simp: protocol_merkle.created_tree.simps Let_def)
  have l_created_raw:
    "protocol_merkle.created_tree
      (map MerkleLeaf (a # take (length cs div 2) (b # cs))) l s0"
    using l_created_raw0 unfolding raw_left_eq .
  have r_created_raw:
    "protocol_merkle.created_tree
      (map MerkleLeaf (drop (length cs div 2) (b # cs))) rr s0"
    using r_created_raw0 unfolding raw_right_eq .
  have l_created': "p.created_tree (a # take (length cs div 2) (b # cs)) l s0"
    using l_created_raw
    unfolding p.created_tree_def protocol_created_tree_def .
  have r_created': "p.created_tree (drop (length cs div 2) (b # cs)) rr s0"
    using r_created_raw
    unfolding p.created_tree_def protocol_created_tree_def .
  have l_created: "p.created_tree ?lxs l s0"
    using l_created' unfolding take_eq .
  have r_created: "p.created_tree ?rxs rr s0"
    using r_created' unfolding drop_eq .
  have len_l: "length ?lxs = 2 ^ n"
    using len_xs by simp
  have len_r: "length ?rxs = 2 ^ n"
    using len_xs by simp
  have lgth_ge: "2 \<le> length xs"
    using len_xs by simp
  have floor_eq: "floor_log (length xs) = Suc (floor_log (length xs div 2))"
    using floor_log_rec[OF lgth_ge] .
  show ?case
  proof (cases "i < ?m")
    case True
    have i_l: "i < length ?lxs"
      using True len_l by simp
    have left_len:
      "length (get_authentication_path (length ?lxs) i l) =
        floor_log (length ?lxs)"
      by (rule Suc.IH[OF l_created len_l i_l])
    have left_len':
      "length (get_authentication_path ?m i l) = floor_log ?m"
      using left_len len_l by simp
    have "length (get_authentication_path (length xs) i r) =
      Suc (floor_log ?m)"
      using True left_len' unfolding r_eq
      by (simp add: mid len_xs)
    then show ?thesis
      using floor_eq mid len_l by simp
  next
    case False
    have i_ge: "?m \<le> i"
      using False by simp
    have i_r: "i - ?m < length ?rxs"
      using Suc.prems(3) len_xs i_ge by simp
    have right_len:
      "length (get_authentication_path (length ?rxs) (i - ?m) rr) =
        floor_log (length ?rxs)"
      by (rule Suc.IH[OF r_created len_r i_r])
    have right_len':
      "length (get_authentication_path ?m (i - ?m) rr) = floor_log ?m"
      using right_len len_r by simp
    have "length (get_authentication_path (length xs) i r) =
      Suc (floor_log ?m)"
      using False right_len' unfolding r_eq
      by (simp add: mid len_xs)
    then show ?thesis
      using floor_eq mid len_r by simp
  qed
qed

lemma honest_fri_layer_decommitment_no_failure:
  assumes created: "p.created_tree l m s0"
    and len_eq: "len = length l"
    and len_pow: "length l = 2 ^ n"
    and i_bound: "i < len"
    and x_eq: "x = l ! i"
    and ext: "s0 \<le> s"
    and path_i:
      "length (get_authentication_path len i m) = floor_log len"
    and path_s:
      "length (get_authentication_path len ((i + len div 2) mod len) m) =
        floor_log len"
    and root: "fr = value m"
  shows
    "None \<notin> dom (dist (execute
      (do {
        xp \<leftarrow> p.read;
        xp' \<leftarrow> ntimes p.read (floor_log len);
        xn \<leftarrow> p.read;
        xn' \<leftarrow> ntimes p.read (floor_log len);
        assert (xp = x);
        ap \<leftarrow> p.check_authentication_path len i xp xp';
        assert (ap = fr);
        let sidx = (i + len div 2) mod len;
        ap \<leftarrow> p.check_authentication_path len sidx xn xn';
        assert (ap = fr);
        let gp = (xp + xn) div 2;
        let hp = (xp - xn) div (2 * ((p.h^i) * shift)^pw);
        let x = gp + b * hp;
        return (i mod (len div 2), x, len div 2, pw + pw)
      })
      (s\<lparr>PTranscript := fri_layer_decommitment_transcript l m i len @ rest\<rparr>)))"
proof -
  let ?sidx = "(i + len div 2) mod len"
  let ?path_i = "get_authentication_path len i m"
  let ?path_s = "get_authentication_path len ?sidx m"
  let ?prefix =
    "do {
      xp \<leftarrow> p.read;
      xp' \<leftarrow> ntimes p.read (floor_log len);
      xn \<leftarrow> p.read;
      xn' \<leftarrow> ntimes p.read (floor_log len);
      return (xp, xp', xn, xn')
    }"
  let ?start =
    "s\<lparr>PTranscript := l ! i # ?path_i @ l ! ?sidx # ?path_s @ rest\<rparr>"
  have len_pos: "0 < len"
    using i_bound by simp
  have sidx_bound: "?sidx < length l"
    using len_pos unfolding len_eq by simp
  have start_eq:
    "s\<lparr>PTranscript := fri_layer_decommitment_transcript l m i len @ rest\<rparr> =
      ?start"
    using i_bound
    unfolding fri_layer_decommitment_transcript_def
    by (simp add: Let_def)
  have prefix_nf: "None \<notin> dom (dist (execute ?prefix ?start))"
  proof -
    have nf_read: "None \<notin> dom (dist (execute p.read ?start))"
      by (rule p.read_no_failure) simp
    have nf_after_read:
      "\<And>xp s_xp. Some (xp, s_xp) \<in> set_dist (execute p.read ?start) \<Longrightarrow>
        None \<notin> dom
          (dist (execute
            (ntimes p.read (floor_log len) \<bind>
              (\<lambda>xp'. p.read \<bind>
                (\<lambda>xn. ntimes p.read (floor_log len) \<bind>
                  (\<lambda>xn'. return (xp, xp', xn, xn'))))) s_xp))"
    proof -
      fix xp s_xp
      assume read_xp: "Some (xp, s_xp) \<in> set_dist (execute p.read ?start)"
      have read_xp_res:
        "s_xp = s\<lparr>PState := concat (PState s) (l ! i),
          PTranscript := ?path_i @ l ! ?sidx # ?path_s @ rest\<rparr>"
        using p.read_cons_outcome[OF read_xp] by simp
      have enough_path_i: "floor_log len \<le> length (PTranscript s_xp)"
        using path_i unfolding read_xp_res by simp
      have nf_path_i:
        "None \<notin> dom (dist (execute (ntimes p.read (floor_log len)) s_xp))"
        by (rule p.ntimes_read_no_failure[OF enough_path_i])
      have nf_after_path_i:
        "\<And>xp' s_path. Some (xp', s_path) \<in>
          set_dist (execute (ntimes p.read (floor_log len)) s_xp) \<Longrightarrow>
          None \<notin> dom
            (dist (execute
              (p.read \<bind>
                (\<lambda>xn. ntimes p.read (floor_log len) \<bind>
                  (\<lambda>xn'. return (xp, xp', xn, xn')))) s_path))"
      proof -
        fix xp' s_path
        assume read_path:
          "Some (xp', s_path) \<in>
            set_dist (execute (ntimes p.read (floor_log len)) s_xp)"
        let ?s_xp0 = "s\<lparr>PState := concat (PState s) (l ! i)\<rparr>"
        have s_xp_eq:
          "s_xp = ?s_xp0\<lparr>PTranscript := ?path_i @ (l ! ?sidx # ?path_s @ rest)\<rparr>"
          using read_xp_res by simp
        have path_res:
          "s_path = ?s_xp0\<lparr>
            PState := foldl concat (PState ?s_xp0) ?path_i,
            PTranscript := l ! ?sidx # ?path_s @ rest\<rparr>"
          using p.ntimes_read_prefix_outcome[
            OF read_path[unfolded path_i[symmetric] s_xp_eq]]
          by simp
        have nf_read_xn: "None \<notin> dom (dist (execute p.read s_path))"
          by (rule p.read_no_failure) (simp add: path_res)
        have nf_after_read_xn:
          "\<And>xn s_xn. Some (xn, s_xn) \<in> set_dist (execute p.read s_path) \<Longrightarrow>
            None \<notin> dom
              (dist (execute
                (ntimes p.read (floor_log len) \<bind>
                  (\<lambda>xn'. return (xp, xp', xn, xn'))) s_xn))"
        proof -
          fix xn s_xn
          assume read_xn: "Some (xn, s_xn) \<in> set_dist (execute p.read s_path)"
          have read_xn_res:
            "s_xn = s_path\<lparr>
              PState := concat (PState s_path) (l ! ?sidx),
              PTranscript := ?path_s @ rest\<rparr>"
            using p.read_nonempty_outcome[OF read_xn] path_res
            by simp
          have enough_path_s: "floor_log len \<le> length (PTranscript s_xn)"
            using path_s unfolding read_xn_res by simp
          have nf_path_s:
            "None \<notin> dom (dist (execute (ntimes p.read (floor_log len)) s_xn))"
            by (rule p.ntimes_read_no_failure[OF enough_path_s])
          show "None \<notin> dom
            (dist (execute
              (ntimes p.read (floor_log len) \<bind>
                (\<lambda>xn'. return (xp, xp', xn, xn'))) s_xn))"
            by (rule no_failure_bind_returnI[OF nf_path_s])
        qed
        show "None \<notin> dom
          (dist (execute
            (p.read \<bind>
              (\<lambda>xn. ntimes p.read (floor_log len) \<bind>
                (\<lambda>xn'. return (xp, xp', xn, xn')))) s_path))"
          using no_failure_bindI[OF nf_read_xn nf_after_read_xn] .
      qed
      show "None \<notin> dom
        (dist (execute
          (ntimes p.read (floor_log len) \<bind>
            (\<lambda>xp'. p.read \<bind>
              (\<lambda>xn. ntimes p.read (floor_log len) \<bind>
                (\<lambda>xn'. return (xp, xp', xn, xn'))))) s_xp))"
        using no_failure_bindI[OF nf_path_i nf_after_path_i] .
    qed
    show ?thesis
      using no_failure_bindI[OF nf_read nf_after_read] by simp
  qed
  have full_eq:
    "(do {
        xp \<leftarrow> p.read;
        xp' \<leftarrow> ntimes p.read (floor_log len);
        xn \<leftarrow> p.read;
        xn' \<leftarrow> ntimes p.read (floor_log len);
        assert (xp = x);
        ap \<leftarrow> p.check_authentication_path len i xp xp';
        assert (ap = fr);
        let sidx = (i + len div 2) mod len;
        ap \<leftarrow> p.check_authentication_path len sidx xn xn';
        assert (ap = fr);
        let gp = (xp + xn) div 2;
        let hp = (xp - xn) div (2 * ((p.h^i) * shift)^pw);
        let x = gp + b * hp;
        return (i mod (len div 2), x, len div 2, pw + pw)
      }) =
      (?prefix \<bind> (\<lambda>(xp, xp', xn, xn').
        do {
          assert (xp = x);
          ap \<leftarrow> p.check_authentication_path len i xp xp';
          assert (ap = fr);
          let sidx = (i + len div 2) mod len;
          ap \<leftarrow> p.check_authentication_path len sidx xn xn';
          assert (ap = fr);
          let gp = (xp + xn) div 2;
          let hp = (xp - xn) div (2 * ((p.h^i) * shift)^pw);
          let x = gp + b * hp;
          return (i mod (len div 2), x, len div 2, pw + pw)
        }))"
    by (simp add: sm_bind_assoc split: prod.splits)
  show ?thesis
    unfolding start_eq full_eq
  proof (rule no_failure_bindI[OF prefix_nf])
    fix out t
    assume out: "Some (out, t) \<in> set_dist (execute ?prefix ?start)"
    obtain xp xp' xn xn' where out_eq: "out = (xp, xp', xn, xn')"
      by (cases out) auto
    from out[unfolded out_eq] obtain s1 s2 s3 where
      read_xp: "Some (xp, s1) \<in> set_dist (execute p.read ?start)"
      and read_xp_path:
        "Some (xp', s2) \<in> set_dist (execute (ntimes p.read (floor_log len)) s1)"
      and read_xn: "Some (xn, s3) \<in> set_dist (execute p.read s2)"
      and read_xn_path:
        "Some (xn', t) \<in> set_dist (execute (ntimes p.read (floor_log len)) s3)"
      by (auto elim!: p.set_dist_bindE)
    have read_xp_start:
      "?start = s\<lparr>PTranscript := l ! i # (?path_i @ l ! ?sidx # ?path_s @ rest)\<rparr>"
      by simp
    have read_xp':
      "Some (xp, s1) \<in>
        set_dist (execute p.read
          (s\<lparr>PTranscript := l ! i # (?path_i @ l ! ?sidx # ?path_s @ rest)\<rparr>))"
      by (subst read_xp_start[symmetric]) (rule read_xp)
    have xp_replay:
      "xp = l ! i \<and>
       s1 = s\<lparr>
         PState := concat (PState s) (l ! i),
         PTranscript := ?path_i @ l ! ?sidx # ?path_s @ rest\<rparr>"
      by (rule p.read_cons_outcome[OF read_xp'])
    let ?s_xp = "s\<lparr>PState := concat (PState s) (l ! i)\<rparr>"
    have s1_eq: "s1 = ?s_xp\<lparr>PTranscript := ?path_i @ l ! ?sidx # ?path_s @ rest\<rparr>"
      using xp_replay by simp
    have xp_path_replay:
      "xp' = ?path_i \<and>
       s2 = ?s_xp\<lparr>
         PState := foldl concat (PState ?s_xp) ?path_i,
         PTranscript := l ! ?sidx # ?path_s @ rest\<rparr>"
      using p.ntimes_read_prefix_outcome[
        OF read_xp_path[unfolded path_i[symmetric] s1_eq]]
      by simp
	    have read_xn_start:
	      "s2 = (s2\<lparr>PTranscript := l ! ?sidx # (?path_s @ rest)\<rparr>)"
	      using xp_path_replay by simp
	    have read_xn':
	      "Some (xn, s3) \<in>
	        set_dist (execute p.read
	          (s2\<lparr>PTranscript := l ! ?sidx # (?path_s @ rest)\<rparr>))"
	      by (subst read_xn_start[symmetric]) (rule read_xn)
	    have xn_replay:
	      "xn = l ! ?sidx \<and>
	       s3 = s2\<lparr>
	         PState := concat (PState s2) (l ! ?sidx),
	         PTranscript := ?path_s @ rest\<rparr>"
	      by (rule p.read_cons_outcome[OF read_xn'])
    let ?s_xn = "s2\<lparr>PState := concat (PState s2) (l ! ?sidx)\<rparr>"
    have s3_eq: "s3 = ?s_xn\<lparr>PTranscript := ?path_s @ rest\<rparr>"
      using xn_replay by simp
    have xn_path_replay:
      "xn' = ?path_s \<and>
       t = ?s_xn\<lparr>
         PState := foldl concat (PState ?s_xn) ?path_s,
         PTranscript := rest\<rparr>"
      using p.ntimes_read_prefix_outcome[
        OF read_xn_path[unfolded path_s[symmetric] s3_eq]]
      by simp
    have s0_t: "s0 \<le> t"
      using ext xp_replay xp_path_replay xn_replay xn_path_replay
      unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    have xp_x: "xp = x"
      using xp_replay x_eq by simp
    let ?after =
      "do {
        assert (xp = x);
        ap \<leftarrow> p.check_authentication_path len i xp xp';
        assert (ap = fr);
        let sidx = (i + len div 2) mod len;
        ap \<leftarrow> p.check_authentication_path len sidx xn xn';
        assert (ap = fr);
        let gp = (xp + xn) div 2;
        let hp = (xp - xn) div (2 * ((p.h^i) * shift)^pw);
        let x = gp + b * hp;
        return (i mod (len div 2), x, len div 2, pw + pw)
      }"
    have after_eq:
      "?after =
        (assert (xp = x) \<bind> (\<lambda>_.
          p.check_authentication_path len i xp xp' \<bind> (\<lambda>ap.
          assert (ap = fr) \<bind> (\<lambda>_.
          p.check_authentication_path len ?sidx xn xn' \<bind> (\<lambda>ap.
          assert (ap = fr) \<bind> (\<lambda>_.
          let gp = (xp + xn) div 2;
              hp = (xp - xn) div (2 * ((p.h^i) * shift)^pw);
              x = gp + b * hp
          in return (i mod (len div 2), x, len div 2, pw + pw)))))))"
      by (simp add: Let_def sm_bind_assoc)
	    have after_nf: "None \<notin> dom (dist (execute ?after t))"
	      unfolding after_eq
	    proof (rule no_failure_assert_bindI[OF xp_x])
	      show "None \<notin> dom
	        (dist (execute
	          (p.check_authentication_path len i xp xp' \<bind>
	            (\<lambda>api.
	              assert (api = fr) \<bind>
	              (\<lambda>_.
	                p.check_authentication_path len ?sidx xn xn' \<bind>
	                (\<lambda>ap.
	                  assert (ap = fr) \<bind>
	                  (\<lambda>_.
	                    let gp = (xp + xn) div 2;
	                        hp = (xp - xn) div (2 * ((p.h ^ i) * shift) ^ pw);
	                        x = gp + b * hp
	                    in return (i mod (len div 2), x, len div 2, pw + pw)))))) t))"
	      proof (rule no_failure_bindI[OF p.check_authentication_path_no_failure])
	      fix api u
	      assume check_i:
	        "Some (api, u) \<in>
	          set_dist (execute (p.check_authentication_path len i xp xp') t)"
	      have check_i_honest:
	        "Some (api, u) \<in>
	          set_dist (execute
	            (p.check_authentication_path (length l) i (l ! i) ?path_i) t)"
	        using check_i xp_replay xp_path_replay len_eq by simp
      have i_bound_l: "i < length l"
        using i_bound len_eq by simp
	      have check_i_honest_l:
	        "Some (api, u) \<in>
	          set_dist (execute
	            (p.check_authentication_path (length l) i (l ! i)
	              (get_authentication_path (length l) i m)) t)"
	        using check_i_honest len_eq by simp
	      have ap_i: "api = value m \<and> t \<le> u"
	        using p.check_created_tree_outcome[
	          OF created len_pow i_bound_l refl s0_t check_i_honest_l]
	        by simp
	      then have ap_fr: "api = fr"
	        using root by simp
      have tail_nf: "None \<notin> dom
        (dist (execute
          (p.check_authentication_path len ?sidx xn xn' \<bind>
            (\<lambda>ap.
              assert (ap = fr) \<bind>
              (\<lambda>_.
                let gp = (xp + xn) div 2;
                    hp = (xp - xn) div (2 * ((p.h ^ i) * shift) ^ pw);
                    x = gp + b * hp
                in return (i mod (len div 2), x, len div 2, pw + pw)))) u))"
      proof (rule no_failure_bindI)
        show "None \<notin> dom
          (dist (execute (p.check_authentication_path len ?sidx xn xn') u))"
          by (rule p.check_authentication_path_no_failure)
        fix ap2 u2
        assume check_s:
          "Some (ap2, u2) \<in>
            set_dist (execute (p.check_authentication_path len ?sidx xn xn') u)"
        have s0_u: "s0 \<le> u"
          using s0_t ap_i
          unfolding less_eq_hash_ext_def less_eq_fmap_def by metis
        have check_s_honest:
          "Some (ap2, u2) \<in>
            set_dist (execute
              (p.check_authentication_path (length l) ?sidx (l ! ?sidx) ?path_s) u)"
          using check_s xn_replay xn_path_replay len_eq by simp
        have check_s_honest_l:
          "Some (ap2, u2) \<in>
            set_dist (execute
              (p.check_authentication_path (length l) ?sidx (l ! ?sidx)
                (get_authentication_path (length l) ?sidx m)) u)"
          using check_s_honest len_eq by simp
        have ap_s: "ap2 = value m"
          using p.check_created_tree_outcome[
            OF created len_pow sidx_bound refl s0_u check_s_honest_l]
          by simp
        have ap_s_fr: "ap2 = fr"
          using ap_s root by simp
        have ap_s_fr_true: "(ap2 = fr) = True"
          using ap_s_fr by simp
        show "None \<notin> dom
          (dist (execute
            (assert (ap2 = fr) \<bind>
              (\<lambda>_.
                let gp = (xp + xn) div 2;
                    hp = (xp - xn) div (2 * ((p.h ^ i) * shift) ^ pw);
                    x = gp + b * hp
                in return (i mod (len div 2), x, len div 2, pw + pw))) u2))"
          using ap_s_fr by (simp add: assert_def)
      qed
	      show "None \<notin> dom
	        (dist (execute
	          (assert (api = fr) \<bind>
	            (\<lambda>_.
	              p.check_authentication_path len ?sidx xn xn' \<bind>
	              (\<lambda>ap.
	                assert (ap = fr) \<bind>
	                (\<lambda>_.
	                  let gp = (xp + xn) div 2;
	                      hp = (xp - xn) div (2 * ((p.h ^ i) * shift) ^ pw);
	                      x = gp + b * hp
	                  in return
	                    (i mod (len div 2),
	                     x,
	                     len div 2, pw + pw))))) u))"
	        by (rule no_failure_assert_bindI[OF ap_fr tail_nf])
	      qed
		      qed
		    show "None \<notin> dom
	      (dist (execute
	        ((case out of (xp, xp', xn, xn') \<Rightarrow>
	          do {
	            assert (xp = x);
	            ap \<leftarrow> p.check_authentication_path len i xp xp';
	            assert (ap = fr);
	            let sidx = (i + len div 2) mod len;
	            ap \<leftarrow> p.check_authentication_path len sidx xn xn';
	            assert (ap = fr);
	            let gp = (xp + xn) div 2;
	            let hp = (xp - xn) div (2 * ((p.h^i) * shift)^pw);
	            let x = gp + b * hp;
	            return (i mod (len div 2), x, len div 2, pw + pw)
	          })) t))"
	      unfolding out_eq
	      using after_nf by simp
      qed
    qed

lemma honest_fri_layer_decommitment_outcome:
  assumes len_eq: "len = length l"
    and i_bound: "i < len"
    and path_i:
      "length (get_authentication_path len i m) = floor_log len"
    and path_s:
      "length (get_authentication_path len ((i + len div 2) mod len) m) =
        floor_log len"
    and outcome:
      "Some (res, t') \<in> set_dist (execute
        (do {
          xp \<leftarrow> p.read;
          xp' \<leftarrow> ntimes p.read (floor_log len);
          xn \<leftarrow> p.read;
          xn' \<leftarrow> ntimes p.read (floor_log len);
          assert (xp = x);
          ap \<leftarrow> p.check_authentication_path len i xp xp';
          assert (ap = fr);
          let sidx = (i + len div 2) mod len;
          ap \<leftarrow> p.check_authentication_path len sidx xn xn';
          assert (ap = fr);
          let gp = (xp + xn) div 2;
          let hp = (xp - xn) div (2 * ((p.h^i) * shift)^pw);
          let x = gp + b * hp;
          return (i mod (len div 2), x, len div 2, pw + pw)
        })
        (s\<lparr>PTranscript := fri_layer_decommitment_transcript l m i len @ rest\<rparr>))"
  shows
	    "res =
	      (i mod (len div 2),
	       ((l ! i) + (l ! ((i + len div 2) mod len))) div 2 +
	        b * (((l ! i) - (l ! ((i + len div 2) mod len))) div
	          (2 * ((p.h^i) * shift)^pw)),
	       len div 2,
	       pw + pw)"
	    "PTranscript t' = rest"
	    "PState t' =
	      foldl concat (PState s) (fri_layer_decommitment_transcript l m i len)"
proof -
  let ?sidx = "(i + len div 2) mod len"
  let ?path_i = "get_authentication_path len i m"
  let ?path_s = "get_authentication_path len ?sidx m"
  let ?start =
    "s\<lparr>PTranscript := l ! i # ?path_i @ l ! ?sidx # ?path_s @ rest\<rparr>"
  have len_pos: "0 < len"
    using i_bound by simp
  have sidx_bound: "?sidx < length l"
    using len_pos unfolding len_eq by simp
  have start_eq:
    "s\<lparr>PTranscript := fri_layer_decommitment_transcript l m i len @ rest\<rparr> =
      ?start"
    using i_bound
    unfolding fri_layer_decommitment_transcript_def
    by (simp add: Let_def)
  from outcome[unfolded start_eq] obtain xp xp' xn xn' api aps
      s1 s2 s3 s4 s5 s6 s7 s8 where
    read_xp: "Some (xp, s1) \<in> set_dist (execute p.read ?start)"
    and read_xp_path:
      "Some (xp', s2) \<in>
        set_dist (execute (ntimes p.read (floor_log len)) s1)"
    and read_xn: "Some (xn, s3) \<in> set_dist (execute p.read s2)"
    and read_xn_path:
      "Some (xn', s4) \<in>
        set_dist (execute (ntimes p.read (floor_log len)) s3)"
    and assert_x: "Some ((), s5) \<in> set_dist (execute (assert (xp = x)) s4)"
    and check_i:
      "Some (api, s6) \<in>
        set_dist (execute (p.check_authentication_path len i xp xp') s5)"
    and assert_i: "Some ((), s7) \<in> set_dist (execute (assert (api = fr)) s6)"
    and check_s:
      "Some (aps, s8) \<in>
        set_dist (execute (p.check_authentication_path len ?sidx xn xn') s7)"
    and assert_s: "Some ((), t') \<in> set_dist (execute (assert (aps = fr)) s8)"
    and res_eq:
      "res =
        (i mod (len div 2),
         (xp + xn) div 2 + b * ((xp - xn) div (2 * ((p.h ^ i) * shift) ^ pw)),
         len div 2, pw + pw)"
    by (auto simp: Let_def elim!: p.set_dist_bindE)
  have xp_replay:
    "xp = l ! i \<and>
     s1 = s\<lparr>
       PState := concat (PState s) (l ! i),
       PTranscript := ?path_i @ l ! ?sidx # ?path_s @ rest\<rparr>"
    by (rule p.read_cons_outcome[OF read_xp])
  let ?s_xp = "s\<lparr>PState := concat (PState s) (l ! i)\<rparr>"
  have s1_eq:
    "s1 = ?s_xp\<lparr>PTranscript := ?path_i @ l ! ?sidx # ?path_s @ rest\<rparr>"
    using xp_replay by simp
  have xp_path_replay:
    "xp' = ?path_i \<and>
     s2 = ?s_xp\<lparr>
       PState := foldl concat (PState ?s_xp) ?path_i,
       PTranscript := l ! ?sidx # ?path_s @ rest\<rparr>"
    using p.ntimes_read_prefix_outcome[
      OF read_xp_path[unfolded path_i[symmetric] s1_eq]]
    by simp
  have read_xn':
    "Some (xn, s3) \<in>
      set_dist (execute p.read
        (s2\<lparr>PTranscript := l ! ?sidx # (?path_s @ rest)\<rparr>))"
    using read_xn xp_path_replay by simp
  have xn_replay:
    "xn = l ! ?sidx \<and>
     s3 = s2\<lparr>
       PState := concat (PState s2) (l ! ?sidx),
       PTranscript := ?path_s @ rest\<rparr>"
    by (rule p.read_cons_outcome[OF read_xn'])
  let ?s_xn = "s2\<lparr>PState := concat (PState s2) (l ! ?sidx)\<rparr>"
  have s3_eq:
    "s3 = ?s_xn\<lparr>PTranscript := ?path_s @ rest\<rparr>"
    using xn_replay by simp
  have xn_path_replay:
    "xn' = ?path_s \<and>
     s4 = ?s_xn\<lparr>
       PState := foldl concat (PState ?s_xn) ?path_s,
       PTranscript := rest\<rparr>"
    using p.ntimes_read_prefix_outcome[
      OF read_xn_path[unfolded path_s[symmetric] s3_eq]]
    by simp
  have s5_tr: "PTranscript s5 = rest"
    using assert_outcomeD(2)[OF assert_x] xn_path_replay by simp
  have s6_tr: "PTranscript s6 = rest"
    using p.check_authentication_path_preserves_channel(2)[OF check_i] s5_tr
    by simp
  have s7_tr: "PTranscript s7 = rest"
    using assert_outcomeD(2)[OF assert_i] s6_tr by simp
	  have s8_tr: "PTranscript s8 = rest"
	    using p.check_authentication_path_preserves_channel(2)[OF check_s] s7_tr
	    by simp
	  have state_t:
	    "PState t' =
	      foldl concat (PState s) (fri_layer_decommitment_transcript l m i len)"
	  proof -
	    have i_mod: "i mod len = i"
	      using i_bound by simp
	    have s5_state: "PState s5 = PState s4"
	      using assert_outcomeD(2)[OF assert_x] by simp
	    have s6_state: "PState s6 = PState s5"
	      using p.check_authentication_path_preserves_channel(1)[OF check_i] .
	    have s7_state: "PState s7 = PState s6"
	      using assert_outcomeD(2)[OF assert_i] by simp
	    have s8_state: "PState s8 = PState s7"
	      using p.check_authentication_path_preserves_channel(1)[OF check_s] .
	    have t_state: "PState t' = PState s8"
	      using assert_outcomeD(2)[OF assert_s] by simp
	    show ?thesis
	      using xp_replay xp_path_replay xn_replay xn_path_replay
	        s5_state s6_state s7_state s8_state t_state i_mod
	      unfolding fri_layer_decommitment_transcript_def
	      by (simp add: Let_def)
	  qed
	  show
	    "res =
	      (i mod (len div 2),
	       ((l ! i) + (l ! ?sidx)) div 2 +
        b * (((l ! i) - (l ! ?sidx)) div
          (2 * ((p.h^i) * shift)^pw)),
       len div 2,
       pw + pw)"
    using res_eq xp_replay xn_replay by simp
	  show "PTranscript t' = rest"
	    using assert_outcomeD(2)[OF assert_s] s8_tr by simp
	  show "PState t' =
	    foldl concat (PState s) (fri_layer_decommitment_transcript l m i len)"
	    using state_t .
	qed

lemma fri_layer_decommitment_hash_extends:
  assumes outcome:
    "Some (res, t') \<in> set_dist (execute
      (do {
        xp \<leftarrow> p.read;
        xp' \<leftarrow> ntimes p.read (floor_log len);
        xn \<leftarrow> p.read;
        xn' \<leftarrow> ntimes p.read (floor_log len);
        assert (xp = x);
        ap \<leftarrow> p.check_authentication_path len i xp xp';
        assert (ap = fr);
        let sidx = (i + len div 2) mod len;
        ap \<leftarrow> p.check_authentication_path len sidx xn xn';
        assert (ap = fr);
        let gp = (xp + xn) div 2;
        let hp = (xp - xn) div (2 * ((p.h^i) * shift)^pw);
        let x = gp + b * hp;
        return (i mod (len div 2), x, len div 2, pw + pw)
      }) s)"
  shows "s \<le> t'"
proof -
  let ?sidx = "(i + len div 2) mod len"
  from outcome obtain xp xp' xn xn' api aps
      s1 s2 s3 s4 s5 s6 s7 s8 where
    read_xp: "Some (xp, s1) \<in> set_dist (execute p.read s)"
    and read_xp_path:
      "Some (xp', s2) \<in>
        set_dist (execute (ntimes p.read (floor_log len)) s1)"
    and read_xn: "Some (xn, s3) \<in> set_dist (execute p.read s2)"
    and read_xn_path:
      "Some (xn', s4) \<in>
        set_dist (execute (ntimes p.read (floor_log len)) s3)"
    and assert_x: "Some ((), s5) \<in> set_dist (execute (assert (xp = x)) s4)"
    and check_i:
      "Some (api, s6) \<in>
        set_dist (execute (p.check_authentication_path len i xp xp') s5)"
    and assert_i: "Some ((), s7) \<in> set_dist (execute (assert (api = fr)) s6)"
    and check_s:
      "Some (aps, s8) \<in>
        set_dist (execute (p.check_authentication_path len ?sidx xn xn') s7)"
    and assert_s: "Some ((), t') \<in> set_dist (execute (assert (aps = fr)) s8)"
    by (auto simp: Let_def elim!: p.set_dist_bindE)
  have "s \<le> s1"
    using read_xp by (rule read_hash_extends)
  moreover have "s1 \<le> s2"
    using read_xp_path by (rule ntimes_read_hash_extends)
  moreover have "s2 \<le> s3"
    using read_xn by (rule read_hash_extends)
  moreover have "s3 \<le> s4"
    using read_xn_path by (rule ntimes_read_hash_extends)
  moreover have "s4 \<le> s5"
    using assert_x by (rule assert_hash_extends)
  moreover have "s5 \<le> s6"
    using check_i by (rule check_authentication_path_hash_extends)
  moreover have "s6 \<le> s7"
    using assert_i by (rule assert_hash_extends)
  moreover have "s7 \<le> s8"
    using check_s by (rule check_authentication_path_hash_extends)
  moreover have "s8 \<le> t'"
    using assert_s by (rule assert_hash_extends)
  ultimately show ?thesis
    by (meson p.hash_ext_trans)
qed

lemma honest_fri_layer_decommitment_step:
  assumes created: "p.created_tree l m s0"
    and len_eq: "len = length l"
    and len_pow: "length l = 2 ^ n"
    and i_bound: "i < len"
    and x_eq: "x = l ! i"
    and ext: "s0 \<le> s"
    and path_i:
      "length (get_authentication_path len i m) = floor_log len"
    and path_s:
      "length (get_authentication_path len ((i + len div 2) mod len) m) =
        floor_log len"
    and root: "fr = value m"
    and tr:
      "start =
        s\<lparr>PTranscript := fri_layer_decommitment_transcript l m i len @ rest\<rparr>"
  shows
    "None \<notin> dom (dist (execute (fri_verifier_layer b fr i x len pw) start))"
    "\<And>res t'. Some (res, t') \<in>
        set_dist (execute (fri_verifier_layer b fr i x len pw) start) \<Longrightarrow>
      res =
        (i mod (len div 2), fri_fold_value b l i len pw, len div 2, pw + pw) \<and>
      PTranscript t' = rest \<and>
      start \<le> t'"
proof -
  show nf:
    "None \<notin> dom (dist (execute (fri_verifier_layer b fr i x len pw) start))"
    unfolding fri_verifier_layer_def tr
    by (rule honest_fri_layer_decommitment_no_failure[
        OF created len_eq len_pow i_bound x_eq ext path_i path_s root])
  fix res t'
  assume outcome:
    "Some (res, t') \<in>
      set_dist (execute (fri_verifier_layer b fr i x len pw) start)"
  have res_tr:
    "res =
      (i mod (len div 2), fri_fold_value b l i len pw, len div 2, pw + pw)"
    "PTranscript t' = rest"
    using honest_fri_layer_decommitment_outcome[
        OF len_eq i_bound path_i path_s outcome[unfolded fri_verifier_layer_def tr]]
    unfolding fri_fold_value_def by simp_all
  have ext_start: "start \<le> t'"
    using fri_layer_decommitment_hash_extends[
      OF outcome[unfolded fri_verifier_layer_def]] .
  show
    "res =
      (i mod (len div 2), fri_fold_value b l i len pw, len div 2, pw + pw) \<and>
     PTranscript t' = rest \<and>
     start \<le> t'"
    using res_tr ext_start by simp
qed

lemma honest_fri_layer_decommitment_step_created:
  assumes created: "p.created_tree l m s0"
    and len_eq: "len = length l"
    and len_pow: "length l = 2 ^ n"
    and i_bound: "i < len"
    and x_eq: "x = l ! i"
    and ext: "s0 \<le> s"
    and root: "fr = value m"
    and tr:
      "start =
        s\<lparr>PTranscript := fri_layer_decommitment_transcript l m i len @ rest\<rparr>"
  shows
    "None \<notin> dom (dist (execute (fri_verifier_layer b fr i x len pw) start))"
    "\<And>res t'. Some (res, t') \<in>
        set_dist (execute (fri_verifier_layer b fr i x len pw) start) \<Longrightarrow>
      res =
        (i mod (len div 2), fri_fold_value b l i len pw, len div 2, pw + pw) \<and>
      PTranscript t' = rest \<and>
      start \<le> t'"
proof -
  have path_i:
    "length (get_authentication_path len i m) = floor_log len"
    using created_tree_get_authentication_path_len[
      OF created len_pow, of i] i_bound len_eq by simp
  have len_pos: "0 < len"
    using i_bound by simp
  have sidx_bound:
    "(i + len div 2) mod len < length l"
    using len_pos len_eq by simp
  have path_s:
    "length (get_authentication_path len ((i + len div 2) mod len) m) =
      floor_log len"
    using created_tree_get_authentication_path_len[
      OF created len_pow, of "(i + len div 2) mod len"] sidx_bound len_eq
    by simp
  show "None \<notin> dom (dist (execute (fri_verifier_layer b fr i x len pw) start))"
    by (rule honest_fri_layer_decommitment_step(1)[
        OF created len_eq len_pow i_bound x_eq ext path_i path_s root tr])
  fix res t'
  assume outcome:
    "Some (res, t') \<in>
      set_dist (execute (fri_verifier_layer b fr i x len pw) start)"
  show
    "res =
      (i mod (len div 2), fri_fold_value b l i len pw, len div 2, pw + pw) \<and>
     PTranscript t' = rest \<and>
     start \<le> t'"
    by (rule honest_fri_layer_decommitment_step(2)[
        OF created len_eq len_pow i_bound x_eq ext path_i path_s root tr outcome])
qed

lemma receive_query_commits_step_hash_extends:
  assumes step_in: "m \<in> set (v.receive_query_commits fl)"
    and outcome: "Some (y, t) \<in> set_dist (execute (m a) s)"
  shows "s \<le> t"
proof -
  from receive_query_commits_step_eq[OF step_in] obtain b fr where
    m_eq: "m = (\<lambda>(i, x, len, pw). fri_verifier_layer b fr i x len pw)"
    by blast
  obtain i x len pw where a_eq: "a = (i, x, len, pw)"
    by (cases a) auto
  have layer_out:
    "Some (y, t) \<in>
      set_dist (execute (fri_verifier_layer b fr i x len pw) s)"
    using outcome unfolding m_eq a_eq by simp
	  show ?thesis
	    using fri_layer_decommitment_hash_extends[
	      OF layer_out[unfolded fri_verifier_layer_def]] .
	qed

lemma fri_verifier_layer_preserves_query_counter:
  assumes outcome:
    "Some (res, t) \<in> set_dist (execute (fri_verifier_layer b fr i x len pw) s)"
  shows "PQueryCounter t = PQueryCounter s"
proof -
  from outcome obtain xp s1 xp' s2 xn s3 xn' s4 s5 ap_i s6 s7 ap_s s8 s9 where
    read_xp: "Some (xp, s1) \<in> set_dist (execute p.read s)"
    and read_xp_path:
      "Some (xp', s2) \<in> set_dist (execute (ntimes p.read (floor_log len)) s1)"
    and read_xn: "Some (xn, s3) \<in> set_dist (execute p.read s2)"
    and read_xn_path:
      "Some (xn', s4) \<in> set_dist (execute (ntimes p.read (floor_log len)) s3)"
    and assert_x: "Some ((), s5) \<in> set_dist (execute (assert (xp = x)) s4)"
    and check_i:
      "Some (ap_i, s6) \<in>
        set_dist (execute (p.check_authentication_path len i xp xp') s5)"
    and assert_i: "Some ((), s7) \<in> set_dist (execute (assert (ap_i = fr)) s6)"
    and check_s:
      "Some (ap_s, s8) \<in>
        set_dist (execute (p.check_authentication_path len ((i + len div 2) mod len) xn xn') s7)"
    and assert_s: "Some ((), s9) \<in> set_dist (execute (assert (ap_s = fr)) s8)"
    and ret:
      "Some (res, t) \<in>
        set_dist (execute
          (return
            (i mod (len div 2),
             (xp + xn) div 2 + b * ((xp - xn) div (2 * ((p.h ^ i) * shift) ^ pw)),
             len div 2, pw + pw)) s9)"
    unfolding fri_verifier_layer_def
    by (auto simp: Let_def elim!: p.set_dist_bindE)
  have q_s1: "PQueryCounter s1 = PQueryCounter s"
    using read_preserves_counters[OF read_xp] by simp
  have q_s2: "PQueryCounter s2 = PQueryCounter s1"
    by (rule ntimes_read_preserves_query_counter[OF read_xp_path])
  have q_s3: "PQueryCounter s3 = PQueryCounter s2"
    using read_preserves_counters[OF read_xn] by simp
  have q_s4: "PQueryCounter s4 = PQueryCounter s3"
    by (rule ntimes_read_preserves_query_counter[OF read_xn_path])
  have s5_eq: "s5 = s4"
    using assert_outcomeD(2)[OF assert_x] .
  have q_s6: "PQueryCounter s6 = PQueryCounter s5"
    using p.check_authentication_path_preserves_channel(6)[OF check_i] .
  have s7_eq: "s7 = s6"
    using assert_outcomeD(2)[OF assert_i] .
  have q_s8: "PQueryCounter s8 = PQueryCounter s7"
    using p.check_authentication_path_preserves_channel(6)[OF check_s] .
  have s9_eq: "s9 = s8"
    using assert_outcomeD(2)[OF assert_s] .
  have t_eq: "t = s9"
    using ret by simp
  show ?thesis
    using q_s1 q_s2 q_s3 q_s4 q_s6 q_s8
    unfolding s5_eq s7_eq s9_eq t_eq by simp
qed

lemma receive_query_commits_step_preserves_query_counter:
  assumes step_in: "m \<in> set (v.receive_query_commits fl)"
    and outcome: "Some (y, t) \<in> set_dist (execute (m a) s)"
  shows "PQueryCounter t = PQueryCounter s"
proof -
  from receive_query_commits_step_eq[OF step_in] obtain b fr where
    m_eq: "m = (\<lambda>(i, x, len, pw). fri_verifier_layer b fr i x len pw)"
    by blast
  obtain i x len pw where a_eq: "a = (i, x, len, pw)"
    by (cases a) auto
  have layer_out:
    "Some (y, t) \<in>
      set_dist (execute (fri_verifier_layer b fr i x len pw) s)"
    using outcome unfolding m_eq a_eq by simp
  show ?thesis
    by (rule fri_verifier_layer_preserves_query_counter[OF layer_out])
qed

lemma receive_query_commits_mfold_preserves_query_counter:
  assumes outcome:
    "Some (y, t) \<in>
      set_dist (execute (mfold a (v.receive_query_commits fl)) s)"
  shows "PQueryCounter t = PQueryCounter s"
  by (rule mfold_preserves_query_counter[OF outcome])
    (rule receive_query_commits_step_preserves_query_counter)

lemma receive_query_commits_mfold_hash_extends:
  assumes outcome:
    "Some (y, t) \<in>
      set_dist (execute (mfold a (v.receive_query_commits fl)) s)"
  shows "s \<le> t"
  by (rule mfold_hash_extends[OF outcome])
    (rule receive_query_commits_step_hash_extends)

lemma next_fri_domain_length:
  "length (p.next_fri_domain d) = length d div 2"
  unfolding p.next_fri_domain_def by simp

lemma next_fri_domain_nth:
  assumes "i < length d div 2"
  shows "p.next_fri_domain d ! i = d ! i * d ! i"
  using assms unfolding p.next_fri_domain_def by simp

lemma next_fri_layer_components:
  assumes "p.next_fri_layer q d b = (q', d', l')"
  shows
    "q' = p.next_fri_polynomial q b"
    "d' = p.next_fri_domain d"
    "l' = map (poly q') d'"
  using assms
  unfolding p.next_fri_layer_def
  by (auto simp: Let_def split: prod.splits)

lemma next_fri_layer_length:
  assumes "p.next_fri_layer q d b = (q', d', l')"
  shows "length l' = length d div 2"
  using next_fri_layer_components[OF assms] next_fri_domain_length by simp

lemma next_fri_layer_domain_nth:
  assumes layer: "p.next_fri_layer q d b = (q', d', l')"
    and i_bound: "i < length d div 2"
  shows "d' ! i = d ! i * d ! i"
  using next_fri_layer_components(2)[OF layer] next_fri_domain_nth[OF i_bound]
  by simp

lemma fri_successor_domain_points:
  assumes ds0: "ds ! 0 = p.eval_domain"
    and successors:
      "\<And>j. j < n \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and j_le: "j \<le> n"
    and k_bound: "k < length (ds ! j)"
  shows "ds ! j ! k = ((p.h ^ k) * shift) ^ (2 ^ j)"
  using j_le k_bound
proof (induction j arbitrary: k)
  case 0
  have k_lt: "k < clength * scale"
    using "0.prems"(2) ds0 eval_domain_length by simp
  show ?case
    using eval_domain_nth[OF k_lt] ds0 by simp
next
  case (Suc j)
  have j_lt_n: "j < n"
    using Suc.prems(1) by simp
  have ds_suc:
    "ds ! Suc j = p.next_fri_domain (ds ! j)"
    using next_fri_layer_components(2)[OF successors[OF j_lt_n]]
    by simp
  have k_half: "k < length (ds ! j) div 2"
    using Suc.prems(2) ds_suc next_fri_domain_length by simp
  have k_prev: "k < length (ds ! j)"
    using k_half by linarith
  have len_pos: "0 < length (ds ! j)"
    using k_prev by (cases "ds ! j") auto
  have curr:
    "ds ! Suc j ! k = ds ! j ! k * ds ! j ! k"
    using ds_suc next_fri_domain_nth[OF k_half] by simp
  have prev:
    "ds ! j ! k = ((p.h ^ k) * shift) ^ (2 ^ j)"
    by (rule Suc.IH) (use Suc.prems(1) k_prev in simp_all)
  have pow_suc: "(2::nat) ^ j + (2::nat) ^ j = (2::nat) ^ Suc j"
  proof -
    have "(2::nat) ^ Suc j = 2 * 2 ^ j"
      by (simp add: power_Suc)
    also have "... = 2 ^ j + 2 ^ j"
      by presburger
    finally show ?thesis
      by simp
  qed
  have next':
    "((p.h ^ k) * shift) ^ (2 ^ j) *
      ((p.h ^ k) * shift) ^ (2 ^ j) =
        ((p.h ^ k) * shift) ^ (2 ^ Suc j)"
  proof -
    have "((p.h ^ k) * shift) ^ (2 ^ j) *
      ((p.h ^ k) * shift) ^ (2 ^ j) =
        ((p.h ^ k) * shift) ^ (2 ^ j + 2 ^ j)"
      by (simp add: power_add[symmetric])
    also have "... = ((p.h ^ k) * shift) ^ (2 ^ Suc j)"
      by (simp only: pow_suc)
    finally show ?thesis .
  qed
  show ?case
    using curr prev next' by simp
qed

lemma fri_successor_layer_lengths_power:
  assumes init_len: "length (ls ! 0) = 2 ^ N"
    and n_le_N: "n \<le> N"
    and layer_lens: "\<And>j. j < n \<Longrightarrow> length (ds ! j) = length (ls ! j)"
    and successors:
      "\<And>j. j < n \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
  shows "j \<le> n \<Longrightarrow> length (ls ! j) = 2 ^ (N - j)"
proof (induction j)
  case 0
  then show ?case
    using init_len by simp
next
  case (Suc j)
  have j_lt_n: "j < n"
    using Suc.prems by simp
  have j_le_n: "j \<le> n"
    using Suc.prems by simp
  have len_j: "length (ls ! j) = 2 ^ (N - j)"
    using Suc.IH[OF j_le_n] .
  have len_next:
    "length (ls ! Suc j) = length (ds ! j) div 2"
    using next_fri_layer_length[OF successors[OF j_lt_n]] by simp
  have j_lt_N: "j < N"
    using j_lt_n n_le_N by linarith
  have diff_suc: "N - j = Suc (N - Suc j)"
    using j_lt_N by simp
  show ?case
    using len_next layer_lens[OF j_lt_n] len_j diff_suc by simp
qed

lemma fri_successor_layer_lengths_are_powers:
  assumes init_len: "length (ls ! 0) = 2 ^ N"
    and n_le_N: "n \<le> N"
    and layer_lens: "\<And>j. j < n \<Longrightarrow> length (ds ! j) = length (ls ! j)"
    and successors:
      "\<And>j. j < n \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and j_bound: "j < n"
  shows "\<exists>k. length (ls ! j) = 2 ^ k"
  using fri_successor_layer_lengths_power[
    OF init_len n_le_N layer_lens successors, of j] j_bound
  by auto

lemma fri_commit_initial_decommit_layer_lengths_are_powers:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.fri_commit n [cp] [d] [l] [m]) s)"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and init_len: "length l = 2 ^ N"
    and n_le_N: "n \<le> N"
    and j_bound: "j < n"
  shows "\<exists>k. length (ls ! j) = 2 ^ k"
proof -
  have lens:
    "length ps = Suc n"
    "length ds = Suc n"
    "length ls = Suc n"
    "length ms = Suc n"
    using p.fri_commit_lengths[OF outcome] by simp_all
  have ls0: "ls ! 0 = l"
  proof -
    have "take (length [l]) ls = [l]"
      using p.fri_commit_preserves_prefix[OF outcome] by simp
    then show ?thesis
      using lens by (cases ls) auto
  qed
  from fri_commit_initial_replay_successor_data[OF outcome]
  obtain roots challenges where
    successors:
      "\<forall>j<n.
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    by blast
  have layer_lens:
    "\<And>j. j < n \<Longrightarrow> length (ds ! j) = length (ls ! j)"
  proof -
    fix j
    assume j_lt: "j < n"
    have "ls ! j = map (poly (ps ! j)) (ds ! j)"
      by (rule layers) (use j_lt lens in simp_all)
    then show "length (ds ! j) = length (ls ! j)"
      by simp
  qed
  have init_len': "length (ls ! 0) = 2 ^ N"
    using ls0 init_len by simp
  have successors':
    "\<And>j. j < n \<Longrightarrow>
      p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    using successors by simp
  show ?thesis
    by (rule fri_successor_layer_lengths_are_powers[
        where ps=ps and ds=ds and ls=ls and challenges=challenges,
        OF init_len' n_le_N layer_lens successors' j_bound])
qed

lemma fri_commit_initial_layer_length_power:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.fri_commit n [cp] [d] [l] [m]) s)"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and init_len: "length l = 2 ^ N"
    and n_le_N: "n \<le> N"
    and j_le: "j \<le> n"
  shows "length (ls ! j) = 2 ^ (N - j)"
proof -
  have lens:
    "length ps = Suc n"
    "length ds = Suc n"
    "length ls = Suc n"
    "length ms = Suc n"
    using p.fri_commit_lengths[OF outcome] by simp_all
  have ls0: "ls ! 0 = l"
    using fri_commit_initial_heads(3)[OF outcome] .
  from fri_commit_initial_replay_successor_data[OF outcome]
  obtain roots challenges where
    successors:
      "\<forall>j<n.
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    by blast
  have layer_lens:
    "\<And>j. j < n \<Longrightarrow> length (ds ! j) = length (ls ! j)"
  proof -
    fix j
    assume j_lt: "j < n"
    have "ls ! j = map (poly (ps ! j)) (ds ! j)"
      by (rule layers) (use j_lt lens in simp_all)
    then show "length (ds ! j) = length (ls ! j)"
      by simp
  qed
  have init_len': "length (ls ! 0) = 2 ^ N"
    using ls0 init_len by simp
  have successors':
    "\<And>j. j < n \<Longrightarrow>
      p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    using successors by simp
  show ?thesis
    by (rule fri_successor_layer_lengths_power[
        OF init_len' n_le_N layer_lens successors' j_le])
qed

lemma fri_commit_initial_domain_points:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.fri_commit n [cp] [p.eval_domain] [l] [m]) s)"
    and j_le: "j \<le> n"
    and k_bound: "k < length (ds ! j)"
  shows "ds ! j ! k = ((p.h ^ k) * shift) ^ (2 ^ j)"
proof -
  have ds0: "ds ! 0 = p.eval_domain"
    using fri_commit_initial_heads(2)[OF outcome] .
  from fri_commit_initial_replay_successor_data[OF outcome]
  obtain roots challenges where
    successors:
      "\<And>j. j < n \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    by blast
  show ?thesis
    by (rule fri_successor_domain_points[
        OF ds0 successors j_le k_bound])
qed

lemma trace_fri_commit_initial_layer_length_power:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.trace_fri_commit n [cp] [d] [l] [m]) s)"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and init_len: "length l = 2 ^ N"
    and n_le_N: "n \<le> N"
    and j_le: "j \<le> n"
  shows "length (ls ! j) = 2 ^ (N - j)"
proof -
  have lens:
    "length ps = Suc n"
    "length ds = Suc n"
    "length ls = Suc n"
    "length ms = Suc n"
    using p.trace_fri_commit_lengths[OF outcome] by simp_all
  have ls0: "ls ! 0 = l"
    using trace_fri_commit_initial_heads(3)[OF outcome] .
  from trace_fri_commit_initial_replay_successor_data[OF outcome]
  obtain roots challenges where
    successors:
      "\<forall>j<n.
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    by blast
  have layer_lens:
    "\<And>j. j < n \<Longrightarrow> length (ds ! j) = length (ls ! j)"
  proof -
    fix j
    assume j_lt: "j < n"
    have "ls ! j = map (poly (ps ! j)) (ds ! j)"
      by (rule layers) (use j_lt lens in simp_all)
    then show "length (ds ! j) = length (ls ! j)"
      by simp
  qed
  have init_len': "length (ls ! 0) = 2 ^ N"
    using ls0 init_len by simp
  have successors':
    "\<And>j. j < n \<Longrightarrow>
      p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    using successors by simp
  show ?thesis
    by (rule fri_successor_layer_lengths_power[
        OF init_len' n_le_N layer_lens successors' j_le])
qed

lemma composition_fri_commit_initial_layer_length_power:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.composition_fri_commit n [cp] [d] [l] [m]) s)"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and init_len: "length l = 2 ^ N"
    and n_le_N: "n \<le> N"
    and j_le: "j \<le> n"
  shows "length (ls ! j) = 2 ^ (N - j)"
proof -
  have lens:
    "length ps = Suc n"
    "length ds = Suc n"
    "length ls = Suc n"
    "length ms = Suc n"
    using p.composition_fri_commit_lengths[OF outcome] by simp_all
  have ls0: "ls ! 0 = l"
    using composition_fri_commit_initial_heads(3)[OF outcome] .
  from composition_fri_commit_initial_replay_successor_data[OF outcome]
  obtain roots challenges where
    successors:
      "\<forall>j<n.
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    by blast
  have layer_lens:
    "\<And>j. j < n \<Longrightarrow> length (ds ! j) = length (ls ! j)"
  proof -
    fix j
    assume j_lt: "j < n"
    have "ls ! j = map (poly (ps ! j)) (ds ! j)"
      by (rule layers) (use j_lt lens in simp_all)
    then show "length (ds ! j) = length (ls ! j)"
      by simp
  qed
  have init_len': "length (ls ! 0) = 2 ^ N"
    using ls0 init_len by simp
  have successors':
    "\<And>j. j < n \<Longrightarrow>
      p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    using successors by simp
  show ?thesis
    by (rule fri_successor_layer_lengths_power[
        OF init_len' n_le_N layer_lens successors' j_le])
qed

lemma fri_commit_outcome_initial_layer_length_power:
  assumes outcome:
    "fri_commit_outcome n cp d l m ps ds ls ms s t"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and init_len: "length l = 2 ^ N"
    and n_le_N: "n \<le> N"
    and j_le: "j \<le> n"
  shows "length (ls ! j) = 2 ^ (N - j)"
proof -
  from outcome consider
    (old) "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.fri_commit n [cp] [d] [l] [m]) s)"
  | (trace) "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.trace_fri_commit n [cp] [d] [l] [m]) s)"
  | (composition) "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.composition_fri_commit n [cp] [d] [l] [m]) s)"
    unfolding fri_commit_outcome_def by blast
  then show ?thesis
  proof cases
    case old
    show ?thesis
      by (rule fri_commit_initial_layer_length_power[
          OF old layers init_len n_le_N j_le])
  next
    case trace
    show ?thesis
      by (rule trace_fri_commit_initial_layer_length_power[
          OF trace layers init_len n_le_N j_le])
  next
    case composition
    show ?thesis
      by (rule composition_fri_commit_initial_layer_length_power[
          OF composition layers init_len n_le_N j_le])
  qed
qed

lemma trace_fri_commit_initial_domain_points:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.trace_fri_commit n [cp] [p.eval_domain] [l] [m]) s)"
    and j_le: "j \<le> n"
    and k_bound: "k < length (ds ! j)"
  shows "ds ! j ! k = ((p.h ^ k) * shift) ^ (2 ^ j)"
proof -
  have ds0: "ds ! 0 = p.eval_domain"
    using trace_fri_commit_initial_heads(2)[OF outcome] .
  from trace_fri_commit_initial_replay_successor_data[OF outcome]
  obtain roots challenges where
    successors:
      "\<And>j. j < n \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    by blast
  show ?thesis
    by (rule fri_successor_domain_points[
        OF ds0 successors j_le k_bound])
qed

lemma composition_fri_commit_initial_domain_points:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.composition_fri_commit n [cp] [p.eval_domain] [l] [m]) s)"
    and j_le: "j \<le> n"
    and k_bound: "k < length (ds ! j)"
  shows "ds ! j ! k = ((p.h ^ k) * shift) ^ (2 ^ j)"
proof -
  have ds0: "ds ! 0 = p.eval_domain"
    using composition_fri_commit_initial_heads(2)[OF outcome] .
  from composition_fri_commit_initial_replay_successor_data[OF outcome]
  obtain roots challenges where
    successors:
      "\<And>j. j < n \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    by blast
  show ?thesis
    by (rule fri_successor_domain_points[
        OF ds0 successors j_le k_bound])
qed

lemma fri_commit_outcome_initial_domain_points:
  assumes outcome:
    "fri_commit_outcome n cp p.eval_domain l m ps ds ls ms s t"
    and j_le: "j \<le> n"
    and k_bound: "k < length (ds ! j)"
  shows "ds ! j ! k = ((p.h ^ k) * shift) ^ (2 ^ j)"
proof -
  from outcome consider
    (old) "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.fri_commit n [cp] [p.eval_domain] [l] [m]) s)"
  | (trace) "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.trace_fri_commit n [cp] [p.eval_domain] [l] [m]) s)"
  | (composition) "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.composition_fri_commit n [cp] [p.eval_domain] [l] [m]) s)"
    unfolding fri_commit_outcome_def by blast
  then show ?thesis
  proof cases
    case old
    show ?thesis
      by (rule fri_commit_initial_domain_points[OF old j_le k_bound])
  next
    case trace
    show ?thesis
      by (rule trace_fri_commit_initial_domain_points[OF trace j_le k_bound])
  next
    case composition
    show ?thesis
      by (rule composition_fri_commit_initial_domain_points[
          OF composition j_le k_bound])
  qed
qed

lemma fri_degree_decreases:
  assumes "degree q > 0"
    and "p.next_fri_layer q d b = (q', d', l')"
  shows "degree q' < degree q"
  using assms p.degree_less_degree next_fri_layer_components(1) by blast

lemma degree_poly_of_list_less_length:
  assumes "xs \<noteq> []"
  shows "degree (poly_of_list xs) < length xs"
proof -
  have "degree (poly_of_list xs) = length (coeffs (poly_of_list xs)) - 1"
    by (simp add: degree_eq_length_coeffs)
  also have "... \<le> length xs - 1"
  proof -
    have "length (coeffs (poly_of_list xs)) \<le> length xs"
      by (simp add: coeffs_Poly length_strip_while_le)
    with assms show ?thesis by linarith
  qed
  also have "... < length xs"
    using assms by simp
  finally show ?thesis .
qed

lemma degree_nths_even_coeffs_le_half:
  "degree (poly_of_list (nths_pred (coeffs q) even)) \<le> degree q div 2"
proof (cases "coeffs q = []")
  case True
  then show ?thesis by simp
next
  case False
  let ?xs = "nths_pred (coeffs q) even"
  have len: "length ?xs = Suc (length (coeffs q)) div 2"
    by (rule nths_pred_even_length_eq)
  show ?thesis
  proof (cases "?xs = []")
    case True
    then show ?thesis by simp
  next
    case xs_ne: False
    have dlt: "degree (poly_of_list ?xs) < length ?xs"
      using xs_ne by (rule degree_poly_of_list_less_length)
    have "degree (poly_of_list ?xs) < Suc (length (coeffs q)) div 2"
      using dlt len by simp
    then have "degree (poly_of_list ?xs) \<le> (length (coeffs q) - 1) div 2"
      by linarith
    then show ?thesis
      by (simp add: degree_eq_length_coeffs)
  qed
qed

lemma degree_nths_odd_coeffs_le_half:
  "degree (poly_of_list (nths_pred (coeffs q) odd)) \<le> degree q div 2"
proof (cases "coeffs q = []")
  case True
  then show ?thesis by simp
next
  case False
  let ?xs = "nths_pred (coeffs q) odd"
  have len: "length ?xs = length (coeffs q) div 2"
    by (rule nths_pred_odd_length_eq)
  show ?thesis
  proof (cases "?xs = []")
    case True
    then show ?thesis by simp
  next
    case xs_ne: False
    have dlt: "degree (poly_of_list ?xs) < length ?xs"
      using xs_ne by (rule degree_poly_of_list_less_length)
    then have "degree (poly_of_list ?xs) < Suc (length (coeffs q)) div 2"
      using len by linarith
    then have "degree (poly_of_list ?xs) \<le> (length (coeffs q) - 1) div 2"
      by linarith
    then show ?thesis
      by (simp add: degree_eq_length_coeffs)
  qed
qed

lemma fri_degree_halves_polynomial:
  "degree (p.next_fri_polynomial q b) \<le> degree q div 2"
proof -
  define odd_coefficients where "odd_coefficients = nths_pred (coeffs q) odd"
  define even_coefficients where "even_coefficients = nths_pred (coeffs q) even"
  define oddp where "oddp = CP b * poly_of_list odd_coefficients"
  define evenp where "evenp = poly_of_list even_coefficients"
  have odd_le: "degree oddp \<le> degree q div 2"
  proof -
    have "degree oddp \<le> degree (CP b) + degree (poly_of_list odd_coefficients)"
      unfolding oddp_def by (rule degree_mult_le)
    also have "... \<le> degree q div 2"
      unfolding CP_def odd_coefficients_def
      using degree_nths_odd_coeffs_le_half[of q]
      by (simp add: monom_0)
    finally show ?thesis .
  qed
  have even_le: "degree evenp \<le> degree q div 2"
    unfolding evenp_def even_coefficients_def
    by (rule degree_nths_even_coeffs_le_half)
  have "degree (p.next_fri_polynomial q b) = degree (oddp + evenp)"
    unfolding p.next_fri_polynomial_def oddp_def evenp_def
      odd_coefficients_def even_coefficients_def
    by (simp add: Let_def)
  also have "... \<le> degree q div 2"
    using odd_le even_le by (rule degree_add_le)
  finally show ?thesis .
qed

lemma fri_degree_halves_layer:
  assumes "p.next_fri_layer q d b = (q', d', l')"
  shows "degree q' \<le> degree q div 2"
  using next_fri_layer_components(1)[OF assms] fri_degree_halves_polynomial by simp

lemma ceil_log_Suc_power_gt:
  "d < 2 ^ ceil_log (Suc d)"
proof (cases d)
  case 0
  then show ?thesis
    unfolding ceil_log_def by simp
next
  case (Suc d')
  then show ?thesis
    using floor_log_exp2_gt[of d]
    unfolding ceil_log_def
    by simp
qed

lemma trace_fri_rounds_enough:
  "ceil_log (degree p.f + 1) \<le> ceil_log clength"
proof -
  have "degree p.f + 1 \<le> clength"
    using trace_polynomial_degree_lt_clength by simp
  then show ?thesis
    using ceil_log_mono by blast
qed

lemma div_power_two_ceil_log_Suc:
  "d div 2 ^ ceil_log (Suc d) = 0"
  using ceil_log_Suc_power_gt[of d] by simp

lemma div_div_two_power:
  fixes m n :: nat
  shows "(m div 2 ^ n) div 2 = m div 2 ^ Suc n"
proof -
  have div_mult:
    "m div (2 ^ n * 2) = (m div 2 ^ n) div 2"
    using div_mult2_eq'[of m "2 ^ n" 2] by simp
  have "(m div 2 ^ n) div 2 = m div (2 ^ n * 2)"
    using div_mult by simp
  also have "... = m div 2 ^ Suc n"
    by (simp add: power_Suc mult.commute)
  finally show ?thesis .
qed

lemma fri_degree_chain_halves:
  assumes successors:
    "\<And>j. j < n \<Longrightarrow>
      p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and j_le: "j \<le> n"
  shows "degree (ps ! j) \<le> degree (ps ! 0) div 2 ^ j"
  using j_le
proof (induction j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  have j_lt: "j < n"
    using Suc.prems by simp
  have step:
    "degree (ps ! Suc j) \<le> degree (ps ! j) div 2"
    by (rule fri_degree_halves_layer[OF successors[OF j_lt]])
  also have "... \<le> (degree (ps ! 0) div 2 ^ j) div 2"
    by (rule div_le_mono) (rule Suc.IH, use Suc.prems in simp)
  also have "... = degree (ps ! 0) div 2 ^ Suc j"
    by (rule div_div_two_power)
  finally show ?case .
qed

lemma fri_degree_final_zero:
  assumes successors:
    "\<And>j. j < n \<Longrightarrow>
      p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and n_def: "n = ceil_log (degree (ps ! 0) + 1)"
  shows "degree (ps ! n) = 0"
proof -
  have "degree (ps ! n) \<le> degree (ps ! 0) div 2 ^ n"
    by (rule fri_degree_chain_halves[OF successors le_refl])
  also have "... = 0"
    using n_def div_power_two_ceil_log_Suc[of "degree (ps ! 0)"] by simp
  finally show ?thesis by simp
qed

lemma fri_degree_final_zero_ge:
  assumes successors:
    "\<And>j. j < n \<Longrightarrow>
      p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and enough: "ceil_log (degree (ps ! 0) + 1) \<le> n"
  shows "degree (ps ! n) = 0"
proof -
  have "degree (ps ! n) \<le> degree (ps ! 0) div 2 ^ n"
    by (rule fri_degree_chain_halves[OF successors le_refl])
  also have "... = 0"
  proof -
    have lt_ceil: "degree (ps ! 0) < 2 ^ ceil_log (degree (ps ! 0) + 1)"
      using ceil_log_Suc_power_gt[of "degree (ps ! 0)"] by simp
    also have "... \<le> 2 ^ n"
      using enough by simp
    finally show ?thesis
      by simp
  qed
  finally show ?thesis by simp
qed

lemma poly_degree_zero_const:
  assumes "degree q = 0"
  shows "poly q x = poly q y"
proof -
  have q_eq: "q = [: coeff q 0 :]"
    using degree_0_id[OF assms] by simp
  have "poly q x = coeff q 0"
    by (subst q_eq) simp
  also have "... = poly q y"
    by (subst q_eq) simp
  finally show ?thesis .
qed

lemma fri_final_layer_constant_value:
  assumes degree0: "degree (ps ! n) = 0"
    and layer: "ls ! n = map (poly (ps ! n)) (ds ! n)"
    and i_bound: "i < length (ls ! n)"
    and len_pos: "0 < length (ls ! n)"
  shows "ls ! n ! i = hd (ls ! n)"
proof -
  have ds_len: "length (ds ! n) = length (ls ! n)"
    using layer by simp
  then have ds_ne: "ds ! n \<noteq> []"
    using len_pos by auto
  have "ls ! n ! i = poly (ps ! n) (ds ! n ! i)"
    using layer i_bound by simp
  also have "... = poly (ps ! n) (hd (ds ! n))"
    by (rule poly_degree_zero_const[OF degree0])
  also have "... = hd (map (poly (ps ! n)) (ds ! n))"
  proof -
    have "hd (map (poly (ps ! n)) (ds ! n)) =
      poly (ps ! n) (hd (ds ! n))"
      by (rule hd_map[OF ds_ne])
    then show ?thesis by simp
  qed
  also have "... = hd (ls ! n)"
    using layer by simp
  finally show ?thesis .
qed

lemma honest_fri_final_layer_equals_sent:
  assumes fri:
    "Some ((ps, ds, ls, ms), s6) \<in>
      set_dist (execute
        (p.fri_commit nrounds [cp'] [p.eval_domain] [p.cp_eval as] [cp_merkle]) s5)"
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and init_len: "length (p.cp_eval as) = 2 ^ N"
    and n_le_N: "nrounds \<le> N"
    and nrounds_def: "nrounds = ceil_log (degree cp' + 1)"
    and successors:
      "\<And>j. j < nrounds \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and i_bound: "i < length (ls ! nrounds)"
  shows "ls ! nrounds ! i = hd (last ls)"
proof -
  have ps0: "ps ! 0 = cp'"
    using fri_commit_initial_heads(1)[OF fri] .
  have n_def: "nrounds = ceil_log (degree (ps ! 0) + 1)"
    using nrounds_def ps0 by simp
  have degree0: "degree (ps ! nrounds) = 0"
    by (rule fri_degree_final_zero[OF successors n_def])
  have layer_n: "ls ! nrounds = map (poly (ps ! nrounds)) (ds ! nrounds)"
    by (rule layers) (use len_ps len_ds len_ls in simp_all)
  have len_pos: "0 < length (ls ! nrounds)"
    using fri_commit_initial_layer_length_power[OF fri layers init_len n_le_N, of nrounds]
    by simp
  have "ls ! nrounds ! i = hd (ls ! nrounds)"
    by (rule fri_final_layer_constant_value[OF degree0 layer_n i_bound len_pos])
  also have "... = hd (last ls)"
  proof -
    have ls_ne: "ls \<noteq> []"
      using len_ls by auto
    have "last ls = ls ! nrounds"
      using last_conv_nth[OF ls_ne] len_ls by simp
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma honest_fri_final_layer_equals_sent_initial:
  assumes fri:
    "Some ((ps, ds, ls, ms), s6) \<in>
      set_dist (execute
        (p.fri_commit nrounds [cp] [p.eval_domain] [l0] [m0]) s5)"
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and init_len: "length l0 = 2 ^ N"
    and n_le_N: "nrounds \<le> N"
    and nrounds_enough: "ceil_log (degree cp + 1) \<le> nrounds"
    and successors:
      "\<And>j. j < nrounds \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and i_bound: "i < length (ls ! nrounds)"
  shows "ls ! nrounds ! i = hd (last ls)"
proof -
  have ps0: "ps ! 0 = cp"
    using fri_commit_initial_heads(1)[OF fri] .
  have n_enough: "ceil_log (degree (ps ! 0) + 1) \<le> nrounds"
    using nrounds_enough ps0 by simp
  have degree0: "degree (ps ! nrounds) = 0"
    by (rule fri_degree_final_zero_ge[OF successors n_enough])
  have layer_n: "ls ! nrounds = map (poly (ps ! nrounds)) (ds ! nrounds)"
    by (rule layers) (use len_ps len_ds len_ls in simp_all)
  have len_pos: "0 < length (ls ! nrounds)"
    using fri_commit_initial_layer_length_power[OF fri layers init_len n_le_N, of nrounds]
    by simp
  have "ls ! nrounds ! i = hd (ls ! nrounds)"
    by (rule fri_final_layer_constant_value[OF degree0 layer_n i_bound len_pos])
  also have "... = hd (last ls)"
  proof -
    have ls_ne: "ls \<noteq> []"
      using len_ls by auto
    have "last ls = ls ! nrounds"
      using last_conv_nth[OF ls_ne] len_ls by simp
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma honest_fri_final_layer_equals_sent_shape:
  assumes fri:
    "fri_commit_outcome nrounds cp p.eval_domain l0 m0 ps ds ls ms s5 s6"
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and init_len: "length l0 = 2 ^ N"
    and n_le_N: "nrounds \<le> N"
    and nrounds_def: "nrounds = ceil_log (degree cp + 1)"
    and successors:
      "\<And>j. j < nrounds \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and i_bound: "i < length (ls ! nrounds)"
  shows "ls ! nrounds ! i = hd (last ls)"
proof -
  have ps0: "ps ! 0 = cp"
    using fri_commit_outcome_initial_heads(1)[OF fri] .
  have n_def: "nrounds = ceil_log (degree (ps ! 0) + 1)"
    using nrounds_def ps0 by simp
  have degree0: "degree (ps ! nrounds) = 0"
    by (rule fri_degree_final_zero[OF successors n_def])
  have layer_n: "ls ! nrounds = map (poly (ps ! nrounds)) (ds ! nrounds)"
    by (rule layers) (use len_ps len_ds len_ls in simp_all)
  have len_pos: "0 < length (ls ! nrounds)"
    using fri_commit_outcome_initial_layer_length_power[
      OF fri layers init_len n_le_N, of nrounds]
    by simp
  have "ls ! nrounds ! i = hd (ls ! nrounds)"
    by (rule fri_final_layer_constant_value[OF degree0 layer_n i_bound len_pos])
  also have "... = hd (last ls)"
  proof -
    have ls_ne: "ls \<noteq> []"
      using len_ls by auto
    have "last ls = ls ! nrounds"
      using last_conv_nth[OF ls_ne] len_ls by simp
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma honest_fri_final_layer_equals_sent_initial_shape:
  assumes fri:
    "fri_commit_outcome nrounds cp p.eval_domain l0 m0 ps ds ls ms s5 s6"
    and len_ps: "length ps = Suc nrounds"
    and len_ds: "length ds = Suc nrounds"
    and len_ls: "length ls = Suc nrounds"
    and layers:
      "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
        ls ! i = map (poly (ps ! i)) (ds ! i)"
    and init_len: "length l0 = 2 ^ N"
    and n_le_N: "nrounds \<le> N"
    and nrounds_enough: "ceil_log (degree cp + 1) \<le> nrounds"
    and successors:
      "\<And>j. j < nrounds \<Longrightarrow>
        p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    and i_bound: "i < length (ls ! nrounds)"
  shows "ls ! nrounds ! i = hd (last ls)"
proof -
  have ps0: "ps ! 0 = cp"
    using fri_commit_outcome_initial_heads(1)[OF fri] .
  have n_enough: "ceil_log (degree (ps ! 0) + 1) \<le> nrounds"
    using nrounds_enough ps0 by simp
  have degree0: "degree (ps ! nrounds) = 0"
    by (rule fri_degree_final_zero_ge[OF successors n_enough])
  have layer_n: "ls ! nrounds = map (poly (ps ! nrounds)) (ds ! nrounds)"
    by (rule layers) (use len_ps len_ds len_ls in simp_all)
  have len_pos: "0 < length (ls ! nrounds)"
    using fri_commit_outcome_initial_layer_length_power[
      OF fri layers init_len n_le_N, of nrounds]
    by simp
  have "ls ! nrounds ! i = hd (ls ! nrounds)"
    by (rule fri_final_layer_constant_value[OF degree0 layer_n i_bound len_pos])
  also have "... = hd (last ls)"
  proof -
    have ls_ne: "ls \<noteq> []"
      using len_ls by auto
    have "last ls = ls ! nrounds"
      using last_conv_nth[OF ls_ne] len_ls by simp
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma poly_of_list_even_odd_decompose:
  fixes xs :: "'f list"
    and x :: 'f
  shows
  "poly (poly_of_list xs) x =
    poly (poly_of_list (nths_pred xs even)) (x * x) +
      x * poly (poly_of_list (nths_pred xs odd)) (x * x)"
proof (induction xs rule: measure_induct_rule[of length])
  case (less xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a ys)
    note xs_eq = Cons
    show ?thesis
    proof (cases ys)
      case Nil
      then show ?thesis
        unfolding xs_eq by (simp add: nths_Cons)
    next
      case (Cons b zs)
      note ys_eq = Cons
      have even_tail:
        "nths_pred (a # b # zs) even = a # nths_pred zs even"
        unfolding nths_pred_def by (simp add: nths_Cons)
      have odd_tail:
        "nths_pred (a # b # zs) odd = b # nths_pred zs odd"
        unfolding nths_pred_def by (simp add: nths_Cons)
      have zs_less: "length zs < length xs"
        unfolding xs_eq ys_eq by simp
      have poly_tail:
        "poly (poly_of_list zs) x =
          poly (poly_of_list (nths_pred zs even)) (x * x) +
            x * poly (poly_of_list (nths_pred zs odd)) (x * x)"
        by (rule less.IH[OF zs_less])
      show ?thesis
        unfolding xs_eq ys_eq even_tail odd_tail
        using poly_tail
        by (simp add: algebra_simps power2_eq_square)
    qed
  qed
qed

lemma poly_even_part_reconstruct:
  fixes q :: "'f poly"
    and x :: 'f
  assumes two_nonzero: "(2::'f) \<noteq> 0"
  shows
  "poly (poly_of_list (nths_pred (coeffs q) even)) (x * x) =
    (poly q x + poly q (-x)) div 2"
proof -
  have decomp_x:
    "poly q x =
      poly (poly_of_list (nths_pred (coeffs q) even)) (x * x) +
        x * poly (poly_of_list (nths_pred (coeffs q) odd)) (x * x)"
    using poly_of_list_even_odd_decompose[of "coeffs q" x]
    by simp
  have decomp_neg:
    "poly q (-x) =
      poly (poly_of_list (nths_pred (coeffs q) even)) (x * x) -
        x * poly (poly_of_list (nths_pred (coeffs q) odd)) (x * x)"
    using poly_of_list_even_odd_decompose[of "coeffs q" "-x"]
    by (simp add: algebra_simps power2_eq_square)
  show ?thesis
    using decomp_x decomp_neg two_nonzero
    by (simp add: field_simps)
qed

lemma poly_odd_part_reconstruct:
  fixes q :: "'f poly"
    and x :: 'f
  assumes two_nonzero: "(2::'f) \<noteq> 0"
    and x_nonzero: "x \<noteq> 0"
  shows "poly (poly_of_list (nths_pred (coeffs q) odd)) (x * x) =
    (poly q x - poly q (-x)) div (2 * x)"
proof -
  have decomp_x:
    "poly q x =
      poly (poly_of_list (nths_pred (coeffs q) even)) (x * x) +
        x * poly (poly_of_list (nths_pred (coeffs q) odd)) (x * x)"
    using poly_of_list_even_odd_decompose[of "coeffs q" x]
    by simp
  have decomp_neg:
    "poly q (-x) =
      poly (poly_of_list (nths_pred (coeffs q) even)) (x * x) -
        x * poly (poly_of_list (nths_pred (coeffs q) odd)) (x * x)"
    using poly_of_list_even_odd_decompose[of "coeffs q" "-x"]
    by (simp add: algebra_simps power2_eq_square)
  show ?thesis
    using decomp_x decomp_neg two_nonzero x_nonzero
    by (simp add: field_simps mult.commute)
qed

lemma next_fri_polynomial_fold:
  fixes q :: "'f poly"
    and b z :: 'f
  assumes two_nonzero: "(2::'f) \<noteq> 0"
    and z_nonzero: "z \<noteq> 0"
  shows
    "((poly q z + poly q (- z)) div 2 +
        b * ((poly q z - poly q (- z)) div (2 * z))) =
      poly (p.next_fri_polynomial q b) (z * z)"
proof -
  let ?E = "poly (poly_of_list (nths_pred (coeffs q) even)) (z * z)"
  let ?O = "poly (poly_of_list (nths_pred (coeffs q) odd)) (z * z)"
  have even:
    "?E = (poly q z + poly q (- z)) div 2"
    by (rule poly_even_part_reconstruct[OF two_nonzero])
  have odd:
    "?O = (poly q z - poly q (- z)) div (2 * z)"
    by (rule poly_odd_part_reconstruct[OF two_nonzero z_nonzero])
  have next_poly_eval:
    "poly (p.next_fri_polynomial q b) (z * z) = b * ?O + ?E"
    unfolding p.next_fri_polynomial_def CP_def
    by (simp add: Let_def monom_0 algebra_simps)
  have lhs:
    "((poly q z + poly q (- z)) div 2 +
        b * ((poly q z - poly q (- z)) div (2 * z))) =
      ?E + b * ?O"
    using even odd by simp
  also have "... = poly (p.next_fri_polynomial q b) (z * z)"
    using next_poly_eval by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma fri_fold_value_poly_next:
  fixes q :: "'f poly"
    and b z :: 'f
  assumes two_nonzero: "(2::'f) \<noteq> 0"
    and z_nonzero: "z \<noteq> 0"
    and len_eq: "len = length l"
    and l_eval: "l = map (poly q) d"
    and d_len: "length d = length l"
    and i_bound: "i < len"
    and z_eq: "z = ((p.h ^ i) * shift) ^ pw"
    and d_i: "d ! i = z"
    and d_sib: "d ! ((i + len div 2) mod len) = - z"
  shows "fri_fold_value b l i len pw =
    poly (p.next_fri_polynomial q b) (z * z)"
proof -
  let ?sidx = "(i + len div 2) mod len"
  have len_pos: "0 < len"
    using i_bound by simp
  have i_d_bound: "i < length d"
    using i_bound len_eq d_len by simp
  have sib_l_bound: "?sidx < length l"
    using len_pos len_eq by simp
  have sib_d_bound: "?sidx < length d"
    using sib_l_bound d_len by simp
  have l_i: "l ! i = poly q z"
    using l_eval d_i i_d_bound by simp
  have l_sib: "l ! ?sidx = poly q (- z)"
    using l_eval d_sib sib_d_bound by simp
  show ?thesis
    unfolding fri_fold_value_def
    using l_i l_sib z_eq next_fri_polynomial_fold[OF two_nonzero z_nonzero, of q b]
    by simp
qed

lemma fri_fold_value_next_layer_value:
  fixes q :: "'f poly"
    and b z :: 'f
  assumes two_nonzero: "(2::'f) \<noteq> 0"
    and z_nonzero: "z \<noteq> 0"
    and layer: "p.next_fri_layer q d b = (q', d', l')"
    and len_eq: "len = length l"
    and l_eval: "l = map (poly q) d"
    and d_len: "length d = length l"
    and i_bound: "i < len"
    and z_eq: "z = ((p.h ^ i) * shift) ^ pw"
    and d_i: "d ! i = z"
    and d_sib: "d ! ((i + len div 2) mod len) = - z"
    and next_idx_bound: "i mod (len div 2) < length d'"
    and d_next: "d' ! (i mod (len div 2)) = z * z"
  shows "fri_fold_value b l i len pw = l' ! (i mod (len div 2))"
proof -
  have fold:
    "fri_fold_value b l i len pw =
      poly (p.next_fri_polynomial q b) (z * z)"
    by (rule fri_fold_value_poly_next[
        OF two_nonzero z_nonzero len_eq l_eval d_len i_bound z_eq d_i d_sib])
  have q'_eq: "q' = p.next_fri_polynomial q b"
    using next_fri_layer_components(1)[OF layer] .
  have l'_eq: "l' = map (poly q') d'"
    using next_fri_layer_components(3)[OF layer] .
  have "l' ! (i mod (len div 2)) = poly q' (z * z)"
    using l'_eq next_idx_bound d_next by simp
  then show ?thesis
    using fold q'_eq by simp
qed

lemma honest_fri_layer_decommitment_step_created_next_value:
  fixes q q' :: "'f poly"
    and d d' l l' :: "'f list"
  assumes created: "p.created_tree l m s0"
    and len_eq: "len = length l"
    and len_pow: "length l = 2 ^ n"
    and i_bound: "i < len"
    and x_eq: "x = l ! i"
    and ext: "s0 \<le> s"
    and root: "fr = value m"
    and tr:
      "start =
        s\<lparr>PTranscript := fri_layer_decommitment_transcript l m i len @ rest\<rparr>"
    and layer: "p.next_fri_layer q d b = (q', d', l')"
    and l_eval: "l = map (poly q) d"
    and d_len: "length d = length l"
    and z_eq: "z = ((p.h ^ i) * shift) ^ pw"
    and d_i: "d ! i = z"
    and d_sib: "d ! ((i + len div 2) mod len) = - z"
    and next_idx_bound: "i mod (len div 2) < length d'"
    and d_next: "d' ! (i mod (len div 2)) = z * z"
  shows
    "None \<notin> dom (dist (execute (fri_verifier_layer b fr i x len pw) start))"
    "\<And>res t'. Some (res, t') \<in>
        set_dist (execute (fri_verifier_layer b fr i x len pw) start) \<Longrightarrow>
      res =
        (i mod (len div 2), l' ! (i mod (len div 2)), len div 2, pw + pw) \<and>
      PTranscript t' = rest \<and>
      start \<le> t'"
proof -
  show "None \<notin> dom (dist (execute (fri_verifier_layer b fr i x len pw) start))"
    by (rule honest_fri_layer_decommitment_step_created(1)[
        OF created len_eq len_pow i_bound x_eq ext root tr])
  fix res t'
  assume outcome:
    "Some (res, t') \<in>
      set_dist (execute (fri_verifier_layer b fr i x len pw) start)"
  have step:
    "res =
      (i mod (len div 2), fri_fold_value b l i len pw, len div 2, pw + pw) \<and>
     PTranscript t' = rest \<and>
     start \<le> t'"
    by (rule honest_fri_layer_decommitment_step_created(2)[
        OF created len_eq len_pow i_bound x_eq ext root tr outcome])
  have z_nonzero: "z \<noteq> 0"
    using z_eq verifier_domain_point_nonzero by simp
  have fold_eq:
    "fri_fold_value b l i len pw = l' ! (i mod (len div 2))"
    by (rule fri_fold_value_next_layer_value[
        OF p.two_nonzero z_nonzero layer len_eq l_eval d_len i_bound z_eq
          d_i d_sib next_idx_bound d_next])
  show
    "res =
      (i mod (len div 2), l' ! (i mod (len div 2)), len div 2, pw + pw) \<and>
     PTranscript t' = rest \<and>
     start \<le> t'"
    using step fold_eq by simp
qed

lemma honest_fri_layer_decommitment_step_created_next_value_domain:
  fixes q q' :: "'f poly"
    and d d' l l' :: "'f list"
  assumes created: "p.created_tree l m s0"
    and len_eq: "len = length l"
    and len_pow: "length l = 2 ^ n"
    and i_bound: "i < len"
    and x_eq: "x = l ! i"
    and ext: "s0 \<le> s"
    and root: "fr = value m"
    and tr:
      "start =
        s\<lparr>PTranscript := fri_layer_decommitment_transcript l m i len @ rest\<rparr>"
    and layer: "p.next_fri_layer q d b = (q', d', l')"
    and l_eval: "l = map (poly q) d"
    and d_len: "length d = length l"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
    and d_i_point: "d ! i = ((p.h ^ i) * shift) ^ pw"
    and d_sib_point:
      "d ! ((i + len div 2) mod len) =
        ((p.h ^ ((i + len div 2) mod len)) * shift) ^ pw"
    and next_idx_bound: "i mod (len div 2) < length d'"
    and d_next:
      "d' ! (i mod (len div 2)) =
        ((p.h ^ i) * shift) ^ pw * ((p.h ^ i) * shift) ^ pw"
  shows
    "None \<notin> dom (dist (execute (fri_verifier_layer b fr i x len pw) start))"
    "\<And>res t'. Some (res, t') \<in>
        set_dist (execute (fri_verifier_layer b fr i x len pw) start) \<Longrightarrow>
      res =
        (i mod (len div 2), l' ! (i mod (len div 2)), len div 2, pw + pw) \<and>
      PTranscript t' = rest \<and>
      start \<le> t'"
proof -
  let ?z = "((p.h ^ i) * shift) ^ pw"
  have len_pos: "0 < len"
    using i_bound by simp
  have d_sib: "d ! ((i + len div 2) mod len) = - ?z"
    by (rule fri_sibling_domain_at[OF len_pos even_len round refl d_sib_point])
  show "None \<notin> dom (dist (execute (fri_verifier_layer b fr i x len pw) start))"
    by (rule honest_fri_layer_decommitment_step_created_next_value(1)[
        OF created len_eq len_pow i_bound x_eq ext root tr layer l_eval d_len
          refl d_i_point d_sib next_idx_bound d_next])
  fix res t'
  assume outcome:
    "Some (res, t') \<in>
      set_dist (execute (fri_verifier_layer b fr i x len pw) start)"
	  show
	    "res =
	      (i mod (len div 2), l' ! (i mod (len div 2)), len div 2, pw + pw) \<and>
	     PTranscript t' = rest \<and>
	     start \<le> t'"
	    by (rule honest_fri_layer_decommitment_step_created_next_value(2)[
	        OF created len_eq len_pow i_bound x_eq ext root tr layer l_eval d_len
	          refl d_i_point d_sib next_idx_bound d_next outcome])
	qed

lemma honest_fri_layer_decommitment_step_created_next_value_domain_state:
  fixes q q' :: "'f poly"
    and d d' l l' :: "'f list"
  assumes created: "p.created_tree l m s0"
    and len_eq: "len = length l"
    and len_pow: "length l = 2 ^ n"
    and i_bound: "i < len"
    and x_eq: "x = l ! i"
    and ext: "s0 \<le> s"
    and root: "fr = value m"
    and tr:
      "start =
        s\<lparr>PTranscript := fri_layer_decommitment_transcript l m i len @ rest\<rparr>"
    and layer: "p.next_fri_layer q d b = (q', d', l')"
    and l_eval: "l = map (poly q) d"
    and d_len: "length d = length l"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
    and d_i_point: "d ! i = ((p.h ^ i) * shift) ^ pw"
    and d_sib_point:
      "d ! ((i + len div 2) mod len) =
        ((p.h ^ ((i + len div 2) mod len)) * shift) ^ pw"
    and next_idx_bound: "i mod (len div 2) < length d'"
    and d_next:
      "d' ! (i mod (len div 2)) =
        ((p.h ^ i) * shift) ^ pw * ((p.h ^ i) * shift) ^ pw"
    and outcome:
      "Some (res, t') \<in>
        set_dist (execute (fri_verifier_layer b fr i x len pw) start)"
  shows
    "res =
      (i mod (len div 2), l' ! (i mod (len div 2)), len div 2, pw + pw) \<and>
     PTranscript t' = rest \<and>
     start \<le> t' \<and>
     PState t' = foldl concat (PState s) (fri_layer_decommitment_transcript l m i len)"
proof -
  have old:
    "res =
      (i mod (len div 2), l' ! (i mod (len div 2)), len div 2, pw + pw) \<and>
     PTranscript t' = rest \<and>
     start \<le> t'"
    by (rule honest_fri_layer_decommitment_step_created_next_value_domain(2)[
        OF created len_eq len_pow i_bound x_eq ext root tr layer l_eval d_len
          even_len round d_i_point d_sib_point next_idx_bound d_next outcome])
  have path_i:
    "length (get_authentication_path len i m) = floor_log len"
    using created_tree_get_authentication_path_len[
      OF created len_pow, of i] i_bound len_eq by simp
  have len_pos: "0 < len"
    using i_bound by simp
  have sidx_bound:
    "(i + len div 2) mod len < length l"
    using len_pos len_eq by simp
  have path_s:
    "length (get_authentication_path len ((i + len div 2) mod len) m) =
      floor_log len"
    using created_tree_get_authentication_path_len[
      OF created len_pow, of "(i + len div 2) mod len"] sidx_bound len_eq
    by simp
  have state:
    "PState t' = foldl concat (PState s) (fri_layer_decommitment_transcript l m i len)"
    using honest_fri_layer_decommitment_outcome(3)[
      OF len_eq i_bound path_i path_s outcome[unfolded fri_verifier_layer_def tr]] .
  show ?thesis
    using old state by simp
qed

end

end
