(*  Title:      Stark/Completeness_Transcript.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Completeness_Transcript
  imports Completeness_Algebra
begin

section \<open>Honest Transcript and Hash Replay\<close>

text \<open>Transcript-extension and hash-extension lemmas for honest prover execution.\<close>

context verification
begin

lemma transcript_send_outcome:
  assumes "Some ((), t) \<in> set_dist (execute (p.send x) s)"
  shows "t = s\<lparr>PState := concat (PState s) x, PTranscript := x # PTranscript s\<rparr>"
  using p.send_outcome[OF assms] .

lemma send_transcript_extends:
  assumes "Some ((), t) \<in> set_dist (execute (p.send x) s)"
  shows "transcript_extends t s"
  using transcript_send_outcome[OF assms]
  unfolding transcript_extends_def by auto

lemma send_hash_extends:
  assumes "Some ((), t) \<in> set_dist (execute (p.send x) s)"
  shows "s \<le> t"
  using p.send_outcome[OF assms]
  unfolding less_eq_hash_ext_def less_eq_fmap_def by simp

lemma transcript_read_cons_outcome:
  assumes "Some (y, t) \<in> set_dist (execute p.read (s\<lparr>PTranscript := x # xs\<rparr>))"
  shows
    "y = x \<and>
     t = s\<lparr>PState := concat (PState s) x, PTranscript := xs\<rparr>"
  using p.read_cons_outcome[OF assms] .

lemma create_preserves_transcript:
  assumes outcome: "Some (r, t) \<in> set_dist (execute (p.create xs) s)"
  shows "PTranscript t = PTranscript s"
  by (rule p.create_preserves_channel(2)[OF outcome])

lemma create_preserves_state:
  assumes outcome: "Some (r, t) \<in> set_dist (execute (p.create xs) s)"
  shows "PState t = PState s"
  by (rule p.create_preserves_channel(1)[OF outcome])

lemma create_transcript_extends:
  assumes "Some (r, t) \<in> set_dist (execute (p.create xs) s)"
  shows "transcript_extends t s"
  using create_preserves_transcript[OF assms]
  unfolding transcript_extends_def by auto

lemma create_hash_extends:
  assumes "Some (r, t) \<in> set_dist (execute (p.create xs) s)"
  shows "s \<le> t"
  using p.create_outcome[OF assms] by simp

lemma receive_random_field_element_preserves_transcript:
  assumes "Some (a, t) \<in> set_dist (execute p.receive_random_field_element s)"
  shows "PTranscript t = PTranscript s"
  using p.receive_random_field_element_outcome[OF assms] by simp

lemma receive_random_field_element_transcript_extends:
  assumes "Some (a, t) \<in> set_dist (execute p.receive_random_field_element s)"
  shows "transcript_extends t s"
  using receive_random_field_element_preserves_transcript[OF assms]
  unfolding transcript_extends_def by auto

lemma receive_alpha_challenge_preserves_transcript:
  assumes "Some (a, t) \<in> set_dist (execute p.receive_alpha_challenge s)"
  shows "PTranscript t = PTranscript s"
  using p.receive_alpha_challenge_outcome[OF assms] by simp

lemma receive_alpha_challenge_transcript_extends:
  assumes "Some (a, t) \<in> set_dist (execute p.receive_alpha_challenge s)"
  shows "transcript_extends t s"
  using receive_alpha_challenge_preserves_transcript[OF assms]
  unfolding transcript_extends_def by auto

lemma receive_query_index_challenge_preserves_transcript:
  assumes "Some (a, t) \<in> set_dist (execute p.receive_query_index_challenge s)"
  shows "PTranscript t = PTranscript s"
  using p.receive_query_index_challenge_outcome[OF assms] by simp

lemma receive_query_index_challenge_transcript_extends:
  assumes "Some (a, t) \<in> set_dist (execute p.receive_query_index_challenge s)"
  shows "transcript_extends t s"
  using receive_query_index_challenge_preserves_transcript[OF assms]
  unfolding transcript_extends_def by auto

lemma receive_random_field_element_outcome:
  assumes outcome: "Some (a, t) \<in> set_dist (execute p.receive_random_field_element s)"
  shows
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t) (FiatShamirChallenge (PState s)) = Some a"
  by (rule p.receive_random_field_element_outcome[OF outcome])

lemma bind_transcript_extends:
  assumes outcome: "Some (y, t) \<in> set_dist (execute (m \<bind> k) s)"
    and m_ext: "\<And>x u. Some (x, u) \<in> set_dist (execute m s) \<Longrightarrow>
      transcript_extends u s"
    and k_ext: "\<And>x u y t. Some (x, u) \<in> set_dist (execute m s) \<Longrightarrow>
      Some (y, t) \<in> set_dist (execute (k x) u) \<Longrightarrow>
      transcript_extends t u"
  shows "transcript_extends t s"
proof -
  from outcome obtain x u where
    mx: "Some (x, u) \<in> set_dist (execute m s)"
    and ky: "Some (y, t) \<in> set_dist (execute (k x) u)"
    by (auto elim!: p.set_dist_bindE)
  show ?thesis
    using m_ext[OF mx] k_ext[OF mx ky] by (rule transcript_extends_trans)
qed

lemma mmap_transcript_extends:
  assumes outcome: "Some (xs, t) \<in> set_dist (execute (mmap ms) s)"
    and step: "\<And>m x u v. m \<in> set ms \<Longrightarrow>
      Some (x, v) \<in> set_dist (execute m u) \<Longrightarrow>
      transcript_extends v u"
  shows "transcript_extends t s"
  using outcome step
proof (induction ms arbitrary: xs s t)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
  from Cons.prems(1) obtain x u xs' where
    head: "Some (x, u) \<in> set_dist (execute m s)"
    and tail: "Some (xs', t) \<in> set_dist (execute (mmap ms) u)"
    by (auto elim!: p.set_dist_bindE)
  have m_in: "m \<in> set (m # ms)"
    by simp
  have head_ext: "transcript_extends u s"
    using Cons.prems(2)[OF m_in head] .
  have tail_step:
    "\<And>m' x' u' v'. m' \<in> set ms \<Longrightarrow>
      Some (x', v') \<in> set_dist (execute m' u') \<Longrightarrow>
      transcript_extends v' u'"
    using Cons.prems(2) by auto
  have tail_ext: "transcript_extends t u"
    by (rule Cons.IH[OF tail tail_step])
  show ?case
    using head_ext tail_ext by (rule transcript_extends_trans)
qed

lemma mfold_transcript_extends:
  assumes outcome: "Some (x, t) \<in> set_dist (execute (mfold a ms) s)"
    and step: "\<And>m a0 y u v. m \<in> set ms \<Longrightarrow>
      Some (y, v) \<in> set_dist (execute (m a0) u) \<Longrightarrow>
      transcript_extends v u"
  shows "transcript_extends t s"
  using outcome step
proof (induction ms arbitrary: a x s t)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
  from Cons.prems(1) obtain y u where
    head: "Some (y, u) \<in> set_dist (execute (m a) s)"
    and tail: "Some (x, t) \<in> set_dist (execute (mfold y ms) u)"
    by (auto elim!: p.set_dist_bindE)
  have m_in: "m \<in> set (m # ms)"
    by simp
  have head_ext: "transcript_extends u s"
    using Cons.prems(2)[OF m_in head] .
  have tail_step:
    "\<And>m' a0 y' u' v'. m' \<in> set ms \<Longrightarrow>
      Some (y', v') \<in> set_dist (execute (m' a0) u') \<Longrightarrow>
      transcript_extends v' u'"
  proof -
    fix m' a0 y' u' v'
    assume m'_in_tail: "m' \<in> set ms"
      and out: "Some (y', v') \<in> set_dist (execute (m' a0) u')"
    have m'_in: "m' \<in> set (m # ms)"
      using m'_in_tail by simp
    show "transcript_extends v' u'"
      using Cons.prems(2)[OF m'_in out] .
  qed
  have tail_ext: "transcript_extends t u"
    by (rule Cons.IH[OF tail tail_step])
  show ?case
    using head_ext tail_ext by (rule transcript_extends_trans)
qed

lemma mmap_hash_extends:
  fixes s t :: "('f, 'more) protocol_channel_scheme"
  assumes outcome: "Some (xs, t) \<in> set_dist (execute (mmap ms) s)"
    and step: "\<And>m x u v. m \<in> set ms \<Longrightarrow>
      Some (x, v) \<in> set_dist (execute m u) \<Longrightarrow>
      u \<le> v"
  shows "s \<le> t"
  using outcome step
proof (induction ms arbitrary: xs s t)
  case Nil
  have t_eq: "t = s"
    using Nil.prems(1) by simp
  show ?case
    unfolding t_eq less_eq_hash_ext_def less_eq_fmap_def by simp
next
  case (Cons m ms)
  from Cons.prems(1) obtain x u xs' where
    head: "Some (x, u) \<in> set_dist (execute m s)"
    and tail: "Some (xs', t) \<in> set_dist (execute (mmap ms) u)"
    by (auto elim!: p.set_dist_bindE)
  have m_in: "m \<in> set (m # ms)"
    by simp
  have head_ext: "s \<le> u"
    using Cons.prems(2)[OF m_in head] .
  have tail_step:
    "\<And>m' x' u' v'. m' \<in> set ms \<Longrightarrow>
      Some (x', v') \<in> set_dist (execute m' u') \<Longrightarrow>
      u' \<le> v'"
  proof -
    fix m' x' u' v'
    assume m'_in_tail: "m' \<in> set ms"
      and out: "Some (x', v') \<in> set_dist (execute m' u')"
    have m'_in: "m' \<in> set (m # ms)"
      using m'_in_tail by simp
    show "u' \<le> v'"
      using Cons.prems(2)[OF m'_in out] .
  qed
  have tail_ext: "u \<le> t"
    by (rule Cons.IH[OF tail tail_step])
  show ?case
    using head_ext tail_ext by (rule p.hash_ext_trans)
qed

lemma mfold_hash_extends:
  fixes s t :: "('f, 'more) protocol_channel_scheme"
  assumes outcome: "Some (x, t) \<in> set_dist (execute (mfold a ms) s)"
    and step: "\<And>m a0 y u v. m \<in> set ms \<Longrightarrow>
      Some (y, v) \<in> set_dist (execute (m a0) u) \<Longrightarrow>
      u \<le> v"
  shows "s \<le> t"
  using outcome step
proof (induction ms arbitrary: a x s t)
  case Nil
  have t_eq: "t = s"
    using Nil.prems(1) by simp
  show ?case
    unfolding t_eq less_eq_hash_ext_def less_eq_fmap_def by simp
next
  case (Cons m ms)
  from Cons.prems(1) obtain y u where
    head: "Some (y, u) \<in> set_dist (execute (m a) s)"
    and tail: "Some (x, t) \<in> set_dist (execute (mfold y ms) u)"
    by (auto elim!: p.set_dist_bindE)
  have m_in: "m \<in> set (m # ms)"
    by simp
  have head_ext: "s \<le> u"
    using Cons.prems(2)[OF m_in head] .
  have tail_step:
    "\<And>m' a0 y' u' v'. m' \<in> set ms \<Longrightarrow>
      Some (y', v') \<in> set_dist (execute (m' a0) u') \<Longrightarrow>
      u' \<le> v'"
  proof -
    fix m' a0 y' u' v'
    assume m'_in_tail: "m' \<in> set ms"
      and out: "Some (y', v') \<in> set_dist (execute (m' a0) u')"
    have m'_in: "m' \<in> set (m # ms)"
      using m'_in_tail by simp
    show "u' \<le> v'"
      using Cons.prems(2)[OF m'_in out] .
  qed
  have tail_ext: "u \<le> t"
    by (rule Cons.IH[OF tail tail_step])
	  show ?case
	    using head_ext tail_ext by (rule p.hash_ext_trans)
	qed

lemma mmap_preserves_query_counter:
  fixes s t :: "('f, 'more) protocol_channel_scheme"
  assumes outcome: "Some (xs, t) \<in> set_dist (execute (mmap ms) s)"
    and step: "\<And>m x u v. m \<in> set ms \<Longrightarrow>
      Some (x, v) \<in> set_dist (execute m u) \<Longrightarrow>
      PQueryCounter v = PQueryCounter u"
  shows "PQueryCounter t = PQueryCounter s"
  using outcome step
proof (induction ms arbitrary: xs s t)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
	  from Cons.prems(1) obtain x u xs' where
	    head: "Some (x, u) \<in> set_dist (execute m s)"
	    and tail: "Some (xs', t) \<in> set_dist (execute (mmap ms) u)"
	    by (auto elim!: p.set_dist_bindE)
	  have m_in: "m \<in> set (m # ms)"
	    by simp
	  have q_head: "PQueryCounter u = PQueryCounter s"
	    by (rule Cons.prems(2)[OF m_in head])
	  have tail_step:
	    "\<And>m' x' u' v'. m' \<in> set ms \<Longrightarrow>
	      Some (x', v') \<in> set_dist (execute m' u') \<Longrightarrow>
	      PQueryCounter v' = PQueryCounter u'"
	  proof -
	    fix m' x' u' v'
	    assume m'_in_tail: "m' \<in> set ms"
	      and out: "Some (x', v') \<in> set_dist (execute m' u')"
	    have m'_in: "m' \<in> set (m # ms)"
	      using m'_in_tail by simp
	    show "PQueryCounter v' = PQueryCounter u'"
	      by (rule Cons.prems(2)[OF m'_in out])
	  qed
  have q_tail: "PQueryCounter t = PQueryCounter u"
    by (rule Cons.IH[OF tail tail_step])
  show ?case
    using q_head q_tail by simp
qed

lemma mfold_preserves_query_counter:
  fixes s t :: "('f, 'more) protocol_channel_scheme"
  assumes outcome: "Some (x, t) \<in> set_dist (execute (mfold a ms) s)"
    and step: "\<And>m a0 y u v. m \<in> set ms \<Longrightarrow>
      Some (y, v) \<in> set_dist (execute (m a0) u) \<Longrightarrow>
      PQueryCounter v = PQueryCounter u"
  shows "PQueryCounter t = PQueryCounter s"
  using outcome step
proof (induction ms arbitrary: a x s t)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
	  from Cons.prems(1) obtain y u where
	    head: "Some (y, u) \<in> set_dist (execute (m a) s)"
	    and tail: "Some (x, t) \<in> set_dist (execute (mfold y ms) u)"
	    by (auto elim!: p.set_dist_bindE)
	  have m_in: "m \<in> set (m # ms)"
	    by simp
	  have q_head: "PQueryCounter u = PQueryCounter s"
	    by (rule Cons.prems(2)[OF m_in head])
	  have tail_step:
	    "\<And>m' a0 y' u' v'. m' \<in> set ms \<Longrightarrow>
	      Some (y', v') \<in> set_dist (execute (m' a0) u') \<Longrightarrow>
	      PQueryCounter v' = PQueryCounter u'"
	  proof -
	    fix m' a0 y' u' v'
	    assume m'_in_tail: "m' \<in> set ms"
	      and out: "Some (y', v') \<in> set_dist (execute (m' a0) u')"
	    have m'_in: "m' \<in> set (m # ms)"
	      using m'_in_tail by simp
	    show "PQueryCounter v' = PQueryCounter u'"
	      by (rule Cons.prems(2)[OF m'_in out])
	  qed
  have q_tail: "PQueryCounter t = PQueryCounter u"
    by (rule Cons.IH[OF tail tail_step])
  show ?case
    using q_head q_tail by simp
qed

lemma mfold2_send_transcript_extends:
  assumes "Some ((), t) \<in> set_dist (execute (mfold2 p.send xs) s)"
  shows "transcript_extends t s"
  using p.mfold2_send_outcome[OF assms]
  unfolding transcript_extends_def by auto

lemma mfold2_send_hash_extends:
  assumes "Some ((), t) \<in> set_dist (execute (mfold2 p.send xs) s)"
  shows "s \<le> t"
  using p.mfold2_send_outcome[OF assms]
  unfolding less_eq_hash_ext_def less_eq_fmap_def by simp

lemma mfold2_send_preserves_query_counter:
  assumes "Some ((), t) \<in> set_dist (execute (mfold2 p.send xs) s)"
  shows "PQueryCounter t = PQueryCounter s"
  using p.mfold2_send_outcome[OF assms] by simp

lemma fri_commit_transcript_extends:
  assumes outcome:
    "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute (p.fri_commit n ps ds ls ms) s)"
  shows "transcript_extends t s"
  using outcome
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (p.send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute p.receive_random_field_element s1)"
    and next_layer_eq: "p.next_fri_layer (last ps) (last ds) b =
      (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (p.create next_layer) s2)"
    and rest: "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute
        (p.fri_commit n
          (ps @ [next_poly])
          (ds @ [next_domain])
          (ls @ [next_layer])
          (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: p.set_dist_bindE)
  have s_s1: "transcript_extends s1 s"
    using send_transcript_extends[OF send_root] .
  have s1_s2: "transcript_extends s2 s1"
    using receive_random_field_element_transcript_extends[OF rand] .
  have s2_s3: "transcript_extends s3 s2"
    using create_transcript_extends[OF create_m] .
  have s3_t: "transcript_extends t s3"
    using Suc.IH[OF rest] .
  show ?case
    using s_s1 s1_s2 s2_s3 s3_t by (meson transcript_extends_trans)
qed

lemma fri_commit_replay_data:
  assumes outcome:
    "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute (p.fri_commit n ps ds ls ms) s)"
  shows "\<exists>roots challenges.
    length roots = n \<and>
    length challenges = n \<and>
    PTranscript t = rev roots @ PTranscript s \<and>
    PState t = foldl concat (PState s) roots \<and>
    s \<le> t \<and>
    (\<forall>i < length roots.
      fmlookup (HashMap t) (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) roots))) =
        Some (challenges ! i))"
  using outcome
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case
    by (auto simp: p.hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (p.send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute p.receive_random_field_element s1)"
    and next_layer_eq: "p.next_fri_layer (last ps) (last ds) b =
      (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (p.create next_layer) s2)"
    and rest:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute
          (p.fri_commit n
            (ps @ [next_poly])
            (ds @ [next_domain])
            (ls @ [next_layer])
            (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: p.set_dist_bindE)
  let ?root = "value (last ms)"
  have send_res:
    "s1 = s\<lparr>PState := concat (PState s) ?root, PTranscript := ?root # PTranscript s\<rparr>"
    using p.send_outcome[OF send_root] .
  have rand_data:
    "s1 \<le> s2 \<and>
     PState s2 = PState s1 \<and>
     PTranscript s2 = PTranscript s1 \<and>
     fmlookup (HashMap s2) (FiatShamirChallenge (PState s1)) = Some b"
    using receive_random_field_element_outcome[OF rand] .
  have create_state: "PState s3 = PState s2"
    using create_preserves_state[OF create_m] .
  have create_tr: "PTranscript s3 = PTranscript s2"
    using create_preserves_transcript[OF create_m] .
  have s2_s3: "s2 \<le> s3"
    using create_hash_extends[OF create_m] .
  from Suc.IH[OF rest] obtain roots challenges where
    roots_len: "length roots = n"
    and challenges_len: "length challenges = n"
    and tr_t: "PTranscript t = rev roots @ PTranscript s3"
    and st_t: "PState t = foldl concat (PState s3) roots"
    and s3_t: "s3 \<le> t"
    and lookups_tail:
      "\<forall>i < length roots.
        fmlookup (HashMap t) (FiatShamirChallenge (foldl concat (PState s3) (take (Suc i) roots))) =
          Some (challenges ! i)"
    by blast
  have s_s1: "s \<le> s1"
    using send_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s_t: "s \<le> t"
    using s_s1 rand_data s2_s3 s3_t by (meson p.hash_ext_trans)
  have s2_t: "s2 \<le> t"
    using s2_s3 s3_t by (rule p.hash_ext_trans)
  have lookup_head:
    "fmlookup (HashMap t) (FiatShamirChallenge (concat (PState s) ?root)) = Some b"
  proof -
    have lookup_s2: "fmlookup (HashMap s2) (FiatShamirChallenge (PState s1)) = Some b"
      using rand_data by simp
    have "fmlookup (HashMap t) (FiatShamirChallenge (PState s1)) = Some b"
      using p.hash_extension_lookup[OF lookup_s2 s2_t] .
    then show ?thesis
      using send_res by simp
  qed
  have tr_final:
    "PTranscript t = rev (?root # roots) @ PTranscript s"
    using tr_t create_tr rand_data send_res by simp
  have st_final:
    "PState t = foldl concat (PState s) (?root # roots)"
    using st_t create_state rand_data send_res by simp
  have lookups:
    "\<forall>i < length (?root # roots).
      fmlookup (HashMap t) (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) (?root # roots)))) =
        Some ((b # challenges) ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length (?root # roots)"
    show "fmlookup (HashMap t) (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) (?root # roots)))) =
      Some ((b # challenges) ! i)"
    proof (cases i)
      case 0
      then show ?thesis
        using lookup_head by simp
    next
      case (Suc j)
      then have j_bound: "j < length roots"
        using i_bound by simp
      have key_eq:
        "foldl concat (PState s) (take (Suc (Suc j)) (?root # roots)) =
          foldl concat (PState s3) (take (Suc j) roots)"
        using send_res rand_data create_state by simp
      show ?thesis
        using lookups_tail j_bound key_eq Suc by simp
    qed
  qed
  show ?case
  proof (rule exI[where x="?root # roots"])
    show "\<exists>challenges.
      length (?root # roots) = Suc n \<and>
      length challenges = Suc n \<and>
      PTranscript t = rev (?root # roots) @ PTranscript s \<and>
      PState t = foldl concat (PState s) (?root # roots) \<and>
      s \<le> t \<and>
      (\<forall>i < length (?root # roots).
        fmlookup (HashMap t)
          (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) (?root # roots)))) =
          Some (challenges ! i))"
    proof (rule exI[where x="b # challenges"])
      show "length (?root # roots) = Suc n \<and>
        length (b # challenges) = Suc n \<and>
        PTranscript t = rev (?root # roots) @ PTranscript s \<and>
        PState t = foldl concat (PState s) (?root # roots) \<and>
        s \<le> t \<and>
        (\<forall>i < length (?root # roots).
          fmlookup (HashMap t)
            (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) (?root # roots)))) =
            Some ((b # challenges) ! i))"
        using roots_len challenges_len tr_final st_final s_t lookups by simp
    qed
  qed
qed

lemma fri_commit_replay_state:
  assumes outcome:
    "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute (p.fri_commit n ps ds ls ms) s)"
  shows "\<exists>roots.
    length roots = n \<and>
    PTranscript t = rev roots @ PTranscript s \<and>
    PState t = foldl concat (PState s) roots \<and>
    s \<le> t"
  using outcome
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case
    by (auto simp: p.hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (p.send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute p.receive_random_field_element s1)"
    and next_layer_eq: "p.next_fri_layer (last ps) (last ds) b =
      (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (p.create next_layer) s2)"
    and rest:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute
          (p.fri_commit n
            (ps @ [next_poly])
            (ds @ [next_domain])
            (ls @ [next_layer])
            (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: p.set_dist_bindE)
  let ?root = "value (last ms)"
  have send_res:
    "s1 = s\<lparr>PState := concat (PState s) ?root, PTranscript := ?root # PTranscript s\<rparr>"
    using p.send_outcome[OF send_root] .
  have rand_data:
    "s1 \<le> s2 \<and> PState s2 = PState s1 \<and> PTranscript s2 = PTranscript s1"
    using receive_random_field_element_outcome[OF rand] by simp
  have create_state: "PState s3 = PState s2"
    using create_preserves_state[OF create_m] .
  have create_tr: "PTranscript s3 = PTranscript s2"
    using create_preserves_transcript[OF create_m] .
  have s_s1: "s \<le> s1"
    using send_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s2_s3: "s2 \<le> s3"
    using create_hash_extends[OF create_m] .
  from Suc.IH[OF rest] obtain roots where
    roots_len: "length roots = n"
    and tr_t: "PTranscript t = rev roots @ PTranscript s3"
    and st_t: "PState t = foldl concat (PState s3) roots"
    and s3_t: "s3 \<le> t"
    by blast
  have tr_final: "PTranscript t = rev (?root # roots) @ PTranscript s"
    using tr_t create_tr rand_data send_res by simp
  have st_final: "PState t = foldl concat (PState s) (?root # roots)"
    using st_t create_state rand_data send_res by simp
  have s_t: "s \<le> t"
    using s_s1 rand_data s2_s3 s3_t by (meson p.hash_ext_trans)
  show ?case
    by (intro exI[where x="?root # roots"])
      (use roots_len tr_final st_final s_t in simp)
qed

lemma fri_commit_successor_layers:
  assumes outcome:
    "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute (p.fri_commit n ps ds ls ms) s)"
    and lens:
      "length ps = length ds"
      "length ds = length ls"
      "length ls = length ms"
    and nonempty: "ps \<noteq> []"
  shows "\<exists>challenges.
    length challenges = n \<and>
    (\<forall>j < n.
      p.next_fri_layer
        (ps' ! (length ps - 1 + j))
        (ds' ! (length ps - 1 + j))
        (challenges ! j) =
          (ps' ! (length ps + j),
           ds' ! (length ps + j),
           ls' ! (length ps + j)))"
  using outcome lens nonempty
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case by auto
next
  case (Suc n)
  from Suc.prems(1) obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root:
      "Some ((), s1) \<in> set_dist (execute (p.send (value (last ms))) s)"
    and rand:
      "Some (b, s2) \<in> set_dist (execute p.receive_random_field_element s1)"
    and next_layer_eq:
      "p.next_fri_layer (last ps) (last ds) b =
        (next_poly, next_domain, next_layer)"
    and create_m:
      "Some (m, s3) \<in> set_dist (execute (p.create next_layer) s2)"
    and rest:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute
          (p.fri_commit n
            (ps @ [next_poly])
            (ds @ [next_domain])
            (ls @ [next_layer])
            (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: p.set_dist_bindE)
  have lens_tail:
    "length (ps @ [next_poly]) = length (ds @ [next_domain])"
    "length (ds @ [next_domain]) = length (ls @ [next_layer])"
    "length (ls @ [next_layer]) = length (ms @ [m])"
    using Suc.prems(2-4) by simp_all
  have nonempty_tail: "ps @ [next_poly] \<noteq> []"
    by simp
  from Suc.IH[OF rest lens_tail nonempty_tail] obtain challenges where
    challenges_len: "length challenges = n"
    and tail_layers:
      "\<forall>j<n.
        p.next_fri_layer
          (ps' ! (length (ps @ [next_poly]) - 1 + j))
          (ds' ! (length (ps @ [next_poly]) - 1 + j))
          (challenges ! j) =
            (ps' ! (length (ps @ [next_poly]) + j),
             ds' ! (length (ps @ [next_poly]) + j),
             ls' ! (length (ps @ [next_poly]) + j))"
    by blast
  have prefix:
    "take (length (ps @ [next_poly])) ps' = ps @ [next_poly] \<and>
     take (length (ds @ [next_domain])) ds' = ds @ [next_domain] \<and>
     take (length (ls @ [next_layer])) ls' = ls @ [next_layer]"
    using p.fri_commit_preserves_prefix[OF rest] by simp
  have head_ps: "ps' ! (length ps - 1) = last ps"
  proof -
    obtain q where len_ps: "length ps = Suc q"
      using Suc.prems(5) by (cases ps) auto
    have idx_lt: "length ps - 1 < length (ps @ [next_poly])"
      using Suc.prems(5) by simp
    have ps'_nth: "ps' ! (length ps - 1) =
      (ps @ [next_poly]) ! (length ps - 1)"
    proof -
      have "(take (length (ps @ [next_poly])) ps') ! (length ps - 1) =
        (ps @ [next_poly]) ! (length ps - 1)"
        using conjunct1[OF prefix] by simp
      then show ?thesis
        using idx_lt by simp
    qed
    have append_nth:
      "(ps @ [next_poly]) ! (length ps - 1) = ps ! (length ps - 1)"
      using len_ps by (simp add: nth_append)
    have last_ps: "last ps = ps ! (length ps - 1)"
      using Suc.prems(5) by (simp add: last_conv_nth)
    show ?thesis
      using ps'_nth append_nth last_ps by simp
  qed
  have head_ds: "ds' ! (length ps - 1) = last ds"
  proof -
    have ds_ne: "ds \<noteq> []"
      using Suc.prems(2,5) by auto
    obtain q where len_ds: "length ds = Suc q"
      using ds_ne by (cases ds) auto
    have idx_lt: "length ps - 1 < length (ds @ [next_domain])"
      using Suc.prems(2,5) by simp
    have ds'_nth: "ds' ! (length ps - 1) =
      (ds @ [next_domain]) ! (length ps - 1)"
    proof -
      have "(take (length (ds @ [next_domain])) ds') ! (length ps - 1) =
        (ds @ [next_domain]) ! (length ps - 1)"
        using conjunct1[OF conjunct2[OF prefix]] by simp
      then show ?thesis
        using idx_lt by simp
    qed
    have append_nth:
      "(ds @ [next_domain]) ! (length ps - 1) = ds ! (length ds - 1)"
      using Suc.prems(2) len_ds by (simp add: nth_append)
    have last_ds: "last ds = ds ! (length ds - 1)"
      using ds_ne by (simp add: last_conv_nth)
    show ?thesis
      using ds'_nth append_nth last_ds by simp
  qed
  have head_next_ps: "ps' ! length ps = next_poly"
  proof -
    have pref: "take (Suc (length ps)) ps' = ps @ [next_poly]"
      using conjunct1[OF prefix] by simp
    have "ps' ! length ps = (take (Suc (length ps)) ps') ! length ps"
      by simp
    also have "... = next_poly"
      using pref by simp
    finally show ?thesis .
  qed
  have head_next_ds: "ds' ! length ps = next_domain"
  proof -
    have pref: "take (Suc (length ds)) ds' = ds @ [next_domain]"
      using conjunct1[OF conjunct2[OF prefix]] Suc.prems(2) by simp
    have "ds' ! length ps = (take (Suc (length ds)) ds') ! length ps"
      using Suc.prems(2) by simp
    also have "... = next_domain"
      using pref Suc.prems(2) by simp
    finally show ?thesis .
  qed
  have head_next_ls: "ls' ! length ps = next_layer"
  proof -
    have pref: "take (Suc (length ls)) ls' = ls @ [next_layer]"
      using conjunct2[OF conjunct2[OF prefix]] Suc.prems(2,3) by simp
    have "ls' ! length ps = (take (Suc (length ls)) ls') ! length ps"
      using Suc.prems(2,3) by simp
    also have "... = next_layer"
      using pref Suc.prems(2,3) by simp
    finally show ?thesis .
  qed
  have layers:
    "\<forall>j < Suc n.
      p.next_fri_layer
        (ps' ! (length ps - 1 + j))
        (ds' ! (length ps - 1 + j))
        ((b # challenges) ! j) =
          (ps' ! (length ps + j),
           ds' ! (length ps + j),
           ls' ! (length ps + j))"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show "p.next_fri_layer
        (ps' ! (length ps - 1 + j))
        (ds' ! (length ps - 1 + j))
        ((b # challenges) ! j) =
          (ps' ! (length ps + j),
           ds' ! (length ps + j),
           ls' ! (length ps + j))"
    proof (cases j)
      case 0
      then show ?thesis
        using next_layer_eq head_ps head_ds head_next_ps head_next_ds head_next_ls
        by simp
    next
      case (Suc k)
      then have k_bound: "k < n"
        using j_bound by simp
      have idx1:
        "length (ps @ [next_poly]) - 1 + k = length ps + k"
        by simp
      have idx2:
        "length (ps @ [next_poly]) + k = length ps + Suc k"
        by simp
      have idx_current:
        "length ps - 1 + Suc k = length ps + k"
      proof -
        obtain q where "length ps = Suc q"
          using Suc.prems(5) by (cases ps) auto
        then show ?thesis by simp
      qed
      have idx_left:
        "Suc (length ps - 1 + k) = length ps + k"
      proof -
        obtain q where "length ps = Suc q"
          using Suc.prems(5) by (cases ps) auto
        then show ?thesis by simp
      qed
      have tail_k:
        "p.next_fri_layer
          (ps' ! (length ps + k))
          (ds' ! (length ps + k))
          (challenges ! k) =
            (ps' ! Suc (length ps + k),
             ds' ! Suc (length ps + k),
             ls' ! Suc (length ps + k))"
        using tail_layers k_bound by simp
      show ?thesis
        unfolding Suc
        apply (subst idx_current)
        apply (subst idx_current)
        using tail_k
        apply simp
        done
    qed
  qed
  show ?case
    by (intro exI[where x="b # challenges"])
      (use challenges_len layers in simp)
qed

lemma fri_commit_replay_successor_data:
  assumes outcome:
    "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute (p.fri_commit n ps ds ls ms) s)"
    and lens:
      "length ps = length ds"
      "length ds = length ls"
      "length ls = length ms"
    and nonempty: "ps \<noteq> []"
  shows "\<exists>roots challenges.
    length roots = n \<and>
    length challenges = n \<and>
    PTranscript t = rev roots @ PTranscript s \<and>
    PState t = foldl concat (PState s) roots \<and>
    s \<le> t \<and>
    (\<forall>i < length roots.
      fmlookup (HashMap t) (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) roots))) =
        Some (challenges ! i)) \<and>
    (\<forall>j < n.
      roots ! j = value (ms' ! (length ms - 1 + j))) \<and>
    (\<forall>j < n.
      p.next_fri_layer
        (ps' ! (length ps - 1 + j))
        (ds' ! (length ps - 1 + j))
        (challenges ! j) =
          (ps' ! (length ps + j),
           ds' ! (length ps + j),
           ls' ! (length ps + j)))"
  using outcome lens nonempty
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case
    by (auto simp: p.hash_ext_refl)
next
  case (Suc n)
  from Suc.prems(1) obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root:
      "Some ((), s1) \<in> set_dist (execute (p.send (value (last ms))) s)"
    and rand:
      "Some (b, s2) \<in> set_dist (execute p.receive_random_field_element s1)"
    and next_layer_eq:
      "p.next_fri_layer (last ps) (last ds) b =
        (next_poly, next_domain, next_layer)"
    and create_m:
      "Some (m, s3) \<in> set_dist (execute (p.create next_layer) s2)"
    and rest:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute
          (p.fri_commit n
            (ps @ [next_poly])
            (ds @ [next_domain])
            (ls @ [next_layer])
            (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: p.set_dist_bindE)
  let ?root = "value (last ms)"
  have lens_tail:
    "length (ps @ [next_poly]) = length (ds @ [next_domain])"
    "length (ds @ [next_domain]) = length (ls @ [next_layer])"
    "length (ls @ [next_layer]) = length (ms @ [m])"
    using Suc.prems(2-4) by simp_all
  have nonempty_tail: "ps @ [next_poly] \<noteq> []"
    by simp
  from Suc.IH[OF rest lens_tail nonempty_tail] obtain roots challenges where
    roots_len: "length roots = n"
    and challenges_len: "length challenges = n"
    and tr_t: "PTranscript t = rev roots @ PTranscript s3"
    and st_t: "PState t = foldl concat (PState s3) roots"
    and s3_t: "s3 \<le> t"
    and lookups_tail:
      "\<forall>i < length roots.
        fmlookup (HashMap t) (FiatShamirChallenge (foldl concat (PState s3) (take (Suc i) roots))) =
          Some (challenges ! i)"
    and roots_tail:
      "\<forall>j<n.
        roots ! j =
          value (ms' ! (length (ms @ [m]) - 1 + j))"
    and tail_layers:
      "\<forall>j<n.
        p.next_fri_layer
          (ps' ! (length (ps @ [next_poly]) - 1 + j))
          (ds' ! (length (ps @ [next_poly]) - 1 + j))
          (challenges ! j) =
            (ps' ! (length (ps @ [next_poly]) + j),
             ds' ! (length (ps @ [next_poly]) + j),
             ls' ! (length (ps @ [next_poly]) + j))"
    by blast
  have send_res:
    "s1 = s\<lparr>PState := concat (PState s) ?root, PTranscript := ?root # PTranscript s\<rparr>"
    using p.send_outcome[OF send_root] .
  have rand_data:
    "s1 \<le> s2 \<and>
     PState s2 = PState s1 \<and>
     PTranscript s2 = PTranscript s1 \<and>
     fmlookup (HashMap s2) (FiatShamirChallenge (PState s1)) = Some b"
    using receive_random_field_element_outcome[OF rand] .
  have create_state: "PState s3 = PState s2"
    using create_preserves_state[OF create_m] .
  have create_tr: "PTranscript s3 = PTranscript s2"
    using create_preserves_transcript[OF create_m] .
  have s2_s3: "s2 \<le> s3"
    using create_hash_extends[OF create_m] .
  have s_s1: "s \<le> s1"
    using send_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s_t: "s \<le> t"
    using s_s1 rand_data s2_s3 s3_t by (meson p.hash_ext_trans)
  have s2_t: "s2 \<le> t"
    using s2_s3 s3_t by (rule p.hash_ext_trans)
  have lookup_head:
    "fmlookup (HashMap t) (FiatShamirChallenge (concat (PState s) ?root)) = Some b"
  proof -
    have lookup_s2: "fmlookup (HashMap s2) (FiatShamirChallenge (PState s1)) = Some b"
      using rand_data by simp
    have "fmlookup (HashMap t) (FiatShamirChallenge (PState s1)) = Some b"
      using p.hash_extension_lookup[OF lookup_s2 s2_t] .
    then show ?thesis
      using send_res by simp
  qed
  have tr_final:
    "PTranscript t = rev (?root # roots) @ PTranscript s"
    using tr_t create_tr rand_data send_res by simp
  have st_final:
    "PState t = foldl concat (PState s) (?root # roots)"
    using st_t create_state rand_data send_res by simp
  have lookups:
    "\<forall>i < length (?root # roots).
      fmlookup (HashMap t) (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) (?root # roots)))) =
        Some ((b # challenges) ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length (?root # roots)"
    show "fmlookup (HashMap t)
        (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) (?root # roots)))) =
      Some ((b # challenges) ! i)"
    proof (cases i)
      case 0
      then show ?thesis
        using lookup_head by simp
    next
      case (Suc j)
      then have j_bound: "j < length roots"
        using i_bound by simp
      have key_eq:
        "foldl concat (PState s) (take (Suc (Suc j)) (?root # roots)) =
          foldl concat (PState s3) (take (Suc j) roots)"
        using send_res rand_data create_state by simp
      show ?thesis
        using lookups_tail j_bound key_eq Suc by simp
    qed
  qed
  have prefix:
    "take (length (ps @ [next_poly])) ps' = ps @ [next_poly] \<and>
     take (length (ds @ [next_domain])) ds' = ds @ [next_domain] \<and>
     take (length (ls @ [next_layer])) ls' = ls @ [next_layer] \<and>
     take (length (ms @ [m])) ms' = ms @ [m]"
    using p.fri_commit_preserves_prefix[OF rest] by simp
  have head_ms: "ms' ! (length ms - 1) = last ms"
  proof -
    have ms_ne: "ms \<noteq> []"
      using Suc.prems(2-5) by auto
    obtain q where len_ms: "length ms = Suc q"
      using ms_ne by (cases ms) auto
    have idx_lt: "length ms - 1 < length (ms @ [m])"
      using ms_ne by simp
    have ms'_nth: "ms' ! (length ms - 1) =
      (ms @ [m]) ! (length ms - 1)"
    proof -
      have "(take (length (ms @ [m])) ms') ! (length ms - 1) =
        (ms @ [m]) ! (length ms - 1)"
        using conjunct2[OF conjunct2[OF conjunct2[OF prefix]]] by simp
      then show ?thesis
        using idx_lt by simp
    qed
    have append_nth:
      "(ms @ [m]) ! (length ms - 1) = ms ! (length ms - 1)"
      using len_ms by (simp add: nth_append)
    have last_ms: "last ms = ms ! (length ms - 1)"
      using ms_ne by (simp add: last_conv_nth)
    show ?thesis
      using ms'_nth append_nth last_ms by simp
  qed
  have head_ps: "ps' ! (length ps - 1) = last ps"
  proof -
    obtain q where len_ps: "length ps = Suc q"
      using Suc.prems(5) by (cases ps) auto
    have idx_lt: "length ps - 1 < length (ps @ [next_poly])"
      using Suc.prems(5) by simp
    have ps'_nth: "ps' ! (length ps - 1) =
      (ps @ [next_poly]) ! (length ps - 1)"
    proof -
      have "(take (length (ps @ [next_poly])) ps') ! (length ps - 1) =
        (ps @ [next_poly]) ! (length ps - 1)"
        using conjunct1[OF prefix] by simp
      then show ?thesis
        using idx_lt by simp
    qed
    have append_nth:
      "(ps @ [next_poly]) ! (length ps - 1) = ps ! (length ps - 1)"
      using len_ps by (simp add: nth_append)
    have last_ps: "last ps = ps ! (length ps - 1)"
      using Suc.prems(5) by (simp add: last_conv_nth)
    show ?thesis
      using ps'_nth append_nth last_ps by simp
  qed
  have head_ds: "ds' ! (length ps - 1) = last ds"
  proof -
    have ds_ne: "ds \<noteq> []"
      using Suc.prems(2,5) by auto
    obtain q where len_ds: "length ds = Suc q"
      using ds_ne by (cases ds) auto
    have idx_lt: "length ps - 1 < length (ds @ [next_domain])"
      using Suc.prems(2,5) by simp
    have ds'_nth: "ds' ! (length ps - 1) =
      (ds @ [next_domain]) ! (length ps - 1)"
    proof -
      have "(take (length (ds @ [next_domain])) ds') ! (length ps - 1) =
        (ds @ [next_domain]) ! (length ps - 1)"
        using conjunct1[OF conjunct2[OF prefix]] by simp
      then show ?thesis
        using idx_lt by simp
    qed
    have append_nth:
      "(ds @ [next_domain]) ! (length ps - 1) = ds ! (length ds - 1)"
      using Suc.prems(2) len_ds by (simp add: nth_append)
    have last_ds: "last ds = ds ! (length ds - 1)"
      using ds_ne by (simp add: last_conv_nth)
    show ?thesis
      using ds'_nth append_nth last_ds by simp
  qed
  have head_next_ps: "ps' ! length ps = next_poly"
  proof -
    have pref: "take (Suc (length ps)) ps' = ps @ [next_poly]"
      using conjunct1[OF prefix] by simp
    have "ps' ! length ps = (take (Suc (length ps)) ps') ! length ps"
      by simp
    also have "... = next_poly"
      using pref by simp
    finally show ?thesis .
  qed
  have head_next_ds: "ds' ! length ps = next_domain"
  proof -
    have pref: "take (Suc (length ds)) ds' = ds @ [next_domain]"
      using conjunct1[OF conjunct2[OF prefix]] Suc.prems(2) by simp
    have "ds' ! length ps = (take (Suc (length ds)) ds') ! length ps"
      using Suc.prems(2) by simp
    also have "... = next_domain"
      using pref Suc.prems(2) by simp
    finally show ?thesis .
  qed
  have head_next_ls: "ls' ! length ps = next_layer"
  proof -
    have pref: "take (Suc (length ls)) ls' = ls @ [next_layer]"
      using conjunct2[OF conjunct2[OF prefix]] Suc.prems(2,3) by simp
    have "ls' ! length ps = (take (Suc (length ls)) ls') ! length ps"
      using Suc.prems(2,3) by simp
    also have "... = next_layer"
      using pref Suc.prems(2,3) by simp
    finally show ?thesis .
  qed
  have layers:
    "\<forall>j < Suc n.
      p.next_fri_layer
        (ps' ! (length ps - 1 + j))
        (ds' ! (length ps - 1 + j))
        ((b # challenges) ! j) =
          (ps' ! (length ps + j),
           ds' ! (length ps + j),
           ls' ! (length ps + j))"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show "p.next_fri_layer
        (ps' ! (length ps - 1 + j))
        (ds' ! (length ps - 1 + j))
        ((b # challenges) ! j) =
          (ps' ! (length ps + j),
           ds' ! (length ps + j),
           ls' ! (length ps + j))"
    proof (cases j)
      case 0
      then show ?thesis
        using next_layer_eq head_ps head_ds head_next_ps head_next_ds head_next_ls
        by simp
    next
      case (Suc k)
      then have k_bound: "k < n"
        using j_bound by simp
      have idx_current:
        "length ps - 1 + Suc k = length ps + k"
      proof -
        obtain q where "length ps = Suc q"
          using Suc.prems(5) by (cases ps) auto
        then show ?thesis by simp
      qed
      have tail_k:
        "p.next_fri_layer
          (ps' ! (length ps + k))
          (ds' ! (length ps + k))
          (challenges ! k) =
            (ps' ! Suc (length ps + k),
             ds' ! Suc (length ps + k),
             ls' ! Suc (length ps + k))"
        using tail_layers k_bound by simp
      show ?thesis
        unfolding Suc
        apply (subst idx_current)
        apply (subst idx_current)
        using tail_k
        apply simp
        done
    qed
  qed
  have roots_aligned:
    "\<forall>j < Suc n.
      (?root # roots) ! j = value (ms' ! (length ms - 1 + j))"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show "(?root # roots) ! j = value (ms' ! (length ms - 1 + j))"
    proof (cases j)
      case 0
      then show ?thesis
        using head_ms by simp
    next
      case (Suc k)
      then have k_bound: "k < n"
        using j_bound by simp
      have idx_current:
        "length ms - 1 + Suc k = length ms + k"
      proof -
        obtain q where "length ms = Suc q"
          using Suc.prems(2-5) by (cases ms) auto
        then show ?thesis by simp
      qed
      have tail_k:
        "roots ! k = value (ms' ! (length ms + k))"
        using roots_tail k_bound by simp
      show ?thesis
        unfolding Suc
        apply (subst idx_current)
        using tail_k
        apply simp
        done
    qed
  qed
  show ?case
    by (intro exI[where x="?root # roots"] exI[where x="b # challenges"])
      (use roots_len challenges_len tr_final st_final s_t lookups roots_aligned layers in simp)
qed

lemma fri_commit_initial_replay_successor_data:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.fri_commit n [cp] [d] [l] [m]) s)"
  shows "\<exists>roots challenges.
    length roots = n \<and>
    length challenges = n \<and>
    PTranscript t = rev roots @ PTranscript s \<and>
    PState t = foldl concat (PState s) roots \<and>
    s \<le> t \<and>
    (\<forall>i < length roots.
      fmlookup (HashMap t) (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) roots))) =
        Some (challenges ! i)) \<and>
    (\<forall>j < n. roots ! j = value (ms ! j)) \<and>
    (\<forall>j < n.
      p.next_fri_layer
        (ps ! j)
        (ds ! j)
        (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j))"
proof -
  have data:
    "\<exists>roots challenges.
      length roots = n \<and>
      length challenges = n \<and>
      PTranscript t = rev roots @ PTranscript s \<and>
      PState t = foldl concat (PState s) roots \<and>
      s \<le> t \<and>
      (\<forall>i < length roots.
        fmlookup (HashMap t) (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) roots))) =
          Some (challenges ! i)) \<and>
      (\<forall>j < n. roots ! j = value (ms ! (length [m] - 1 + j))) \<and>
      (\<forall>j < n.
        p.next_fri_layer
          (ps ! (length [cp] - 1 + j))
          (ds ! (length [cp] - 1 + j))
          (challenges ! j) =
            (ps ! (length [cp] + j),
             ds ! (length [cp] + j),
             ls ! (length [cp] + j)))"
    by (rule fri_commit_replay_successor_data[OF outcome]) simp_all
  from data obtain roots challenges where
    len_roots: "length roots = n"
    and len_challenges: "length challenges = n"
    and tr: "PTranscript t = rev roots @ PTranscript s"
    and st: "PState t = foldl concat (PState s) roots"
    and ext: "s \<le> t"
    and lookups:
      "\<forall>i < length roots.
        fmlookup (HashMap t) (FiatShamirChallenge (foldl concat (PState s) (take (Suc i) roots))) =
          Some (challenges ! i)"
    and roots_aligned:
      "\<forall>j<n. roots ! j = value (ms ! (length [m] - 1 + j))"
    and layers:
      "\<forall>j<n.
        p.next_fri_layer
          (ps ! (length [cp] - 1 + j))
          (ds ! (length [cp] - 1 + j))
          (challenges ! j) =
            (ps ! (length [cp] + j),
             ds ! (length [cp] + j),
             ls ! (length [cp] + j))"
    by blast
  have roots_simple:
    "\<forall>j < n. roots ! j = value (ms ! j)"
    using roots_aligned by simp
  have layers_simple:
    "\<forall>j < n.
      p.next_fri_layer (ps ! j) (ds ! j) (challenges ! j) =
        (ps ! Suc j, ds ! Suc j, ls ! Suc j)"
    using layers by simp
  show ?thesis
    by (intro exI[where x=roots] exI[where x=challenges])
      (use len_roots len_challenges tr st ext lookups roots_simple layers_simple in simp)
qed

lemma fri_commit_with_replay_successor_data:
  assumes send_counter:
      "\<And>x s t. Some ((), t) \<in> set_dist (execute (p.send x) s) \<Longrightarrow>
        counter t = counter s"
    and receiver_data:
      "\<And>b s t. Some (b, t) \<in> set_dist (execute receive_challenge s) \<Longrightarrow>
        s \<le> t \<and>
        PState t = PState s \<and>
        PTranscript t = PTranscript s \<and>
        counter t = Suc (counter s) \<and>
        fmlookup (HashMap t) (tag (counter s) (PState s)) = Some b"
    and create_counter:
      "\<And>xs m s t. Some (m, t) \<in> set_dist (execute (p.create xs) s) \<Longrightarrow>
        counter t = counter s"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute (p.fri_commit_with receive_challenge n ps ds ls ms) s)"
    and lens:
      "length ps = length ds"
      "length ds = length ls"
      "length ls = length ms"
    and nonempty: "ps \<noteq> []"
  shows "\<exists>roots challenges.
    length roots = n \<and>
    length challenges = n \<and>
    PTranscript t = rev roots @ PTranscript s \<and>
    PState t = foldl concat (PState s) roots \<and>
    s \<le> t \<and>
    counter t = counter s + n \<and>
    (\<forall>i < length roots.
      fmlookup (HashMap t)
        (tag (counter s + i)
          (foldl concat (PState s) (take (Suc i) roots))) =
        Some (challenges ! i)) \<and>
    (\<forall>j < n.
      roots ! j = value (ms' ! (length ms - 1 + j))) \<and>
    (\<forall>j < n.
      p.next_fri_layer
        (ps' ! (length ps - 1 + j))
        (ds' ! (length ps - 1 + j))
        (challenges ! j) =
          (ps' ! (length ps + j),
           ds' ! (length ps + j),
           ls' ! (length ps + j)))"
  using outcome lens nonempty
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case
    by (auto simp: p.hash_ext_refl)
next
  case (Suc n)
  from Suc.prems(1) obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root:
      "Some ((), s1) \<in> set_dist (execute (p.send (value (last ms))) s)"
    and rand:
      "Some (b, s2) \<in> set_dist (execute receive_challenge s1)"
    and next_layer_eq:
      "p.next_fri_layer (last ps) (last ds) b =
        (next_poly, next_domain, next_layer)"
    and create_m:
      "Some (m, s3) \<in> set_dist (execute (p.create next_layer) s2)"
    and rest:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute
          (p.fri_commit_with receive_challenge n
            (ps @ [next_poly])
            (ds @ [next_domain])
            (ls @ [next_layer])
            (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: p.set_dist_bindE)
  let ?root = "value (last ms)"
  have lens_tail:
    "length (ps @ [next_poly]) = length (ds @ [next_domain])"
    "length (ds @ [next_domain]) = length (ls @ [next_layer])"
    "length (ls @ [next_layer]) = length (ms @ [m])"
    using Suc.prems(2-4) by simp_all
  have nonempty_tail: "ps @ [next_poly] \<noteq> []"
    by simp
  from Suc.IH[OF rest lens_tail nonempty_tail] obtain roots challenges where
    roots_len: "length roots = n"
    and challenges_len: "length challenges = n"
    and tr_t: "PTranscript t = rev roots @ PTranscript s3"
    and st_t: "PState t = foldl concat (PState s3) roots"
    and s3_t: "s3 \<le> t"
    and counter_t: "counter t = counter s3 + n"
    and lookups_tail:
      "\<forall>i < length roots.
        fmlookup (HashMap t)
          (tag (counter s3 + i)
            (foldl concat (PState s3) (take (Suc i) roots))) =
          Some (challenges ! i)"
    and roots_tail:
      "\<forall>j<n.
        roots ! j =
          value (ms' ! (length (ms @ [m]) - 1 + j))"
    and tail_layers:
      "\<forall>j<n.
        p.next_fri_layer
          (ps' ! (length (ps @ [next_poly]) - 1 + j))
          (ds' ! (length (ps @ [next_poly]) - 1 + j))
          (challenges ! j) =
            (ps' ! (length (ps @ [next_poly]) + j),
             ds' ! (length (ps @ [next_poly]) + j),
             ls' ! (length (ps @ [next_poly]) + j))"
    by blast
  have send_res:
    "s1 = s\<lparr>PState := concat (PState s) ?root,
      PTranscript := ?root # PTranscript s\<rparr>"
    using p.send_outcome[OF send_root] .
  have rand_data:
    "s1 \<le> s2 \<and>
     PState s2 = PState s1 \<and>
     PTranscript s2 = PTranscript s1 \<and>
     counter s2 = Suc (counter s1) \<and>
     fmlookup (HashMap s2) (tag (counter s1) (PState s1)) = Some b"
    using receiver_data[OF rand] .
  have create_state: "PState s3 = PState s2"
    using create_preserves_state[OF create_m] .
  have create_tr: "PTranscript s3 = PTranscript s2"
    using create_preserves_transcript[OF create_m] .
  have counter_s1: "counter s1 = counter s"
    using send_counter[OF send_root] .
  have counter_s2: "counter s2 = Suc (counter s1)"
    using rand_data by simp
  have counter_s3: "counter s3 = counter s2"
    using create_counter[OF create_m] .
  have counter_s3_s: "counter s3 = Suc (counter s)"
    using counter_s1 counter_s2 counter_s3 by simp
  have counter_final: "counter t = counter s + Suc n"
    using counter_t counter_s3_s by simp
  have s2_s3: "s2 \<le> s3"
    using create_hash_extends[OF create_m] .
  have s_s1: "s \<le> s1"
    using send_res unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s_t: "s \<le> t"
    using s_s1 rand_data s2_s3 s3_t by (meson p.hash_ext_trans)
  have s2_t: "s2 \<le> t"
    using s2_s3 s3_t by (rule p.hash_ext_trans)
  have lookup_head:
    "fmlookup (HashMap t)
      (tag (counter s) (concat (PState s) ?root)) = Some b"
  proof -
    have lookup_s2:
      "fmlookup (HashMap s2) (tag (counter s1) (PState s1)) = Some b"
      using rand_data by simp
    have "fmlookup (HashMap t) (tag (counter s1) (PState s1)) = Some b"
      using p.hash_extension_lookup[OF lookup_s2 s2_t] .
    then show ?thesis
      using send_res counter_s1 by simp
  qed
  have tr_final:
    "PTranscript t = rev (?root # roots) @ PTranscript s"
    using tr_t create_tr rand_data send_res by simp
  have st_final:
    "PState t = foldl concat (PState s) (?root # roots)"
    using st_t create_state rand_data send_res by simp
  have lookups:
    "\<forall>i < length (?root # roots).
      fmlookup (HashMap t)
        (tag (counter s + i)
          (foldl concat (PState s) (take (Suc i) (?root # roots)))) =
        Some ((b # challenges) ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length (?root # roots)"
    show "fmlookup (HashMap t)
        (tag (counter s + i)
          (foldl concat (PState s) (take (Suc i) (?root # roots)))) =
      Some ((b # challenges) ! i)"
    proof (cases i)
      case 0
      then show ?thesis
        using lookup_head by simp
    next
      case (Suc j)
      then have j_bound: "j < length roots"
        using i_bound by simp
      have key_eq:
        "foldl concat (PState s) (take (Suc (Suc j)) (?root # roots)) =
          foldl concat (PState s3) (take (Suc j) roots)"
        using send_res rand_data create_state by simp
      show ?thesis
        using lookups_tail j_bound key_eq Suc counter_s3_s by simp
    qed
  qed
  have prefix:
    "take (length (ps @ [next_poly])) ps' = ps @ [next_poly] \<and>
     take (length (ds @ [next_domain])) ds' = ds @ [next_domain] \<and>
     take (length (ls @ [next_layer])) ls' = ls @ [next_layer] \<and>
     take (length (ms @ [m])) ms' = ms @ [m]"
    using p.fri_commit_with_preserves_prefix[OF rest] by simp
  have head_ms: "ms' ! (length ms - 1) = last ms"
  proof -
    have ms_ne: "ms \<noteq> []"
      using Suc.prems(2-5) by auto
    obtain q where len_ms: "length ms = Suc q"
      using ms_ne by (cases ms) auto
    have idx_lt: "length ms - 1 < length (ms @ [m])"
      using ms_ne by simp
    have ms'_nth: "ms' ! (length ms - 1) =
      (ms @ [m]) ! (length ms - 1)"
    proof -
      have "(take (length (ms @ [m])) ms') ! (length ms - 1) =
        (ms @ [m]) ! (length ms - 1)"
        using conjunct2[OF conjunct2[OF conjunct2[OF prefix]]] by simp
      then show ?thesis
        using idx_lt by simp
    qed
    have append_nth:
      "(ms @ [m]) ! (length ms - 1) = ms ! (length ms - 1)"
      using len_ms by (simp add: nth_append)
    have last_ms: "last ms = ms ! (length ms - 1)"
      using ms_ne by (simp add: last_conv_nth)
    show ?thesis
      using ms'_nth append_nth last_ms by simp
  qed
  have head_ps: "ps' ! (length ps - 1) = last ps"
  proof -
    obtain q where len_ps: "length ps = Suc q"
      using Suc.prems(5) by (cases ps) auto
    have idx_lt: "length ps - 1 < length (ps @ [next_poly])"
      using Suc.prems(5) by simp
    have ps'_nth: "ps' ! (length ps - 1) =
      (ps @ [next_poly]) ! (length ps - 1)"
    proof -
      have "(take (length (ps @ [next_poly])) ps') ! (length ps - 1) =
        (ps @ [next_poly]) ! (length ps - 1)"
        using conjunct1[OF prefix] by simp
      then show ?thesis
        using idx_lt by simp
    qed
    have append_nth:
      "(ps @ [next_poly]) ! (length ps - 1) = ps ! (length ps - 1)"
      using len_ps by (simp add: nth_append)
    have last_ps: "last ps = ps ! (length ps - 1)"
      using Suc.prems(5) by (simp add: last_conv_nth)
    show ?thesis
      using ps'_nth append_nth last_ps by simp
  qed
  have head_ds: "ds' ! (length ps - 1) = last ds"
  proof -
    have ds_ne: "ds \<noteq> []"
      using Suc.prems(2,5) by auto
    obtain q where len_ds: "length ds = Suc q"
      using ds_ne by (cases ds) auto
    have idx_lt: "length ps - 1 < length (ds @ [next_domain])"
      using Suc.prems(2,5) by simp
    have ds'_nth: "ds' ! (length ps - 1) =
      (ds @ [next_domain]) ! (length ps - 1)"
    proof -
      have "(take (length (ds @ [next_domain])) ds') ! (length ps - 1) =
        (ds @ [next_domain]) ! (length ps - 1)"
        using conjunct1[OF conjunct2[OF prefix]] by simp
      then show ?thesis
        using idx_lt by simp
    qed
    have append_nth:
      "(ds @ [next_domain]) ! (length ps - 1) = ds ! (length ds - 1)"
      using Suc.prems(2) len_ds by (simp add: nth_append)
    have last_ds: "last ds = ds ! (length ds - 1)"
      using ds_ne by (simp add: last_conv_nth)
    show ?thesis
      using ds'_nth append_nth last_ds by simp
  qed
  have head_next_ps: "ps' ! length ps = next_poly"
  proof -
    have pref: "take (Suc (length ps)) ps' = ps @ [next_poly]"
      using conjunct1[OF prefix] by simp
    have "ps' ! length ps = (take (Suc (length ps)) ps') ! length ps"
      by simp
    also have "... = next_poly"
      using pref by simp
    finally show ?thesis .
  qed
  have head_next_ds: "ds' ! length ps = next_domain"
  proof -
    have pref: "take (Suc (length ds)) ds' = ds @ [next_domain]"
      using conjunct1[OF conjunct2[OF prefix]] Suc.prems(2) by simp
    have "ds' ! length ps = (take (Suc (length ds)) ds') ! length ps"
      using Suc.prems(2) by simp
    also have "... = next_domain"
      using pref Suc.prems(2) by simp
    finally show ?thesis .
  qed
  have head_next_ls: "ls' ! length ps = next_layer"
  proof -
    have pref: "take (Suc (length ls)) ls' = ls @ [next_layer]"
      using conjunct2[OF conjunct2[OF prefix]] Suc.prems(2,3) by simp
    have "ls' ! length ps = (take (Suc (length ls)) ls') ! length ps"
      using Suc.prems(2,3) by simp
    also have "... = next_layer"
      using pref Suc.prems(2,3) by simp
    finally show ?thesis .
  qed
  have layers:
    "\<forall>j < Suc n.
      p.next_fri_layer
        (ps' ! (length ps - 1 + j))
        (ds' ! (length ps - 1 + j))
        ((b # challenges) ! j) =
          (ps' ! (length ps + j),
           ds' ! (length ps + j),
           ls' ! (length ps + j))"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show "p.next_fri_layer
        (ps' ! (length ps - 1 + j))
        (ds' ! (length ps - 1 + j))
        ((b # challenges) ! j) =
          (ps' ! (length ps + j),
           ds' ! (length ps + j),
           ls' ! (length ps + j))"
    proof (cases j)
      case 0
      then show ?thesis
        using next_layer_eq head_ps head_ds head_next_ps head_next_ds head_next_ls
        by simp
    next
      case (Suc k)
      then have k_bound: "k < n"
        using j_bound by simp
      have idx_current:
        "length ps - 1 + Suc k = length ps + k"
      proof -
        obtain q where "length ps = Suc q"
          using Suc.prems(5) by (cases ps) auto
        then show ?thesis by simp
      qed
      have tail_k:
        "p.next_fri_layer
          (ps' ! (length ps + k))
          (ds' ! (length ps + k))
          (challenges ! k) =
            (ps' ! Suc (length ps + k),
             ds' ! Suc (length ps + k),
             ls' ! Suc (length ps + k))"
        using tail_layers k_bound by simp
      show ?thesis
        unfolding Suc
        apply (subst idx_current)
        apply (subst idx_current)
        using tail_k
        apply simp
        done
    qed
  qed
  have roots_aligned:
    "\<forall>j < Suc n.
      (?root # roots) ! j = value (ms' ! (length ms - 1 + j))"
  proof (intro allI impI)
    fix j
    assume j_bound: "j < Suc n"
    show "(?root # roots) ! j = value (ms' ! (length ms - 1 + j))"
    proof (cases j)
      case 0
      then show ?thesis
        using head_ms by simp
    next
      case (Suc k)
      then have k_bound: "k < n"
        using j_bound by simp
      have idx_current:
        "length ms - 1 + Suc k = length ms + k"
      proof -
        obtain q where "length ms = Suc q"
          using Suc.prems(2-5) by (cases ms) auto
        then show ?thesis by simp
      qed
      have tail_k:
        "roots ! k = value (ms' ! (length ms + k))"
        using roots_tail k_bound by simp
      show ?thesis
        unfolding Suc
        apply (subst idx_current)
        using tail_k
        apply simp
        done
    qed
  qed
  show ?case
  proof (rule exI[where x="?root # roots"])
    show "\<exists>challenges.
      length (?root # roots) = Suc n \<and>
      length challenges = Suc n \<and>
      PTranscript t = rev (?root # roots) @ PTranscript s \<and>
      PState t = foldl concat (PState s) (?root # roots) \<and>
      s \<le> t \<and>
      counter t = counter s + Suc n \<and>
      (\<forall>i<length (?root # roots).
        fmlookup (HashMap t)
          (tag (counter s + i)
            (foldl concat (PState s) (take (Suc i) (?root # roots)))) =
        Some (challenges ! i)) \<and>
      (\<forall>j<Suc n.
        (?root # roots) ! j = value (ms' ! (length ms - 1 + j))) \<and>
      (\<forall>j<Suc n.
        p.next_fri_layer
          (ps' ! (length ps - 1 + j))
          (ds' ! (length ps - 1 + j))
          (challenges ! j) =
            (ps' ! (length ps + j),
             ds' ! (length ps + j),
             ls' ! (length ps + j)))"
    proof (rule exI[where x="b # challenges"])
      show "length (?root # roots) = Suc n \<and>
        length (b # challenges) = Suc n \<and>
        PTranscript t = rev (?root # roots) @ PTranscript s \<and>
        PState t = foldl concat (PState s) (?root # roots) \<and>
        s \<le> t \<and>
        counter t = counter s + Suc n \<and>
        (\<forall>i<length (?root # roots).
          fmlookup (HashMap t)
            (tag (counter s + i)
              (foldl concat (PState s) (take (Suc i) (?root # roots)))) =
          Some ((b # challenges) ! i)) \<and>
        (\<forall>j<Suc n.
          (?root # roots) ! j = value (ms' ! (length ms - 1 + j))) \<and>
        (\<forall>j<Suc n.
          p.next_fri_layer
            (ps' ! (length ps - 1 + j))
            (ds' ! (length ps - 1 + j))
            ((b # challenges) ! j) =
              (ps' ! (length ps + j),
               ds' ! (length ps + j),
               ls' ! (length ps + j)))"
        using roots_len challenges_len tr_final st_final s_t counter_final
          lookups roots_aligned layers
        by simp
    qed
  qed
qed

lemma fri_commit_with_preserves_counter:
  fixes counter :: "'f protocol_channel \<Rightarrow> nat"
  assumes send_counter:
      "\<And>x s t. Some ((), t) \<in> set_dist (execute (p.send x) s) \<Longrightarrow>
        counter t = counter s"
    and receiver_counter:
      "\<And>b s t. Some (b, t) \<in> set_dist (execute receive_challenge s) \<Longrightarrow>
        counter t = counter s"
    and create_counter:
      "\<And>xs m s t. Some (m, t) \<in> set_dist (execute (p.create xs) s) \<Longrightarrow>
        counter t = counter s"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute
          (p.fri_commit_with receive_challenge n ps ds ls ms) s)"
  shows "counter t = counter s"
  using outcome
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (p.send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute receive_challenge s1)"
    and next_layer_eq:
      "p.next_fri_layer (last ps) (last ds) b =
        (next_poly, next_domain, next_layer)"
    and create_m:
      "Some (m, s3) \<in> set_dist (execute (p.create next_layer) s2)"
    and rest:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute
          (p.fri_commit_with receive_challenge n
            (ps @ [next_poly])
            (ds @ [next_domain])
            (ls @ [next_layer])
            (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: p.set_dist_bindE)
  have c_s1: "counter s1 = counter s"
    by (rule send_counter[OF send_root])
  have c_s2: "counter s2 = counter s1"
    by (rule receiver_counter[OF rand])
  have c_s3: "counter s3 = counter s2"
    by (rule create_counter[OF create_m])
  have c_t: "counter t = counter s3"
    by (rule Suc.IH[OF rest])
  show ?case
    using c_s1 c_s2 c_s3 c_t by simp
qed

lemma trace_fri_commit_preserves_alpha_counter:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.trace_fri_commit n ps0 ds0 ls0 ms0) s)"
  shows "PAlphaCounter t = PAlphaCounter s"
proof -
  have send_counter:
    "\<And>x s t. Some ((), t) \<in> set_dist (execute (p.send x) s) \<Longrightarrow>
      PAlphaCounter t = PAlphaCounter s"
    using p.send_outcome by fastforce
  have receiver_counter:
    "\<And>b s t. Some (b, t) \<in> set_dist (execute p.receive_trace_fri_challenge s) \<Longrightarrow>
      PAlphaCounter t = PAlphaCounter s"
    using p.receive_trace_fri_challenge_counter_outcome by fastforce
  have create_counter:
    "\<And>xs m s t. Some (m, t) \<in> set_dist (execute (p.create xs) s) \<Longrightarrow>
      PAlphaCounter t = PAlphaCounter s"
    by (rule p.create_preserves_channel(5))
  show ?thesis
    unfolding p.trace_fri_commit_def
    by (rule fri_commit_with_preserves_counter[
        where counter=PAlphaCounter and receive_challenge=p.receive_trace_fri_challenge,
        OF send_counter receiver_counter create_counter
          outcome[unfolded p.trace_fri_commit_def]])
qed

lemma trace_fri_commit_preserves_composition_counter:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.trace_fri_commit n ps0 ds0 ls0 ms0) s)"
  shows "PCompositionFriCounter t = PCompositionFriCounter s"
proof -
  have send_counter:
    "\<And>x s t. Some ((), t) \<in> set_dist (execute (p.send x) s) \<Longrightarrow>
      PCompositionFriCounter t = PCompositionFriCounter s"
    using p.send_outcome by fastforce
  have receiver_counter:
    "\<And>b s t. Some (b, t) \<in> set_dist (execute p.receive_trace_fri_challenge s) \<Longrightarrow>
      PCompositionFriCounter t = PCompositionFriCounter s"
    using p.receive_trace_fri_challenge_counter_outcome by fastforce
  have create_counter:
    "\<And>xs m s t. Some (m, t) \<in> set_dist (execute (p.create xs) s) \<Longrightarrow>
      PCompositionFriCounter t = PCompositionFriCounter s"
    by (rule p.create_preserves_channel(4))
  show ?thesis
    unfolding p.trace_fri_commit_def
	    by (rule fri_commit_with_preserves_counter[
	        where counter=PCompositionFriCounter and receive_challenge=p.receive_trace_fri_challenge,
	        OF send_counter receiver_counter create_counter
	          outcome[unfolded p.trace_fri_commit_def]])
	qed

lemma fri_commit_preserves_query_counter:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.fri_commit n ps0 ds0 ls0 ms0) s)"
  shows "PQueryCounter t = PQueryCounter s"
proof -
  have send_counter:
    "\<And>x s t. Some ((), t) \<in> set_dist (execute (p.send x) s) \<Longrightarrow>
      PQueryCounter t = PQueryCounter s"
    using p.send_outcome by fastforce
  have receiver_counter:
    "\<And>b s t. Some (b, t) \<in> set_dist (execute p.receive_random_field_element s) \<Longrightarrow>
      PQueryCounter t = PQueryCounter s"
    using p.receive_random_field_element_counter_outcome by fastforce
	  have create_counter:
	    "\<And>xs m s t. Some (m, t) \<in> set_dist (execute (p.create xs) s) \<Longrightarrow>
	      PQueryCounter t = PQueryCounter s"
	    by (rule p.create_preserves_channel(6))
	  have outcome':
	    "Some ((ps, ds, ls, ms), t) \<in>
	      set_dist (execute
	        (p.fri_commit_with p.receive_random_field_element n ps0 ds0 ls0 ms0) s)"
	    using outcome p.fri_commit_with_receive_random_field_element by simp
	  show ?thesis
	    by (rule fri_commit_with_preserves_counter[
	        where counter=PQueryCounter and receive_challenge=p.receive_random_field_element,
	        OF send_counter receiver_counter create_counter outcome'])
	qed

lemma trace_fri_commit_preserves_query_counter:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.trace_fri_commit n ps0 ds0 ls0 ms0) s)"
  shows "PQueryCounter t = PQueryCounter s"
proof -
  have send_counter:
    "\<And>x s t. Some ((), t) \<in> set_dist (execute (p.send x) s) \<Longrightarrow>
      PQueryCounter t = PQueryCounter s"
    using p.send_outcome by fastforce
  have receiver_counter:
    "\<And>b s t. Some (b, t) \<in> set_dist (execute p.receive_trace_fri_challenge s) \<Longrightarrow>
      PQueryCounter t = PQueryCounter s"
    using p.receive_trace_fri_challenge_counter_outcome by fastforce
  have create_counter:
    "\<And>xs m s t. Some (m, t) \<in> set_dist (execute (p.create xs) s) \<Longrightarrow>
      PQueryCounter t = PQueryCounter s"
    by (rule p.create_preserves_channel(6))
  show ?thesis
    unfolding p.trace_fri_commit_def
    by (rule fri_commit_with_preserves_counter[
        where counter=PQueryCounter and receive_challenge=p.receive_trace_fri_challenge,
        OF send_counter receiver_counter create_counter
          outcome[unfolded p.trace_fri_commit_def]])
qed

lemma composition_fri_commit_preserves_query_counter:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.composition_fri_commit n ps0 ds0 ls0 ms0) s)"
  shows "PQueryCounter t = PQueryCounter s"
proof -
  have send_counter:
    "\<And>x s t. Some ((), t) \<in> set_dist (execute (p.send x) s) \<Longrightarrow>
      PQueryCounter t = PQueryCounter s"
    using p.send_outcome by fastforce
  have receiver_counter:
    "\<And>b s t. Some (b, t) \<in> set_dist (execute p.receive_composition_fri_challenge s) \<Longrightarrow>
      PQueryCounter t = PQueryCounter s"
    using p.receive_composition_fri_challenge_counter_outcome by fastforce
  have create_counter:
    "\<And>xs m s t. Some (m, t) \<in> set_dist (execute (p.create xs) s) \<Longrightarrow>
      PQueryCounter t = PQueryCounter s"
    by (rule p.create_preserves_channel(6))
  show ?thesis
    unfolding p.composition_fri_commit_def
    by (rule fri_commit_with_preserves_counter[
        where counter=PQueryCounter and receive_challenge=p.receive_composition_fri_challenge,
        OF send_counter receiver_counter create_counter
          outcome[unfolded p.composition_fri_commit_def]])
qed

lemma trace_fri_commit_initial_replay_successor_data:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.trace_fri_commit n [cp] [d] [l] [m]) s)"
  shows "\<exists>roots challenges.
    length roots = n \<and>
    length challenges = n \<and>
    PTranscript t = rev roots @ PTranscript s \<and>
    PState t = foldl concat (PState s) roots \<and>
    s \<le> t \<and>
    (\<forall>i < length roots.
      fmlookup (HashMap t)
        (TraceFriChallenge (PTraceFriCounter s + i)
          (foldl concat (PState s) (take (Suc i) roots))) =
        Some (challenges ! i)) \<and>
    (\<forall>j < n. roots ! j = value (ms ! j)) \<and>
    (\<forall>j < n.
      p.next_fri_layer
        (ps ! j)
        (ds ! j)
        (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j))"
proof -
  have send_counter:
    "\<And>x s t. Some ((), t) \<in> set_dist (execute (p.send x) s) \<Longrightarrow>
      PTraceFriCounter t = PTraceFriCounter s"
  proof -
    fix x s t
    assume send: "Some ((), t) \<in> set_dist (execute (p.send x) s)"
    show "PTraceFriCounter t = PTraceFriCounter s"
      using p.send_outcome[OF send] by simp
  qed
  have receiver:
    "\<And>b s t. Some (b, t) \<in>
        set_dist (execute p.receive_trace_fri_challenge s) \<Longrightarrow>
      s \<le> t \<and>
      PState t = PState s \<and>
      PTranscript t = PTranscript s \<and>
      PTraceFriCounter t = Suc (PTraceFriCounter s) \<and>
      fmlookup (HashMap t)
        (TraceFriChallenge (PTraceFriCounter s) (PState s)) = Some b"
  proof -
    fix b s t
    assume rand:
      "Some (b, t) \<in> set_dist (execute p.receive_trace_fri_challenge s)"
    show "s \<le> t \<and>
      PState t = PState s \<and>
      PTranscript t = PTranscript s \<and>
      PTraceFriCounter t = Suc (PTraceFriCounter s) \<and>
      fmlookup (HashMap t)
        (TraceFriChallenge (PTraceFriCounter s) (PState s)) = Some b"
      using p.receive_trace_fri_challenge_outcome[OF rand]
        p.receive_trace_fri_challenge_counter_outcome[OF rand]
      by simp
  qed
  have create_counter:
    "\<And>xs m s t. Some (m, t) \<in> set_dist (execute (p.create xs) s) \<Longrightarrow>
      PTraceFriCounter t = PTraceFriCounter s"
    by (rule p.create_preserves_channel(3))
  have data:
    "\<exists>roots challenges.
      length roots = n \<and>
      length challenges = n \<and>
      PTranscript t = rev roots @ PTranscript s \<and>
      PState t = foldl concat (PState s) roots \<and>
      s \<le> t \<and>
      PTraceFriCounter t = PTraceFriCounter s + n \<and>
      (\<forall>i < length roots.
        fmlookup (HashMap t)
          (TraceFriChallenge (PTraceFriCounter s + i)
            (foldl concat (PState s) (take (Suc i) roots))) =
          Some (challenges ! i)) \<and>
      (\<forall>j < n. roots ! j = value (ms ! (length [m] - 1 + j))) \<and>
      (\<forall>j < n.
        p.next_fri_layer
          (ps ! (length [cp] - 1 + j))
          (ds ! (length [cp] - 1 + j))
          (challenges ! j) =
            (ps ! (length [cp] + j),
             ds ! (length [cp] + j),
             ls ! (length [cp] + j)))"
    unfolding p.trace_fri_commit_def
    by (rule fri_commit_with_replay_successor_data
        [where counter=PTraceFriCounter and tag=TraceFriChallenge,
          OF send_counter receiver create_counter
          outcome[unfolded p.trace_fri_commit_def]]) simp_all
  then show ?thesis by auto
qed

lemma composition_fri_commit_initial_replay_successor_data:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.composition_fri_commit n [cp] [d] [l] [m]) s)"
  shows "\<exists>roots challenges.
    length roots = n \<and>
    length challenges = n \<and>
    PTranscript t = rev roots @ PTranscript s \<and>
    PState t = foldl concat (PState s) roots \<and>
    s \<le> t \<and>
    (\<forall>i < length roots.
      fmlookup (HashMap t)
        (CompositionFriChallenge (PCompositionFriCounter s + i)
          (foldl concat (PState s) (take (Suc i) roots))) =
        Some (challenges ! i)) \<and>
    (\<forall>j < n. roots ! j = value (ms ! j)) \<and>
    (\<forall>j < n.
      p.next_fri_layer
        (ps ! j)
        (ds ! j)
        (challenges ! j) =
          (ps ! Suc j, ds ! Suc j, ls ! Suc j))"
proof -
  have send_counter:
    "\<And>x s t. Some ((), t) \<in> set_dist (execute (p.send x) s) \<Longrightarrow>
      PCompositionFriCounter t = PCompositionFriCounter s"
  proof -
    fix x s t
    assume send: "Some ((), t) \<in> set_dist (execute (p.send x) s)"
    show "PCompositionFriCounter t = PCompositionFriCounter s"
      using p.send_outcome[OF send] by simp
  qed
  have receiver:
    "\<And>b s t. Some (b, t) \<in>
        set_dist (execute p.receive_composition_fri_challenge s) \<Longrightarrow>
      s \<le> t \<and>
      PState t = PState s \<and>
      PTranscript t = PTranscript s \<and>
      PCompositionFriCounter t = Suc (PCompositionFriCounter s) \<and>
      fmlookup (HashMap t)
        (CompositionFriChallenge (PCompositionFriCounter s) (PState s)) = Some b"
  proof -
    fix b s t
    assume rand:
      "Some (b, t) \<in>
        set_dist (execute p.receive_composition_fri_challenge s)"
    show "s \<le> t \<and>
      PState t = PState s \<and>
      PTranscript t = PTranscript s \<and>
      PCompositionFriCounter t = Suc (PCompositionFriCounter s) \<and>
      fmlookup (HashMap t)
        (CompositionFriChallenge (PCompositionFriCounter s) (PState s)) = Some b"
      using p.receive_composition_fri_challenge_outcome[OF rand]
        p.receive_composition_fri_challenge_counter_outcome[OF rand]
      by simp
  qed
  have create_counter:
    "\<And>xs m s t. Some (m, t) \<in> set_dist (execute (p.create xs) s) \<Longrightarrow>
      PCompositionFriCounter t = PCompositionFriCounter s"
    by (rule p.create_preserves_channel(4))
  have data:
    "\<exists>roots challenges.
      length roots = n \<and>
      length challenges = n \<and>
      PTranscript t = rev roots @ PTranscript s \<and>
      PState t = foldl concat (PState s) roots \<and>
      s \<le> t \<and>
      PCompositionFriCounter t = PCompositionFriCounter s + n \<and>
      (\<forall>i < length roots.
        fmlookup (HashMap t)
          (CompositionFriChallenge (PCompositionFriCounter s + i)
            (foldl concat (PState s) (take (Suc i) roots))) =
          Some (challenges ! i)) \<and>
      (\<forall>j < n. roots ! j = value (ms ! (length [m] - 1 + j))) \<and>
      (\<forall>j < n.
        p.next_fri_layer
          (ps ! (length [cp] - 1 + j))
          (ds ! (length [cp] - 1 + j))
          (challenges ! j) =
            (ps ! (length [cp] + j),
             ds ! (length [cp] + j),
             ls ! (length [cp] + j)))"
    unfolding p.composition_fri_commit_def
    by (rule fri_commit_with_replay_successor_data
        [where counter=PCompositionFriCounter and tag=CompositionFriChallenge,
          OF send_counter receiver create_counter
          outcome[unfolded p.composition_fri_commit_def]]) simp_all
  then show ?thesis by auto
qed

lemma fri_commit_initial_heads:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.fri_commit n [cp] [d] [l] [m]) s)"
  shows
    "ps ! 0 = cp"
    "ds ! 0 = d"
    "ls ! 0 = l"
    "ms ! 0 = m"
proof -
  have lens:
    "length ps = Suc n"
    "length ds = Suc n"
    "length ls = Suc n"
    "length ms = Suc n"
    using p.fri_commit_lengths[OF outcome] by simp_all
  have prefixes:
    "take (length [cp]) ps = [cp]"
    "take (length [d]) ds = [d]"
    "take (length [l]) ls = [l]"
    "take (length [m]) ms = [m]"
    using p.fri_commit_preserves_prefix[OF outcome] by simp_all
  show "ps ! 0 = cp"
    using lens prefixes by (cases ps) auto
  show "ds ! 0 = d"
    using lens prefixes by (cases ds) auto
  show "ls ! 0 = l"
    using lens prefixes by (cases ls) auto
  show "ms ! 0 = m"
    using lens prefixes by (cases ms) auto
qed

lemma trace_fri_commit_initial_heads:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.trace_fri_commit n [cp] [d] [l] [m]) s)"
  shows
    "ps ! 0 = cp"
    "ds ! 0 = d"
    "ls ! 0 = l"
    "ms ! 0 = m"
proof -
  have lens:
    "length ps = Suc n"
    "length ds = Suc n"
    "length ls = Suc n"
    "length ms = Suc n"
    using p.trace_fri_commit_lengths[OF outcome] by simp_all
  have prefixes:
    "take (length [cp]) ps = [cp]"
    "take (length [d]) ds = [d]"
    "take (length [l]) ls = [l]"
    "take (length [m]) ms = [m]"
    using p.trace_fri_commit_preserves_prefix[OF outcome] by simp_all
  show "ps ! 0 = cp"
    using lens prefixes by (cases ps) auto
  show "ds ! 0 = d"
    using lens prefixes by (cases ds) auto
  show "ls ! 0 = l"
    using lens prefixes by (cases ls) auto
  show "ms ! 0 = m"
    using lens prefixes by (cases ms) auto
qed

lemma composition_fri_commit_initial_heads:
  assumes outcome:
    "Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute
        (p.composition_fri_commit n [cp] [d] [l] [m]) s)"
  shows
    "ps ! 0 = cp"
    "ds ! 0 = d"
    "ls ! 0 = l"
    "ms ! 0 = m"
proof -
  have lens:
    "length ps = Suc n"
    "length ds = Suc n"
    "length ls = Suc n"
    "length ms = Suc n"
    using p.composition_fri_commit_lengths[OF outcome] by simp_all
  have prefixes:
    "take (length [cp]) ps = [cp]"
    "take (length [d]) ds = [d]"
    "take (length [l]) ls = [l]"
    "take (length [m]) ms = [m]"
    using p.composition_fri_commit_preserves_prefix[OF outcome] by simp_all
  show "ps ! 0 = cp"
    using lens prefixes by (cases ps) auto
  show "ds ! 0 = d"
    using lens prefixes by (cases ds) auto
  show "ls ! 0 = l"
    using lens prefixes by (cases ls) auto
  show "ms ! 0 = m"
    using lens prefixes by (cases ms) auto
qed

definition fri_commit_outcome where
  "fri_commit_outcome n cp d l m ps ds ls ms s t \<longleftrightarrow>
    Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.fri_commit n [cp] [d] [l] [m]) s) \<or>
    Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.trace_fri_commit n [cp] [d] [l] [m]) s) \<or>
    Some ((ps, ds, ls, ms), t) \<in>
      set_dist (execute (p.composition_fri_commit n [cp] [d] [l] [m]) s)"

lemma fri_commit_outcomeI:
  assumes "Some ((ps, ds, ls, ms), t) \<in>
    set_dist (execute (p.fri_commit n [cp] [d] [l] [m]) s)"
  shows "fri_commit_outcome n cp d l m ps ds ls ms s t"
  using assms unfolding fri_commit_outcome_def by blast

lemma trace_fri_commit_outcomeI:
  assumes "Some ((ps, ds, ls, ms), t) \<in>
    set_dist (execute (p.trace_fri_commit n [cp] [d] [l] [m]) s)"
  shows "fri_commit_outcome n cp d l m ps ds ls ms s t"
  using assms unfolding fri_commit_outcome_def by blast

lemma composition_fri_commit_outcomeI:
  assumes "Some ((ps, ds, ls, ms), t) \<in>
    set_dist (execute (p.composition_fri_commit n [cp] [d] [l] [m]) s)"
  shows "fri_commit_outcome n cp d l m ps ds ls ms s t"
  using assms unfolding fri_commit_outcome_def by blast

lemma fri_commit_outcome_initial_heads:
  assumes "fri_commit_outcome n cp d l m ps ds ls ms s t"
  shows
    "ps ! 0 = cp"
    "ds ! 0 = d"
    "ls ! 0 = l"
    "ms ! 0 = m"
  using assms
  unfolding fri_commit_outcome_def
  by (auto dest: fri_commit_initial_heads trace_fri_commit_initial_heads
      composition_fri_commit_initial_heads)

lemma decommit_on_query_step_transcript_extends:
  assumes step_in: "m \<in> set (p.decommit_on_query idx f_merkle)"
    and outcome: "Some (x, t) \<in> set_dist (execute m s)"
  shows "transcript_extends t s"
proof -
  from step_in obtain i where
    m_eq:
      "m = do {
        p.send (p.f_eval ! i);
        mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)
      }"
    unfolding p.decommit_on_query_def by auto
  from outcome[unfolded m_eq] obtain u where
    send_leaf: "Some ((), u) \<in> set_dist (execute (p.send (p.f_eval ! i)) s)"
    and send_path:
      "Some (x, t) \<in>
        set_dist (execute
          (mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)) u)"
    by (auto elim!: p.set_dist_bindE)
  have s_u: "transcript_extends u s"
    using send_transcript_extends[OF send_leaf] .
  have x_unit: "x = ()"
    by (cases x) simp
  have path_out:
    "Some ((), t) \<in>
      set_dist (execute
        (mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)) u)"
    using send_path x_unit by simp
  have u_t: "transcript_extends t u"
    by (rule mfold2_send_transcript_extends[OF path_out])
  show ?thesis
    using s_u u_t by (rule transcript_extends_trans)
qed

lemma decommit_on_query_step_hash_extends:
  assumes step_in: "m \<in> set (p.decommit_on_query idx f_merkle)"
    and outcome: "Some (x, t) \<in> set_dist (execute m s)"
  shows "s \<le> t"
proof -
  from step_in obtain i where
    m_eq:
      "m = do {
        p.send (p.f_eval ! i);
        mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)
      }"
    unfolding p.decommit_on_query_def by auto
  from outcome[unfolded m_eq] obtain u where
    send_leaf: "Some ((), u) \<in> set_dist (execute (p.send (p.f_eval ! i)) s)"
    and send_path:
      "Some (x, t) \<in>
        set_dist (execute
          (mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)) u)"
    by (auto elim!: p.set_dist_bindE)
  have s_u: "s \<le> u"
    using send_hash_extends[OF send_leaf] .
  have x_unit: "x = ()"
    by (cases x) simp
  have path_out:
    "Some ((), t) \<in>
      set_dist (execute
        (mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)) u)"
    using send_path x_unit by simp
  have u_t: "u \<le> t"
    using mfold2_send_hash_extends[OF path_out] .
	  show ?thesis
	    using s_u u_t by (rule p.hash_ext_trans)
	qed

lemma decommit_on_query_step_preserves_query_counter:
  assumes step_in: "m \<in> set (p.decommit_on_query idx f_merkle)"
    and outcome: "Some (x, t) \<in> set_dist (execute m s)"
  shows "PQueryCounter t = PQueryCounter s"
proof -
  from step_in obtain i where
    m_eq:
      "m = do {
        p.send (p.f_eval ! i);
        mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)
      }"
    unfolding p.decommit_on_query_def by auto
  from outcome[unfolded m_eq] obtain u where
    send_leaf: "Some ((), u) \<in> set_dist (execute (p.send (p.f_eval ! i)) s)"
    and send_path:
      "Some (x, t) \<in>
        set_dist (execute
          (mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)) u)"
    by (auto elim!: p.set_dist_bindE)
  have x_unit: "x = ()"
    by (cases x) simp
  have path_out:
    "Some ((), t) \<in>
      set_dist (execute
        (mfold2 p.send (get_authentication_path (length p.f_eval) i f_merkle)) u)"
    using send_path x_unit by simp
  have q_u: "PQueryCounter u = PQueryCounter s"
    using p.send_outcome[OF send_leaf] by simp
  have q_t: "PQueryCounter t = PQueryCounter u"
    by (rule mfold2_send_preserves_query_counter[OF path_out])
  show ?thesis
    using q_u q_t by simp
qed

lemma decommit_on_fri_layers_step_transcript_extends:
  assumes step_in: "m \<in> set (p.decommit_on_fri_layers fs)"
    and outcome: "Some (x, t) \<in> set_dist (execute (m idx) s)"
  shows "transcript_extends t s"
proof -
  from step_in obtain l tree where
    pair_in: "(l, tree) \<in> set fs"
    and m_eq:
      "m = (\<lambda>idx. do {
        let len = length l;
        let idx' = idx mod len;
        let sidx = (idx' + (len div 2)) mod len;
        p.send (l ! idx');
        mfold2 p.send (get_authentication_path len idx' tree);
        p.send (l ! sidx);
        mfold2 p.send (get_authentication_path len sidx tree);
        return idx'
      })"
    unfolding p.decommit_on_fri_layers_def by auto
  let ?len = "length l"
  let ?idx' = "idx mod ?len"
  let ?sidx = "(?idx' + (?len div 2)) mod ?len"
  from outcome[unfolded m_eq Let_def] obtain u1 u2 u3 u4 where
    send_xp: "Some ((), u1) \<in> set_dist (execute (p.send (l ! ?idx')) s)"
    and path_xp:
      "Some ((), u2) \<in>
        set_dist (execute (mfold2 p.send (get_authentication_path ?len ?idx' tree)) u1)"
    and send_xn: "Some ((), u3) \<in> set_dist (execute (p.send (l ! ?sidx)) u2)"
    and path_xn:
      "Some ((), u4) \<in>
        set_dist (execute (mfold2 p.send (get_authentication_path ?len ?sidx tree)) u3)"
    and ret: "Some (x, t) \<in> set_dist (execute (return ?idx') u4)"
    by (auto elim!: p.set_dist_bindE)
  have s_u1: "transcript_extends u1 s"
    using send_transcript_extends[OF send_xp] .
  have u1_u2: "transcript_extends u2 u1"
    using mfold2_send_transcript_extends[OF path_xp] .
  have u2_u3: "transcript_extends u3 u2"
    using send_transcript_extends[OF send_xn] .
  have u3_u4: "transcript_extends u4 u3"
    using mfold2_send_transcript_extends[OF path_xn] .
  have u4_t: "transcript_extends t u4"
    using ret by simp
  show ?thesis
    using s_u1 u1_u2 u2_u3 u3_u4 u4_t by (meson transcript_extends_trans)
qed

lemma decommit_on_fri_layers_step_hash_extends:
  assumes step_in: "m \<in> set (p.decommit_on_fri_layers fs)"
    and outcome: "Some (x, t) \<in> set_dist (execute (m idx) s)"
  shows "s \<le> t"
proof -
  from step_in obtain l tree where
    pair_in: "(l, tree) \<in> set fs"
    and m_eq:
      "m = (\<lambda>idx. do {
        let len = length l;
        let idx' = idx mod len;
        let sidx = (idx' + (len div 2)) mod len;
        p.send (l ! idx');
        mfold2 p.send (get_authentication_path len idx' tree);
        p.send (l ! sidx);
        mfold2 p.send (get_authentication_path len sidx tree);
        return idx'
      })"
    unfolding p.decommit_on_fri_layers_def by auto
  let ?len = "length l"
  let ?idx' = "idx mod ?len"
  let ?sidx = "(?idx' + (?len div 2)) mod ?len"
  from outcome[unfolded m_eq Let_def] obtain u1 u2 u3 u4 where
    send_xp: "Some ((), u1) \<in> set_dist (execute (p.send (l ! ?idx')) s)"
    and path_xp:
      "Some ((), u2) \<in>
        set_dist (execute (mfold2 p.send (get_authentication_path ?len ?idx' tree)) u1)"
    and send_xn: "Some ((), u3) \<in> set_dist (execute (p.send (l ! ?sidx)) u2)"
    and path_xn:
      "Some ((), u4) \<in>
        set_dist (execute (mfold2 p.send (get_authentication_path ?len ?sidx tree)) u3)"
    and ret: "Some (x, t) \<in> set_dist (execute (return ?idx') u4)"
    by (auto elim!: p.set_dist_bindE)
  have s_u1: "s \<le> u1"
    using send_hash_extends[OF send_xp] .
  have u1_u2: "u1 \<le> u2"
    using mfold2_send_hash_extends[OF path_xp] .
  have u2_u3: "u2 \<le> u3"
    using send_hash_extends[OF send_xn] .
  have u3_u4: "u3 \<le> u4"
    using mfold2_send_hash_extends[OF path_xn] .
  have u4_t: "u4 \<le> t"
    using ret unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
	  show ?thesis
	    using s_u1 u1_u2 u2_u3 u3_u4 u4_t by (meson p.hash_ext_trans)
	qed

lemma decommit_on_fri_layers_step_preserves_query_counter:
  assumes step_in: "m \<in> set (p.decommit_on_fri_layers fs)"
    and outcome: "Some (x, t) \<in> set_dist (execute (m idx) s)"
  shows "PQueryCounter t = PQueryCounter s"
proof -
  from step_in obtain l tree where
    m_eq:
      "m = (\<lambda>idx. do {
        let len = length l;
        let idx' = idx mod len;
        let sidx = (idx' + (len div 2)) mod len;
        p.send (l ! idx');
        mfold2 p.send (get_authentication_path len idx' tree);
        p.send (l ! sidx);
        mfold2 p.send (get_authentication_path len sidx tree);
        return idx'
      })"
    unfolding p.decommit_on_fri_layers_def by auto
  let ?len = "length l"
  let ?idx' = "idx mod ?len"
  let ?sidx = "(?idx' + (?len div 2)) mod ?len"
  from outcome[unfolded m_eq Let_def] obtain u1 u2 u3 u4 where
    send_xp: "Some ((), u1) \<in> set_dist (execute (p.send (l ! ?idx')) s)"
    and path_xp:
      "Some ((), u2) \<in>
        set_dist (execute (mfold2 p.send (get_authentication_path ?len ?idx' tree)) u1)"
    and send_xn: "Some ((), u3) \<in> set_dist (execute (p.send (l ! ?sidx)) u2)"
    and path_xn:
      "Some ((), u4) \<in>
        set_dist (execute (mfold2 p.send (get_authentication_path ?len ?sidx tree)) u3)"
    and ret: "Some (x, t) \<in> set_dist (execute (return ?idx') u4)"
    by (auto elim!: p.set_dist_bindE)
  have q_u1: "PQueryCounter u1 = PQueryCounter s"
    using p.send_outcome[OF send_xp] by simp
  have q_u2: "PQueryCounter u2 = PQueryCounter u1"
    by (rule mfold2_send_preserves_query_counter[OF path_xp])
  have q_u3: "PQueryCounter u3 = PQueryCounter u2"
    using p.send_outcome[OF send_xn] by simp
  have q_u4: "PQueryCounter u4 = PQueryCounter u3"
    by (rule mfold2_send_preserves_query_counter[OF path_xn])
  have t_eq: "t = u4"
    using ret by simp
  show ?thesis
    using q_u1 q_u2 q_u3 q_u4 unfolding t_eq by simp
qed

lemma prover_query_round_hash_extends:
  assumes outcome:
    "Some (x, t) \<in> set_dist (execute (prover_query_round f_merkle f_ls f_ms ls ms) s)"
  shows "s \<le> t"
proof -
  from outcome obtain idx s1 qouts s2 f_fri_idx s3 fri_idx where
    rand: "Some (idx, s1) \<in> set_dist (execute p.receive_query_index_challenge s)"
    and query:
      "Some (qouts, s2) \<in>
        set_dist (execute (mmap (p.decommit_on_query (p.index (to_nat idx)) f_merkle)) s1)"
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
    unfolding prover_query_round_def
    by (auto elim!: p.set_dist_bindE)
  have s_s1: "s \<le> s1"
    using p.receive_query_index_challenge_extends[OF rand] .
  have s1_s2: "s1 \<le> s2"
    by (rule mmap_hash_extends[OF query])
      (rule decommit_on_query_step_hash_extends)
  have s2_s3: "s2 \<le> s3"
    by (rule mfold_hash_extends[OF trace_fri])
      (rule decommit_on_fri_layers_step_hash_extends)
  have s3_t: "s3 \<le> t"
    by (rule mfold_hash_extends[OF fri])
      (rule decommit_on_fri_layers_step_hash_extends)
	  show ?thesis
	    using s_s1 s1_s2 s2_s3 s3_t by (meson p.hash_ext_trans)
	qed

lemma prover_query_round_query_counter:
  assumes outcome:
    "Some (x, t) \<in> set_dist (execute (prover_query_round f_merkle f_ls f_ms ls ms) s)"
  shows "PQueryCounter t = Suc (PQueryCounter s)"
proof -
  from outcome obtain idx s1 qouts s2 f_fri_idx s3 fri_idx where
    rand: "Some (idx, s1) \<in> set_dist (execute p.receive_query_index_challenge s)"
    and query:
      "Some (qouts, s2) \<in>
        set_dist (execute (mmap (p.decommit_on_query (p.index (to_nat idx)) f_merkle)) s1)"
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
    unfolding prover_query_round_def
    by (auto elim!: p.set_dist_bindE)
  have q_s1: "PQueryCounter s1 = Suc (PQueryCounter s)"
    using p.receive_query_index_challenge_counter_outcome[OF rand] by simp
  have q_s2: "PQueryCounter s2 = PQueryCounter s1"
    by (rule mmap_preserves_query_counter[OF query])
      (rule decommit_on_query_step_preserves_query_counter)
  have q_s3: "PQueryCounter s3 = PQueryCounter s2"
    by (rule mfold_preserves_query_counter[OF trace_fri])
      (rule decommit_on_fri_layers_step_preserves_query_counter)
  have q_t: "PQueryCounter t = PQueryCounter s3"
    by (rule mfold_preserves_query_counter[OF fri])
      (rule decommit_on_fri_layers_step_preserves_query_counter)
  show ?thesis
    using q_s1 q_s2 q_s3 q_t by simp
qed

lemma prover_query_round_transcript_extends:
  assumes outcome:
    "Some (x, t) \<in> set_dist (execute (prover_query_round f_merkle f_ls f_ms ls ms) s)"
  shows "transcript_extends t s"
proof -
  from outcome obtain idx s1 qouts s2 f_fri_idx s3 fri_idx where
    rand: "Some (idx, s1) \<in> set_dist (execute p.receive_query_index_challenge s)"
    and query:
      "Some (qouts, s2) \<in>
        set_dist (execute (mmap (p.decommit_on_query (p.index (to_nat idx)) f_merkle)) s1)"
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
    unfolding prover_query_round_def
    by (auto elim!: p.set_dist_bindE)
  have s_s1: "transcript_extends s1 s"
    using receive_query_index_challenge_transcript_extends[OF rand] .
  have s1_s2: "transcript_extends s2 s1"
    by (rule mmap_transcript_extends[OF query])
      (rule decommit_on_query_step_transcript_extends)
  have s2_s3: "transcript_extends s3 s2"
    by (rule mfold_transcript_extends[OF trace_fri])
      (rule decommit_on_fri_layers_step_transcript_extends)
  have s3_t: "transcript_extends t s3"
    by (rule mfold_transcript_extends[OF fri])
      (rule decommit_on_fri_layers_step_transcript_extends)
  show ?thesis
    using s_s1 s1_s2 s2_s3 s3_t by (meson transcript_extends_trans)
qed

lemma prover_query_round_outcomeE:
  assumes outcome:
    "Some (x, t) \<in> set_dist (execute (prover_query_round f_merkle f_ls f_ms ls ms) s)"
  obtains idx s1 qouts s2 f_fri_idx s3 fri_idx
  where
    "Some (idx, s1) \<in> set_dist (execute p.receive_query_index_challenge s)"
    "Some (qouts, s2) \<in>
      set_dist (execute
        (mmap (p.decommit_on_query (p.index (to_nat idx)) f_merkle)) s1)"
    "Some (f_fri_idx, s3) \<in>
      set_dist (execute
        (mfold (p.index (to_nat idx))
          (p.decommit_on_fri_layers (butlast (zip f_ls f_ms)))) s2)"
    "Some (fri_idx, t) \<in>
      set_dist (execute
        (mfold (p.index (to_nat idx))
          (p.decommit_on_fri_layers (butlast (zip ls ms)))) s3)"
    "x = ()"
proof -
  from outcome obtain idx s1 qouts s2 f_fri_idx s3 fri_idx s4 where
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
      "Some (fri_idx, s4) \<in>
        set_dist (execute
          (mfold (p.index (to_nat idx))
            (p.decommit_on_fri_layers (butlast (zip ls ms)))) s3)"
    and ret: "Some (x, t) \<in> set_dist (execute (return ()) s4)"
    unfolding prover_query_round_def
    by (auto elim!: p.set_dist_bindE)
  have x_unit: "x = ()"
    using ret by simp
  have t_eq: "t = s4"
    using ret by simp
  show ?thesis
    by (rule that[OF rand query trace_fri _ x_unit])
      (use fri t_eq in simp)
qed

lemma random_send_round_transcript:
  assumes outcome:
    "Some (a, t) \<in>
      set_dist (execute
        (do {
          a \<leftarrow> p.receive_alpha_challenge;
          p.send a;
          return a
        }) s)"
  shows "PTranscript t = a # PTranscript s"
proof -
  from outcome obtain u v where
    rand: "Some (a, u) \<in> set_dist (execute p.receive_alpha_challenge s)"
    and send_a: "Some ((), v) \<in> set_dist (execute (p.send a) u)"
    and ret: "Some (a, t) \<in> set_dist (execute (return a) v)"
    by (auto elim!: p.set_dist_bindE)
  have t_v: "t = v"
    using ret by simp
  have tr_u: "PTranscript u = PTranscript s"
    using receive_alpha_challenge_preserves_transcript[OF rand] .
  have "v = u\<lparr>PState := concat (PState u) a, PTranscript := a # PTranscript u\<rparr>"
    using p.send_outcome[OF send_a] .
  then show ?thesis
    using t_v tr_u by simp
qed

lemma random_send_round_parts_outcome:
  assumes rand: "Some (a, u) \<in> set_dist (execute p.receive_alpha_challenge s)"
    and send_a: "Some ((), t) \<in> set_dist (execute (p.send a) u)"
  shows
    "s \<le> t \<and>
     PState t = concat (PState s) a \<and>
     PTranscript t = a # PTranscript s \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = Suc (PAlphaCounter s) \<and>
     PQueryCounter t = PQueryCounter s \<and>
     fmlookup (HashMap t) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
proof -
  have rand_out:
    "s \<le> u \<and>
     PState u = PState s \<and>
     PTranscript u = PTranscript s \<and>
     fmlookup (HashMap u) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    by (rule p.receive_alpha_challenge_outcome[OF rand])
  have s_u: "s \<le> u"
    using rand_out by simp
  have lookup_u: "fmlookup (HashMap u) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using rand_out by simp
  have state_u: "PState u = PState s"
    using rand_out by simp
  have tr_u: "PTranscript u = PTranscript s"
    using rand_out by simp
  have alpha_counter_u: "PAlphaCounter u = Suc (PAlphaCounter s)"
    using p.receive_alpha_challenge_counter_outcome[OF rand] by simp
  have other_counters_u:
    "PTraceFriCounter u = PTraceFriCounter s \<and>
     PCompositionFriCounter u = PCompositionFriCounter s \<and>
     PQueryCounter u = PQueryCounter s"
    using p.receive_alpha_challenge_counter_outcome[OF rand] by simp
  have t_eq: "t = u\<lparr>PState := concat (PState u) a, PTranscript := a # PTranscript u\<rparr>"
    using p.send_outcome[OF send_a] .
  have u_t: "u \<le> t"
    unfolding t_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  have s_t: "s \<le> t"
    using s_u u_t by (rule p.hash_ext_trans)
  have lookup_t: "fmlookup (HashMap t) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using p.hash_extension_lookup[OF lookup_u u_t] .
  show ?thesis
    using s_t state_u tr_u alpha_counter_u other_counters_u lookup_t
    unfolding t_eq by simp
qed

lemma random_send_round_outcome:
  assumes outcome:
    "Some (a, t) \<in>
      set_dist (execute
        (do {
          a \<leftarrow> p.receive_alpha_challenge;
          p.send a;
          return a
        }) s)"
  shows
    "s \<le> t \<and>
     PState t = concat (PState s) a \<and>
     PTranscript t = a # PTranscript s \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = Suc (PAlphaCounter s) \<and>
     PQueryCounter t = PQueryCounter s \<and>
     fmlookup (HashMap t) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
proof -
  from outcome obtain u v where
    rand: "Some (a, u) \<in> set_dist (execute p.receive_alpha_challenge s)"
    and send_a: "Some ((), v) \<in> set_dist (execute (p.send a) u)"
    and ret: "Some (a, t) \<in> set_dist (execute (return a) v)"
    by (auto elim!: p.set_dist_bindE)
  have t_v: "t = v"
    using ret by simp
  show ?thesis
    using random_send_round_parts_outcome[OF rand send_a] unfolding t_v .
qed

lemma alpha_mmap_transcript:
  assumes outcome:
    "Some (as, t) \<in>
      set_dist (execute
        (mmap (replicate n
          (do {
            a \<leftarrow> p.receive_alpha_challenge;
            p.send a;
            return a
          }))) s)"
  shows "length as = n \<and> PTranscript t = rev as @ PTranscript s"
  using outcome
proof (induction n arbitrary: as s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?round =
    "do {
      a \<leftarrow> p.receive_alpha_challenge;
      p.send a;
      return a
    }"
  from Suc.prems obtain a u0 u as' where
    rand: "Some (a, u0) \<in> set_dist (execute p.receive_alpha_challenge s)"
    and send_a: "Some ((), u) \<in> set_dist (execute (p.send a) u0)"
    and rest:
      "Some (as', t) \<in>
        set_dist (execute (mmap (replicate n ?round)) u)"
    and as_eq: "as = a # as'"
    by (auto elim!: p.set_dist_bindE)
  have tr_u0: "PTranscript u0 = PTranscript s"
    using receive_alpha_challenge_preserves_transcript[OF rand] .
  have tr_u: "PTranscript u = a # PTranscript s"
    using p.send_outcome[OF send_a] tr_u0 by simp
  have ih: "length as' = n \<and> PTranscript t = rev as' @ PTranscript u"
    using Suc.IH[OF rest] .
  show ?case
    using as_eq tr_u ih by simp
qed

lemma alpha_mmap_outcome:
  assumes outcome:
    "Some (as, t) \<in>
      set_dist (execute
        (mmap (replicate n
          (do {
            a \<leftarrow> p.receive_alpha_challenge;
            p.send a;
            return a
          }))) s)"
  shows
    "length as = n \<and>
     s \<le> t \<and>
     PState t = foldl concat (PState s) as \<and>
     PTranscript t = rev as @ PTranscript s \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s + length as \<and>
     PQueryCounter t = PQueryCounter s \<and>
     (\<forall>i < length as.
        fmlookup (HashMap t)
          (AlphaChallenge (PAlphaCounter s + i)
            (foldl concat (PState s) (take i as))) = Some (as ! i))"
  using outcome
proof (induction n arbitrary: as s t)
  case 0
  then show ?case
    unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
next
  case (Suc n)
  let ?round =
    "do {
      a \<leftarrow> p.receive_alpha_challenge;
      p.send a;
      return a
    }"
  from Suc.prems obtain a u0 u as' where
    rand: "Some (a, u0) \<in> set_dist (execute p.receive_alpha_challenge s)"
    and send_a: "Some ((), u) \<in> set_dist (execute (p.send a) u0)"
    and tail:
      "Some (as', t) \<in>
        set_dist (execute (mmap (replicate n ?round)) u)"
    and as_eq: "as = a # as'"
    by (auto elim!: p.set_dist_bindE)
  have head_data:
    "s \<le> u \<and>
     PState u = concat (PState s) a \<and>
     PTranscript u = a # PTranscript s \<and>
     PTraceFriCounter u = PTraceFriCounter s \<and>
     PCompositionFriCounter u = PCompositionFriCounter s \<and>
     PAlphaCounter u = Suc (PAlphaCounter s) \<and>
     PQueryCounter u = PQueryCounter s \<and>
     fmlookup (HashMap u) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using random_send_round_parts_outcome[OF rand send_a] .
  have tail_data:
    "length as' = n \<and>
     u \<le> t \<and>
     PState t = foldl concat (PState u) as' \<and>
     PTranscript t = rev as' @ PTranscript u \<and>
     PTraceFriCounter t = PTraceFriCounter u \<and>
     PCompositionFriCounter t = PCompositionFriCounter u \<and>
     PAlphaCounter t = PAlphaCounter u + length as' \<and>
     PQueryCounter t = PQueryCounter u \<and>
     (\<forall>i < length as'.
        fmlookup (HashMap t)
          (AlphaChallenge (PAlphaCounter u + i)
            (foldl concat (PState u) (take i as'))) = Some (as' ! i))"
    using Suc.IH[OF tail] .
  have s_t: "s \<le> t"
    using head_data tail_data by (meson p.hash_ext_trans)
  have lookup_head:
    "fmlookup (HashMap t) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using head_data tail_data by (meson p.hash_extension_lookup)
  have lookup_all:
    "\<forall>i < length (a # as').
      fmlookup (HashMap t)
        (AlphaChallenge (PAlphaCounter s + i)
          (foldl concat (PState s) (take i (a # as')))) =
        Some ((a # as') ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length (a # as')"
    show "fmlookup (HashMap t)
        (AlphaChallenge (PAlphaCounter s + i)
          (foldl concat (PState s) (take i (a # as')))) =
      Some ((a # as') ! i)"
    proof (cases i)
      case 0
      then show ?thesis
        using lookup_head by simp
    next
      case (Suc j)
      then have j_bound: "j < length as'"
        using i_bound by simp
      have fold_eq:
        "foldl concat (PState s) (take (Suc j) (a # as')) =
          foldl concat (PState u) (take j as')"
        using head_data by simp
      have alpha_u: "PAlphaCounter u = Suc (PAlphaCounter s)"
        using head_data by simp
      show ?thesis
        using tail_data j_bound fold_eq Suc alpha_u by simp
    qed
  qed
  show ?case
    using as_eq head_data tail_data s_t lookup_all by simp
qed

lemma honest_alpha_mmap_replay_no_failure:
  assumes lookups:
    "\<forall>i < length as.
      fmlookup (HashMap s)
        (AlphaChallenge (PAlphaCounter s + i)
          (foldl concat (PState s) (take i as))) = Some (as ! i)"
  shows
    "None \<notin> dom (dist (execute
      (mmap (replicate (length as)
        (do {
          a0 \<leftarrow> p.receive_alpha_challenge;
          let a0' = a0;
          a1 \<leftarrow> p.read;
          let a1' = a1;
          assert (a0' = a1');
          return a1'
        })))
      (s\<lparr>PTranscript := as @ rest\<rparr>)))"
  using lookups
proof (induction as arbitrary: s rest)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  have lookup_a: "fmlookup (HashMap s) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using spec[OF Cons.prems, of 0] by simp
  have head_nf:
    "None \<notin> dom (dist (execute ?round
      (s\<lparr>PTranscript := a # (as @ rest)\<rparr>)))"
    using honest_alpha_round_replay_no_failure[OF lookup_a, of "as @ rest"]
    by simp
  have full_eq:
    "mmap (replicate (length (a # as)) ?round) =
      (?round \<bind> (\<lambda>x. mmap (replicate (length as) ?round) \<bind> (\<lambda>xs. return (x # xs))))"
    by simp
  have start_eq:
    "s\<lparr>PTranscript := (a # as) @ rest\<rparr> =
      s\<lparr>PTranscript := a # (as @ rest)\<rparr>"
    by simp
  show ?case
    unfolding full_eq start_eq
  proof (rule no_failure_bindI[OF head_nf])
    fix y t
    assume head:
      "Some (y, t) \<in>
        set_dist (execute ?round (s\<lparr>PTranscript := a # as @ rest\<rparr>))"
    have head_out:
      "y = a \<and>
       PState t = concat (PState s) a \<and>
       PTranscript t = as @ rest \<and>
       PAlphaCounter t = Suc (PAlphaCounter s) \<and>
       s \<le> t"
      using honest_alpha_round_replay_outcome[OF lookup_a head] by simp
    have tail_lookups:
      "\<forall>i < length as.
        fmlookup (HashMap t)
          (AlphaChallenge (PAlphaCounter t + i)
            (foldl concat (PState t) (take i as))) = Some (as ! i)"
    proof (intro allI impI)
      fix i
      assume i_bound: "i < length as"
      have old_lookup:
        "fmlookup (HashMap s)
          (AlphaChallenge (PAlphaCounter s + Suc i)
            (foldl concat (PState s) (take (Suc i) (a # as)))) =
            Some ((a # as) ! Suc i)"
        using spec[OF Cons.prems, of "Suc i"] i_bound by simp
      have key_eq:
        "foldl concat (PState s) (take (Suc i) (a # as)) =
          foldl concat (PState t) (take i as)"
        using head_out by simp
      show "fmlookup (HashMap t)
          (AlphaChallenge (PAlphaCounter t + i)
            (foldl concat (PState t) (take i as))) =
        Some (as ! i)"
        using p.hash_extension_lookup[OF old_lookup, of t] head_out key_eq i_bound
        by simp
    qed
    have tail_nf_start:
      "None \<notin> dom (dist (execute
        (mmap (replicate (length as) ?round))
        (t\<lparr>PTranscript := as @ rest\<rparr>)))"
      using Cons.IH[OF tail_lookups, of rest] .
    have t_update: "t\<lparr>PTranscript := as @ rest\<rparr> = t"
      using head_out by simp
    have tail_nf:
      "None \<notin> dom (dist (execute
        (mmap (replicate (length as) ?round)) t))"
      using tail_nf_start unfolding t_update .
    show "None \<notin> dom (dist (execute
      (mmap (replicate (length as) ?round) \<bind> (\<lambda>xs. return (y # xs))) t))"
      by (rule no_failure_bindI[OF tail_nf]) simp
  qed
qed

lemma honest_alpha_mmap_replay_outcome:
  assumes lookups:
    "\<forall>i < length as.
      fmlookup (HashMap s)
        (AlphaChallenge (PAlphaCounter s + i)
          (foldl concat (PState s) (take i as))) = Some (as ! i)"
    and outcome:
      "Some (ys, t) \<in> set_dist (execute
        (mmap (replicate (length as)
          (do {
            a0 \<leftarrow> p.receive_alpha_challenge;
            let a0' = a0;
            a1 \<leftarrow> p.read;
            let a1' = a1;
            assert (a0' = a1');
            return a1'
          })))
        (s\<lparr>PTranscript := as @ rest\<rparr>))"
  shows
    "ys = as \<and>
     PState t = foldl concat (PState s) as \<and>
     PTranscript t = rest \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s + length as \<and>
     PQueryCounter t = PQueryCounter s \<and>
     s \<le> t"
  using lookups outcome
proof (induction as arbitrary: ys s t rest)
  case Nil
  have t_eq: "t = s\<lparr>PTranscript := rest\<rparr>"
    using Nil.prems(2) by simp
  have ys_eq: "ys = []"
    using Nil.prems(2) by simp
  have s_t: "s \<le> t"
    unfolding t_eq less_eq_hash_ext_def less_eq_fmap_def by simp
  show ?case
    using ys_eq t_eq s_t by simp
next
  case (Cons a as)
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  from Cons.prems(2) obtain a0 r_state y read_state u ys' where
    rand:
      "Some (a0, r_state) \<in>
        set_dist (execute p.receive_alpha_challenge
          (s\<lparr>PTranscript := a # (as @ rest)\<rparr>))"
    and read:
      "Some (y, read_state) \<in> set_dist (execute p.read r_state)"
    and assert_ok:
      "Some ((), u) \<in> set_dist (execute (assert (a0 = y)) read_state)"
    and tail:
      "Some (ys', t) \<in>
        set_dist (execute (mmap (replicate (length as) ?round)) u)"
    and ys_eq: "ys = y # ys'"
    by (auto elim!: p.set_dist_bindE)
  have lookup_a: "fmlookup (HashMap s) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using spec[OF Cons.prems(1), of 0] by simp
  have head_out:
    "y = a \<and>
     PState u = concat (PState s) a \<and>
     PTranscript u = as @ rest \<and>
     PTraceFriCounter u = PTraceFriCounter s \<and>
     PCompositionFriCounter u = PCompositionFriCounter s \<and>
     PAlphaCounter u = Suc (PAlphaCounter s) \<and>
     PQueryCounter u = PQueryCounter s \<and>
     s \<le> u"
    using honest_alpha_round_replay_parts_outcome[
      OF lookup_a rand read assert_ok] .
  have tail_lookups:
    "\<forall>i < length as.
      fmlookup (HashMap u)
        (AlphaChallenge (PAlphaCounter u + i)
          (foldl concat (PState u) (take i as))) = Some (as ! i)"
  proof (intro allI impI)
    fix i
    assume i_bound: "i < length as"
    have old_lookup:
      "fmlookup (HashMap s)
        (AlphaChallenge (PAlphaCounter s + Suc i)
          (foldl concat (PState s) (take (Suc i) (a # as)))) =
          Some ((a # as) ! Suc i)"
      using spec[OF Cons.prems(1), of "Suc i"] i_bound by simp
    have key_eq:
      "foldl concat (PState s) (take (Suc i) (a # as)) =
        foldl concat (PState u) (take i as)"
      using head_out by simp
    show "fmlookup (HashMap u)
        (AlphaChallenge (PAlphaCounter u + i)
          (foldl concat (PState u) (take i as))) =
      Some (as ! i)"
      using p.hash_extension_lookup[OF old_lookup, of u] head_out key_eq i_bound
      by simp
  qed
  have u_update: "u\<lparr>PTranscript := as @ rest\<rparr> = u"
    using head_out by simp
  have tail':
    "Some (ys', t) \<in>
      set_dist (execute (mmap (replicate (length as) ?round))
        (u\<lparr>PTranscript := as @ rest\<rparr>))"
    using tail unfolding u_update .
  have tail_out:
    "ys' = as \<and>
     PState t = foldl concat (PState u) as \<and>
     PTranscript t = rest \<and>
     PTraceFriCounter t = PTraceFriCounter u \<and>
     PCompositionFriCounter t = PCompositionFriCounter u \<and>
     PAlphaCounter t = PAlphaCounter u + length as \<and>
     PQueryCounter t = PQueryCounter u \<and>
     u \<le> t"
    using Cons.IH[OF tail_lookups tail'] .
  have s_t: "s \<le> t"
    using head_out tail_out by (meson p.hash_ext_trans)
	  show ?case
	    using ys_eq head_out tail_out s_t by simp
	qed

lemma honest_alpha_replay_round_preserves_query_counter:
  assumes outcome:
    "Some (y, t) \<in> set_dist (execute
      (do {
        a0 \<leftarrow> p.receive_alpha_challenge;
        let a0' = a0;
        a1 \<leftarrow> p.read;
        let a1' = a1;
        assert (a0' = a1');
        return a1'
      }) s)"
  shows "PQueryCounter t = PQueryCounter s"
proof -
  from outcome obtain a0 r_state read_state where
    rand:
      "Some (a0, r_state) \<in> set_dist (execute p.receive_alpha_challenge s)"
    and read:
      "Some (y, read_state) \<in> set_dist (execute p.read r_state)"
    and assert_ok: "Some ((), t) \<in> set_dist (execute (assert (a0 = y)) read_state)"
    by (auto simp: Let_def elim!: p.set_dist_bindE)
  have q_rand: "PQueryCounter r_state = PQueryCounter s"
    using p.receive_alpha_challenge_counter_outcome[OF rand] by simp
  have q_read: "PQueryCounter read_state = PQueryCounter r_state"
    using read_preserves_counters[OF read] by simp
  have t_eq: "t = read_state"
    using assert_outcomeD(2)[OF assert_ok] .
  show ?thesis
    using q_rand q_read unfolding t_eq by simp
qed

lemma honest_alpha_mmap_replay_preserves_query_counter:
  assumes outcome:
    "Some (ys, t) \<in> set_dist (execute
      (mmap (replicate n
        (do {
          a0 \<leftarrow> p.receive_alpha_challenge;
          let a0' = a0;
          a1 \<leftarrow> p.read;
          let a1' = a1;
          assert (a0' = a1');
          return a1'
        }))) s)"
  shows "PQueryCounter t = PQueryCounter s"
  using outcome
proof (induction n arbitrary: ys s t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?round =
    "do {
      a0 \<leftarrow> p.receive_alpha_challenge;
      let a0' = a0;
      a1 \<leftarrow> p.read;
      let a1' = a1;
      assert (a0' = a1');
      return a1'
    }"
  from Suc.prems obtain a0 r_state y read_state u ys' where
    rand:
      "Some (a0, r_state) \<in> set_dist (execute p.receive_alpha_challenge s)"
    and read:
      "Some (y, read_state) \<in> set_dist (execute p.read r_state)"
    and assert_ok:
      "Some ((), u) \<in> set_dist (execute (assert (a0 = y)) read_state)"
    and tail: "Some (ys', t) \<in> set_dist (execute (mmap (replicate n ?round)) u)"
    by (auto elim!: p.set_dist_bindE)
  have q_rand: "PQueryCounter r_state = PQueryCounter s"
    using p.receive_alpha_challenge_counter_outcome[OF rand] by simp
  have q_read: "PQueryCounter read_state = PQueryCounter r_state"
    using read_preserves_counters[OF read] by simp
  have u_eq: "u = read_state"
    using assert_outcomeD(2)[OF assert_ok] .
  have q_head: "PQueryCounter u = PQueryCounter s"
    using q_rand q_read unfolding u_eq by simp
  have q_tail: "PQueryCounter t = PQueryCounter u"
    by (rule Suc.IH[OF tail])
  show ?case
    using q_head q_tail by simp
qed

lemma prover_root_alpha_degree_transcript:
  assumes create_f:
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
  shows
    "length as = length spec \<and>
     PTranscript s4 = of_nat (degree cp') # rev as @ [value f_merkle]"
proof -
  have tr_s1: "PTranscript s1 = []"
    using create_preserves_transcript[OF create_f]
    unfolding init_state_def by simp
  have tr_s2: "PTranscript s2 = [value f_merkle]"
    using p.send_outcome[OF send_f] tr_s1 by simp
  have alpha_tr:
    "length as = length spec \<and> PTranscript s3 = rev as @ PTranscript s2"
    using alpha_mmap_transcript[OF alphas] .
  have tr_s4: "PTranscript s4 = of_nat (degree cp') # PTranscript s3"
    using p.send_outcome[OF send_degree] by simp
  show ?thesis
    using alpha_tr tr_s2 tr_s4 by simp
qed

lemma prover_later_phases_transcript_extends:
  assumes create_cp:
    "Some (cp_merkle, s5) \<in> set_dist (execute (p.create (p.cp_eval as)) s4)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute
          (p.fri_commit nrounds [cp'] [p.eval_domain] [p.cp_eval as] [cp_merkle]) s5)"
    and final_send:
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
  shows "transcript_extends prover_state s4"
proof -
  have s4_s5: "transcript_extends s5 s4"
    using create_transcript_extends[OF create_cp] .
  have s5_s6: "transcript_extends s6 s5"
    using fri_commit_transcript_extends[OF fri] .
  have s6_final: "transcript_extends s_final s6"
    using send_transcript_extends[OF final_send] .
  have final_s7: "transcript_extends s7 s_final"
    using receive_query_index_challenge_transcript_extends[OF random_idx] .
  have s7_s8: "transcript_extends s8 s7"
    by (rule mmap_transcript_extends[OF query_decommit])
      (rule decommit_on_query_step_transcript_extends)
  have s8_s9: "transcript_extends s9 s8"
    by (rule mfold_transcript_extends[OF fri_decommit])
      (rule decommit_on_fri_layers_step_transcript_extends)
  have s9_prover: "transcript_extends prover_state s9"
    using prover_state_eq by simp
  show ?thesis
    using s4_s5 s5_s6 s6_final final_s7 s7_s8 s8_s9 s9_prover
    by (meson transcript_extends_trans)
qed

lemma prover_later_phases_hash_extends:
  assumes send_degree:
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
    and query_decommit:
      "Some (qouts, s8) \<in>
        set_dist (execute (mmap (p.decommit_on_query idx' f_merkle)) s7)"
    and fri_decommit:
      "Some (fri_idx, s9) \<in>
        set_dist (execute
          (mfold idx' (p.decommit_on_fri_layers (butlast (zip ls ms)))) s8)"
    and prover_state_eq: "prover_state = s9"
  shows "s3 \<le> prover_state"
proof -
  have s3_s4: "s3 \<le> s4"
    using send_hash_extends[OF send_degree] .
  have s4_s5: "s4 \<le> s5"
    using create_hash_extends[OF create_cp] .
  have s5_s6: "s5 \<le> s6"
    using honest_fri_commit_extends[OF fri] .
  have s6_final: "s6 \<le> s_final"
    using send_hash_extends[OF final_send] .
  have final_s7: "s_final \<le> s7"
    using p.receive_query_index_challenge_extends[OF random_idx] .
  have s7_s8: "s7 \<le> s8"
    by (rule mmap_hash_extends[OF query_decommit])
      (rule decommit_on_query_step_hash_extends)
  have s8_s9: "s8 \<le> s9"
    by (rule mfold_hash_extends[OF fri_decommit])
      (rule decommit_on_fri_layers_step_hash_extends)
  have s9_prover: "s9 \<le> prover_state"
    using prover_state_eq p.hash_ext_refl by simp
  show ?thesis
    using s3_s4 s4_s5 s5_s6 s6_final final_s7 s7_s8 s8_s9 s9_prover
    by (meson p.hash_ext_trans)
qed

lemma prover_after_fri_transcript_extends:
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
  shows "transcript_extends prover_state s6"
proof -
  have s6_final: "transcript_extends s_final s6"
    using send_transcript_extends[OF final_send] .
  have final_s7: "transcript_extends s7 s_final"
    using receive_query_index_challenge_transcript_extends[OF random_idx] .
  have s7_s8: "transcript_extends s8 s7"
    by (rule mmap_transcript_extends[OF query_decommit])
      (rule decommit_on_query_step_transcript_extends)
  have s8_s9: "transcript_extends s9 s8"
    by (rule mfold_transcript_extends[OF fri_decommit])
      (rule decommit_on_fri_layers_step_transcript_extends)
  have s9_prover: "transcript_extends prover_state s9"
    using prover_state_eq by simp
  show ?thesis
    using s6_final final_s7 s7_s8 s8_s9 s9_prover by (meson transcript_extends_trans)
qed

lemma prover_after_fri_hash_extends:
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
  shows "s6 \<le> prover_state"
proof -
  have s6_final: "s6 \<le> s_final"
    using send_hash_extends[OF final_send] .
  have final_s7: "s_final \<le> s7"
    using p.receive_query_index_challenge_extends[OF random_idx] .
  have s7_s8: "s7 \<le> s8"
    by (rule mmap_hash_extends[OF query_decommit])
      (rule decommit_on_query_step_hash_extends)
  have s8_s9: "s8 \<le> s9"
    by (rule mfold_hash_extends[OF fri_decommit])
      (rule decommit_on_fri_layers_step_hash_extends)
  have s9_prover: "s9 \<le> prover_state"
    using prover_state_eq p.hash_ext_refl by simp
  show ?thesis
    using s6_final final_s7 s7_s8 s8_s9 s9_prover by (meson p.hash_ext_trans)
qed

lemma prover_after_final_hash_extends:
  assumes random_idx:
    "Some (idx, s7) \<in> set_dist (execute p.receive_query_index_challenge s_final)"
    and query_decommit:
      "Some (qouts, s8) \<in>
        set_dist (execute (mmap (p.decommit_on_query idx' f_merkle)) s7)"
    and fri_decommit:
      "Some (fri_idx, s9) \<in>
        set_dist (execute
          (mfold idx' (p.decommit_on_fri_layers (butlast (zip ls ms)))) s8)"
    and prover_state_eq: "prover_state = s9"
  shows "s_final \<le> prover_state"
proof -
  have final_s7: "s_final \<le> s7"
    using p.receive_query_index_challenge_extends[OF random_idx] .
  have s7_s8: "s7 \<le> s8"
    by (rule mmap_hash_extends[OF query_decommit])
      (rule decommit_on_query_step_hash_extends)
  have s8_s9: "s8 \<le> s9"
    by (rule mfold_hash_extends[OF fri_decommit])
      (rule decommit_on_fri_layers_step_hash_extends)
  have s9_prover: "s9 \<le> prover_state"
    using prover_state_eq p.hash_ext_refl by simp
  show ?thesis
    using final_s7 s7_s8 s8_s9 s9_prover by (meson p.hash_ext_trans)
qed

lemma prover_query_random_lookup_in_replay_state:
  assumes random_idx:
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
  shows "fmlookup (HashMap replay_state) (QueryIndexChallenge (PQueryCounter s_final) (PState s_final)) = Some idx"
proof -
  have lookup_s7: "fmlookup (HashMap s7) (QueryIndexChallenge (PQueryCounter s_final) (PState s_final)) = Some idx"
    using p.receive_query_index_challenge_outcome[OF random_idx] by simp
  have s7_prover: "s7 \<le> prover_state"
  proof -
    have s7_s8: "s7 \<le> s8"
      by (rule mmap_hash_extends[OF query_decommit])
        (rule decommit_on_query_step_hash_extends)
    have s8_s9: "s8 \<le> s9"
      by (rule mfold_hash_extends[OF fri_decommit])
        (rule decommit_on_fri_layers_step_hash_extends)
    have s9_prover: "s9 \<le> prover_state"
      using prover_state_eq p.hash_ext_refl by simp
    show ?thesis
      using s7_s8 s8_s9 s9_prover by (meson p.hash_ext_trans)
  qed
  have lookup_prover:
    "fmlookup (HashMap prover_state) (QueryIndexChallenge (PQueryCounter s_final) (PState s_final)) = Some idx"
    using p.hash_extension_lookup[OF lookup_s7 s7_prover] .
	  show ?thesis
	    using lookup_prover replay
	    unfolding verifier_replay_state_def by simp
	qed

lemma prover_final_query_counter_in_replay_state:
  assumes create_f:
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
    and send_degree:
      "Some ((), s4) \<in> set_dist (execute (p.send degree_msg) s3)"
    and create_cp:
      "Some (cp_merkle, s5) \<in> set_dist (execute (p.create cp_eval) s4)"
    and fri:
      "Some ((ps, ds, ls, ms), s6) \<in>
        set_dist (execute (p.fri_commit n ps0 ds0 ls0 ms0) s5)"
    and final_send:
      "Some ((), s_final) \<in> set_dist (execute (p.send final_msg) s6)"
    and replay: "replay_state = verifier_replay_state prover_state"
  shows "PQueryCounter s_final = PQueryCounter replay_state"
proof -
  have q_s1_zero: "PQueryCounter s1 = 0"
    using p.create_preserves_channel(6)[OF create_f]
    unfolding init_state_def by simp
  have q_s2_zero: "PQueryCounter s2 = 0"
    using p.send_outcome[OF send_f] q_s1_zero by simp
  have q_s3_zero: "PQueryCounter s3 = 0"
    using alpha_mmap_outcome[OF alphas] q_s2_zero by simp
  have q_s4_zero: "PQueryCounter s4 = 0"
    using p.send_outcome[OF send_degree] q_s3_zero by simp
  have q_s5_zero: "PQueryCounter s5 = 0"
    using p.create_preserves_channel(6)[OF create_cp] q_s4_zero by simp
  have q_s6_zero: "PQueryCounter s6 = 0"
    using fri_commit_preserves_query_counter[OF fri] q_s5_zero by simp
  have q_final_zero: "PQueryCounter s_final = 0"
    using p.send_outcome[OF final_send] q_s6_zero by simp
  have q_replay_zero: "PQueryCounter replay_state = 0"
    using replay unfolding verifier_replay_state_def by simp
  show ?thesis
    using q_final_zero q_replay_zero by simp
qed

lemma prover_alpha_lookups_in_replay_state:
  assumes create_f:
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
    and later_hash: "s3 \<le> prover_state"
    and replay: "replay_state = verifier_replay_state prover_state"
  shows
    "\<forall>i < length as.
      fmlookup (HashMap replay_state)
        (AlphaChallenge (PAlphaCounter replay_state + i)
          (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
        Some (as ! i)"
proof -
  have st_s1: "PState s1 = 0"
    using create_preserves_state[OF create_f]
    unfolding init_state_def by simp
  have send_res:
    "s2 = s1\<lparr>
      PState := concat (PState s1) (value f_merkle),
      PTranscript := value f_merkle # PTranscript s1\<rparr>"
    using p.send_outcome[OF send_f] .
  have st_s2: "PState s2 = concat 0 (value f_merkle)"
    using st_s1 send_res by simp
  have alpha_s1_zero: "PAlphaCounter s1 = 0"
    using p.create_preserves_channel(5)[OF create_f]
    unfolding init_state_def by simp
  have alpha_s2_zero: "PAlphaCounter s2 = 0"
    using p.send_outcome[OF send_f] alpha_s1_zero by simp
  have alpha_data:
    "length as = length spec \<and>
     s2 \<le> s3 \<and>
     PState s3 = foldl concat (PState s2) as \<and>
     PTranscript s3 = rev as @ PTranscript s2 \<and>
     (\<forall>i < length as.
        fmlookup (HashMap s3)
          (AlphaChallenge (PAlphaCounter s2 + i)
            (foldl concat (PState s2) (take i as))) = Some (as ! i))"
    using alpha_mmap_outcome[OF alphas] by simp
  show ?thesis
  proof (intro allI impI)
    fix i
	    assume i_bound: "i < length as"
	    have lookup_s3:
	      "fmlookup (HashMap s3)
	        (AlphaChallenge (PAlphaCounter s2 + i)
	          (foldl concat (PState s2) (take i as))) = Some (as ! i)"
	      using alpha_data i_bound by simp
	    have lookup_final:
	      "fmlookup (HashMap prover_state)
	        (AlphaChallenge (PAlphaCounter s2 + i)
	          (foldl concat (PState s2) (take i as))) =
	        Some (as ! i)"
	      using p.hash_extension_lookup[OF lookup_s3 later_hash] .
	    show "fmlookup (HashMap replay_state)
	      (AlphaChallenge (PAlphaCounter replay_state + i)
	        (foldl concat (concat (PState replay_state) (value f_merkle)) (take i as))) =
	      Some (as ! i)"
	      using lookup_final st_s2 replay alpha_s2_zero
	      unfolding verifier_replay_state_def by simp
	  qed
	qed

end

end
