(*  Title:      Stark/Channel_Transcript.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Channel_Transcript
  imports Channel_Core
begin

locale channel = merkle_tree +
  constrains concat :: "'a::finite \<Rightarrow> 'a \<Rightarrow> 'a"
begin

definition send:: "'a \<Rightarrow>('a, unit, 'b) c_monad"
where
  "send x \<equiv>
      modify (\<lambda>s. s\<lparr>State:=concat (State s) x, Transcript:=x # (Transcript s)\<rparr>)"

definition send2::"'a \<Rightarrow>('a, unit, 'b) c_monad"
where
  "send2 x \<equiv>
      modify (\<lambda>s. s\<lparr>Transcript:=x # (Transcript s)\<rparr>)"

text \<open>
  The idea is that read recovers the state of write
\<close>
definition read :: "('a, 'a, 'b) c_monad"
where
  "read \<equiv>
    do {
      s \<leftarrow> get;
      assert (Transcript s \<noteq> []);
      modify (\<lambda>s. s\<lparr>State:=concat (State s) (hd (Transcript s)), Transcript:=tl (Transcript s)\<rparr>);
      return (hd (Transcript s))
    }"

lemma send_outcome:
  assumes "Some ((), t) \<in> set_dist (execute (send x) s)"
  shows "t = s\<lparr>State := concat (State s) x, Transcript := x # Transcript s\<rparr>"
  using assms
  unfolding send_def modify_def
  by (auto elim!: set_dist_bindE)

lemma read_cons_outcome:
  assumes "Some (y, t) \<in> set_dist (execute read (s\<lparr>Transcript := x # xs\<rparr>))"
  shows
    "y = x \<and>
     t = s\<lparr>State := concat (State s) x, Transcript := xs\<rparr>"
  using assms
  unfolding read_def modify_def assert_def
  by (auto elim!: set_dist_bindE)

lemma read_nonempty_outcome:
  assumes out: "Some (y, t) \<in> set_dist (execute read s)"
    and tr: "Transcript s = x # xs"
  shows
    "y = x \<and>
     t = s\<lparr>State := concat (State s) x, Transcript := xs\<rparr>"
proof -
  have s_eq: "s\<lparr>Transcript := x # xs\<rparr> = s"
    using tr by (cases s) simp
  have out': "Some (y, t) \<in>
    set_dist (execute read (s\<lparr>Transcript := x # xs\<rparr>))"
    using out unfolding s_eq .
  show ?thesis
    using read_cons_outcome[OF out'] tr by simp
qed

lemma read_no_failure:
  assumes "Transcript s \<noteq> []"
  shows "None \<notin> dom (dist (execute read s))"
  using assms
  unfolding read_def assert_def
  by (intro no_failure_bindI) simp_all

lemma hash_no_failure:
  "None \<notin> dom (dist (execute (hash x) s))"
  unfolding hash_def apply_hash_def modify_HashMap_def
  by (intro no_failure_bindI) simp_all

lemma receive_random_field_element_no_failure:
  "None \<notin> dom (dist (execute receive_random_field_element s))"
  unfolding receive_random_field_element_def
  by (intro no_failure_bindI) (simp_all add: hash_no_failure)

lemma receive_random_field_element_extends:
  assumes "Some (r, t) \<in> set_dist (execute receive_random_field_element s)"
  shows "s \<le> t"
proof -
  from assms obtain s0 where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and rest:
      "Some (r, t) \<in>
        set_dist (execute (hash (State s0) \<bind> return) s0)"
    unfolding receive_random_field_element_def
    by (auto elim!: set_dist_bindE)
  have s0: "s0 = s"
    using get_s by simp
  have hash_out:
    "Some (r, t) \<in> set_dist (execute (hash (State s)) s)"
    using rest unfolding s0 by simp
  show ?thesis
    using hash_outcome(1)[OF hash_out] .
qed

lemma hash_channel_preserves:
  assumes "Some (h, t) \<in> set_dist (execute (hash x) s)"
  shows "State t = State s"
    and "Transcript t = Transcript s"
proof -
  from assms obtain a s1 where
    a: "Some (a, s1) \<in> set_dist (execute (apply_hash x) s)"
    and rest: "Some (h, t) \<in>
      set_dist (execute (modify_HashMap x a \<bind> (\<lambda>_. return a)) s1)"
  proof -
    have "Some (h, t) \<in>
      set_dist (execute
        (apply_hash x \<bind> (\<lambda>a. modify_HashMap x a \<bind> (\<lambda>_. return a))) s)"
      using assms unfolding hash_def .
    then show ?thesis
      by (rule set_dist_bindE) (rule that)
  qed
  have a_img: "Some (a, s1) \<in> (\<lambda>a. Some (a, s)) ` set_dist (hash_dist x s)"
    using a
    unfolding apply_hash_def lift.rep_eq lift_dist_def
    by (simp add: set_dist_dist_map)
  then have s1: "s1 = s"
    by auto
  from rest obtain u s2 where
    mod: "Some (u, s2) \<in> set_dist (execute (modify_HashMap x a) s1)"
    and ret: "Some (h, t) \<in> set_dist (execute (return a) s2)"
    by (elim set_dist_bindE)
  from mod have s2: "s2 = s1\<lparr>HashMap := fmupd x a (HashMap s1)\<rparr>"
    unfolding modify_HashMap_def modify_def
    by (auto elim!: set_dist_bindE)
  from ret have t: "t = s2"
    by auto
  show "State t = State s"
    unfolding t s2 s1 by simp
  show "Transcript t = Transcript s"
    unfolding t s2 s1 by simp
qed

lemma receive_random_field_element_known_outcome:
  assumes lookup: "fmlookup (HashMap s) (State s) = Some r"
    and outcome: "Some (r', t) \<in> set_dist (execute receive_random_field_element s)"
  shows
    "r' = r \<and> State t = State s \<and> Transcript t = Transcript s \<and> s \<le> t"
proof -
  from outcome obtain s0 where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and rest:
      "Some (r', t) \<in>
        set_dist (execute (hash (State s0) \<bind> return) s0)"
    unfolding receive_random_field_element_def
    by (auto elim!: set_dist_bindE)
  have s0: "s0 = s"
    using get_s by simp
  have hash_out:
    "Some (r', t) \<in> set_dist (execute (hash (State s)) s)"
    using rest unfolding s0 by simp
  have ext: "s \<le> t"
    using hash_outcome(1)[OF hash_out] .
  have lookup_r': "fmlookup (HashMap t) (State s) = Some r'"
    using hash_outcome(2)[OF hash_out] .
  have lookup_r: "fmlookup (HashMap t) (State s) = Some r"
    using hash_extension_lookup[OF lookup ext] .
  moreover have "State t = State s \<and> Transcript t = Transcript s"
    using hash_channel_preserves[OF hash_out] by simp
  ultimately show ?thesis
    using ext lookup_r' by auto
qed

lemma random_then_read_cons_outcome:
  assumes lookup: "fmlookup (HashMap s) (State s) = Some x"
    and outcome:
      "Some ((r, y), t) \<in>
        set_dist (execute
          (do {
            r \<leftarrow> receive_random_field_element;
            y \<leftarrow> read;
            return (r, y)
          }) (s\<lparr>Transcript := x # xs\<rparr>))"
  shows
    "r = x \<and>
     y = x \<and>
     State t = concat (State s) x \<and>
     Transcript t = xs"
proof -
  let ?s = "s\<lparr>Transcript := x # xs\<rparr>"
  have outcome':
    "Some ((r, y), t) \<in>
      set_dist (execute
        (receive_random_field_element \<bind>
          (\<lambda>r. read \<bind> (\<lambda>y. return (r, y)))) ?s)"
    using outcome by simp
  from outcome' obtain r_state where
    rand:
      "Some (r, r_state) \<in> set_dist (execute receive_random_field_element ?s)"
    and read_y:
      "Some (y, t) \<in> set_dist (execute read r_state)"
    by (auto elim!: set_dist_bindE)
  have lookup': "fmlookup (HashMap ?s) (State ?s) = Some x"
    using lookup by simp
  have rand_res:
    "r = x \<and> State r_state = State s \<and> Transcript r_state = x # xs"
    using receive_random_field_element_known_outcome[OF lookup' rand] by simp
  have r_state_update: "r_state\<lparr>Transcript := x # xs\<rparr> = r_state"
    using rand_res by simp
  have read_y':
    "Some (y, t) \<in> set_dist (execute read (r_state\<lparr>Transcript := x # xs\<rparr>))"
    using read_y unfolding r_state_update .
  have read_res:
    "y = x \<and> State t = concat (State s) x \<and> Transcript t = xs"
    using read_cons_outcome[OF read_y'] rand_res by simp
  show ?thesis
    using rand_res read_res by simp
qed

lemma random_then_read_assert_no_failure:
  assumes lookup: "fmlookup (HashMap s) (State s) = Some x"
  shows
    "None \<notin> dom (dist (execute
      (do {
        r \<leftarrow> receive_random_field_element;
        y \<leftarrow> read;
        assert (r = y);
        return y
      }) (s\<lparr>Transcript := x # xs\<rparr>)))"
proof -
  let ?s = "s\<lparr>Transcript := x # xs\<rparr>"
  let ?prefix =
    "do {
      r \<leftarrow> receive_random_field_element;
      y \<leftarrow> read;
      return (r, y)
    }"
  have prefix_no_failure:
    "None \<notin> dom (dist (execute ?prefix ?s))"
  proof (rule no_failure_bindI)
    show "None \<notin> dom (dist (execute receive_random_field_element ?s))"
      by (rule receive_random_field_element_no_failure)
    fix r t
    assume rand: "Some (r, t) \<in> set_dist (execute receive_random_field_element ?s)"
    have lookup_s: "fmlookup (HashMap ?s) (State ?s) = Some x"
      using lookup by simp
    have tr_t: "Transcript t = x # xs"
      using receive_random_field_element_known_outcome[OF lookup_s rand] by simp
    show "None \<notin> dom (dist (execute (read \<bind> (\<lambda>y. return (r, y))) t))"
    proof (rule no_failure_bindI)
      show "None \<notin> dom (dist (execute read t))"
        by (rule read_no_failure) (simp add: tr_t)
      fix y u
      assume "Some (y, u) \<in> set_dist (execute read t)"
      show "None \<notin> dom (dist (execute (return (r, y)) u))"
        by simp
    qed
  qed
  have full:
    "do {
      r \<leftarrow> receive_random_field_element;
      y \<leftarrow> read;
      assert (r = y);
      return y
    } =
    (?prefix \<bind> (\<lambda>(r, y). assert (r = y) \<bind> (\<lambda>_. return y)))"
    by (simp add: sm_bind_assoc split: prod.splits)
  show ?thesis
    unfolding full
  proof (rule no_failure_bindI[OF prefix_no_failure])
    fix ry t
    assume prefix:
      "Some (ry, t) \<in> set_dist (execute ?prefix ?s)"
    obtain r y where ry: "ry = (r, y)"
      by (cases ry)
    have replay: "r = y"
      using random_then_read_cons_outcome[OF lookup prefix[unfolded ry]] by simp
    show "None \<notin> dom
      (dist (execute ((case ry of (r, y) \<Rightarrow> assert (r = y) \<bind> (\<lambda>_. return y))) t))"
      unfolding ry replay assert_def by simp
  qed
qed

lemma read_then_random_cons_outcome:
  assumes lookup:
    "fmlookup (HashMap s) (concat (State s) x) = Some r"
    and outcome:
      "Some ((y, r'), t) \<in>
        set_dist (execute
          (do {
            y \<leftarrow> read;
            r \<leftarrow> receive_random_field_element;
            return (y, r)
          }) (s\<lparr>Transcript := x # xs\<rparr>))"
  shows
    "y = x \<and>
     r' = r \<and>
     State t = concat (State s) x \<and>
     Transcript t = xs"
proof -
  let ?s = "s\<lparr>Transcript := x # xs\<rparr>"
  have outcome':
    "Some ((y, r'), t) \<in>
      set_dist (execute
        (read \<bind>
          (\<lambda>y. receive_random_field_element \<bind> (\<lambda>r. return (y, r)))) ?s)"
    using outcome by simp
  from outcome' obtain read_state where
    read_y: "Some (y, read_state) \<in> set_dist (execute read ?s)"
    and rand:
      "Some (r', t) \<in> set_dist (execute receive_random_field_element read_state)"
    by (auto elim!: set_dist_bindE)
  have read_res:
    "y = x \<and>
     read_state = s\<lparr>State := concat (State s) x, Transcript := xs\<rparr>"
    using read_cons_outcome[OF read_y] by simp
  have rand_res:
    "r' = r \<and>
     State t = concat (State s) x \<and>
     Transcript t = xs"
    using receive_random_field_element_known_outcome[OF _ rand] lookup read_res by simp
  show ?thesis
    using read_res rand_res by simp
qed

lemma mfold2_send_outcome:
  assumes "Some ((), t) \<in> set_dist (execute (mfold2 send xs) s)"
  shows
    "t =
      s\<lparr>
        State := foldl concat (State s) xs,
        Transcript := rev xs @ Transcript s
      \<rparr>"
  using assms
proof (induction xs arbitrary: s t)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems obtain s1 where
    send_x: "Some ((), s1) \<in> set_dist (execute (send x) s)"
    and rest: "Some ((), t) \<in> set_dist (execute (mfold2 send xs) s1)"
    by (auto elim!: set_dist_bindE)
  have s1:
    "s1 = s\<lparr>State := concat (State s) x, Transcript := x # Transcript s\<rparr>"
    using send_outcome[OF send_x] .
  show ?case
    using Cons.IH[OF rest] unfolding s1 by simp
qed

lemma ntimes_read_outcome:
  assumes "Some (ys, t) \<in> set_dist (execute (ntimes read (length xs)) (s\<lparr>Transcript := xs\<rparr>))"
  shows
    "ys = xs \<and>
     t = s\<lparr>State := foldl concat (State s) xs, Transcript := []\<rparr>"
  using assms
proof (induction xs arbitrary: s ys t)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have prems':
    "Some (ys, t) \<in>
      set_dist (execute
        (read \<bind> (\<lambda>y. ntimes read (length xs) \<bind> (\<lambda>ys. return (y # ys))))
        (s\<lparr>Transcript := x # xs\<rparr>))"
    using Cons.prems by simp
  from prems' obtain y s1 where
    read_x: "Some (y, s1) \<in> set_dist (execute read (s\<lparr>Transcript := x # xs\<rparr>))"
    and rest1:
      "Some (ys, t) \<in>
        set_dist (execute (ntimes read (length xs) \<bind> (\<lambda>ys. return (y # ys))) s1)"
    by (rule set_dist_bindE) blast
  from rest1 obtain ys' s2 where
    reads: "Some (ys', s2) \<in> set_dist (execute (ntimes read (length xs)) s1)"
    and ret: "Some (ys, t) \<in> set_dist (execute (return (y # ys')) s2)"
    by (auto elim!: set_dist_bindE)
  have read_res:
    "y = x \<and> s1 = s\<lparr>State := concat (State s) x, Transcript := xs\<rparr>"
    using read_cons_outcome[OF read_x] .
  let ?s0 = "s\<lparr>State := concat (State s) x\<rparr>"
  have s1: "s1 = ?s0\<lparr>Transcript := xs\<rparr>"
    using read_res by simp
  have tail:
    "ys' = xs \<and>
     s2 = ?s0\<lparr>State := foldl concat (State ?s0) xs, Transcript := []\<rparr>"
    using Cons.IH[OF reads[unfolded s1]] .
  have ys_t: "ys = y # ys' \<and> t = s2"
    using ret by simp
  show ?case
    using read_res tail ys_t by simp
qed

lemma ntimes_read_prefix_outcome:
  assumes "Some (ys, t) \<in>
    set_dist (execute (ntimes read (length xs)) (s\<lparr>Transcript := xs @ rest\<rparr>))"
  shows
    "ys = xs \<and>
     t = s\<lparr>State := foldl concat (State s) xs, Transcript := rest\<rparr>"
  using assms
proof (induction xs arbitrary: s ys t)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have prems':
    "Some (ys, t) \<in>
      set_dist (execute
        (read \<bind> (\<lambda>y. ntimes read (length xs) \<bind> (\<lambda>ys. return (y # ys))))
        (s\<lparr>Transcript := x # xs @ rest\<rparr>))"
    using Cons.prems by simp
  from prems' obtain y s1 where
    read_x: "Some (y, s1) \<in> set_dist (execute read (s\<lparr>Transcript := x # xs @ rest\<rparr>))"
    and rest1:
      "Some (ys, t) \<in>
        set_dist (execute (ntimes read (length xs) \<bind> (\<lambda>ys. return (y # ys))) s1)"
    by (rule set_dist_bindE) blast
  from rest1 obtain ys' s2 where
    reads: "Some (ys', s2) \<in> set_dist (execute (ntimes read (length xs)) s1)"
    and ret: "Some (ys, t) \<in> set_dist (execute (return (y # ys')) s2)"
    by (auto elim!: set_dist_bindE)
  have read_res:
    "y = x \<and> s1 = s\<lparr>State := concat (State s) x, Transcript := xs @ rest\<rparr>"
    using read_cons_outcome[OF read_x] .
  let ?s0 = "s\<lparr>State := concat (State s) x\<rparr>"
  have s1: "s1 = ?s0\<lparr>Transcript := xs @ rest\<rparr>"
    using read_res by simp
  have tail:
    "ys' = xs \<and>
     s2 = ?s0\<lparr>State := foldl concat (State ?s0) xs, Transcript := rest\<rparr>"
    using Cons.IH[OF reads[unfolded s1]] .
  have ys_t: "ys = y # ys' \<and> t = s2"
    using ret by simp
  show ?case
    using read_res tail ys_t by simp
qed

theorem honest_transcript_replay_mfold2_ntimes:
  assumes init: "Transcript s = []"
    and sent: "Some ((), sent) \<in> set_dist (execute (mfold2 send xs) s)"
    and replay:
      "Some (ys, replayed) \<in>
        set_dist (execute
          (ntimes read (length xs))
          (sent\<lparr>State := State s, Transcript := rev (Transcript sent)\<rparr>))"
  shows "ys = xs \<and> replayed = sent\<lparr>Transcript := []\<rparr>"
proof -
  have sent_eq:
    "sent =
      s\<lparr>
        State := foldl concat (State s) xs,
        Transcript := rev xs
      \<rparr>"
    using mfold2_send_outcome[OF sent] init by simp
  let ?replay_start = "sent\<lparr>State := State s\<rparr>"
  have start_eq:
    "sent\<lparr>State := State s, Transcript := rev (Transcript sent)\<rparr> =
      ?replay_start\<lparr>Transcript := xs\<rparr>"
    using sent_eq by simp
  have replay_out:
    "ys = xs \<and>
     replayed =
      ?replay_start\<lparr>
        State := foldl concat (State ?replay_start) xs,
        Transcript := []
      \<rparr>"
    using ntimes_read_outcome[OF replay[unfolded start_eq]] .
  then show ?thesis
    using sent_eq by simp
qed

lemma ntimes_read_no_failure:
  assumes "n \<le> length (Transcript s)"
  shows "None \<notin> dom (dist (execute (ntimes read n) s))"
  using assms
proof (induction n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have nonempty: "Transcript s \<noteq> []"
    using Suc.prems by (cases "Transcript s") auto
  have nf_read: "None \<notin> dom (dist (execute read s))"
    by (rule read_no_failure[OF nonempty])
  have nf_cont:
    "\<And>x t. Some (x, t) \<in> set_dist (execute read s) \<Longrightarrow>
      None \<notin> dom
        (dist (execute
          (ntimes read n \<bind> (\<lambda>xs. return (x # xs))) t))"
  proof -
    fix x t
    assume out: "Some (x, t) \<in> set_dist (execute read s)"
    obtain y ys where tr: "Transcript s = y # ys"
      using nonempty by (cases "Transcript s") auto
    have t_eq: "t = s\<lparr>State := concat (State s) y, Transcript := ys\<rparr>"
      using read_nonempty_outcome[OF out tr] by simp
    have "n \<le> length ys"
      using Suc.prems tr by simp
    then have nf_tail: "None \<notin> dom (dist (execute (ntimes read n) t))"
      using Suc.IH[of t] unfolding t_eq by simp
    show "None \<notin> dom
      (dist (execute
        (ntimes read n \<bind> (\<lambda>xs. return (x # xs))) t))"
      by (rule no_failure_bindI[OF nf_tail]) simp
  qed
  show ?case
    by (simp add: no_failure_bindI[OF nf_read nf_cont])
qed

lemma check_authentication_path_no_failure:
  "None \<notin> dom (dist (execute (check_authentication_path len i v path) s))"
proof (induction path arbitrary: len i v s)
  case Nil
  then show ?case
    by (simp add: hash_no_failure)
next
  case (Cons a path)
  show ?case
  proof (cases "i < len div 2")
    case True
    then show ?thesis
      by (simp add: no_failure_bindI hash_no_failure Cons.IH)
  next
    case False
    then show ?thesis
      by (simp add: no_failure_bindI hash_no_failure Cons.IH)
  qed
qed

lemma check_authentication_path_preserves_channel:
  assumes "Some (h, t) \<in> set_dist (execute (check_authentication_path len i v path) s)"
  shows "State t = State s"
    and "Transcript t = Transcript s"
proof -
  have both:
    "State t = State s \<and> Transcript t = Transcript s"
    if outcome:
      "Some (h, t) \<in> set_dist (execute (check_authentication_path len i v path) s)"
    for len i v s h t
    using outcome
  proof (induction path arbitrary: len i v s h t)
    case Nil
    have hash_step: "Some (h, t) \<in> set_dist (execute (hash v) s)"
      using Nil.prems by simp
    show ?case
      using hash_channel_preserves(1)[OF hash_step]
        hash_channel_preserves(2)[OF hash_step]
      by simp
  next
    case (Cons a path)
    show ?case
    proof (cases "i < len div 2")
      case True
      from Cons.prems obtain x s1 where
        rest:
          "Some (x, s1) \<in>
            set_dist (execute (check_authentication_path (len div 2) i v path) s)"
        and hash_step: "Some (h, t) \<in> set_dist (execute (hash (concat x a)) s1)"
        using True by (auto elim!: set_dist_bindE)
      have rec: "State s1 = State s \<and> Transcript s1 = Transcript s"
        using Cons.IH[OF rest] .
      have hash_pres: "State t = State s1 \<and> Transcript t = Transcript s1"
        using hash_channel_preserves(1)[OF hash_step]
          hash_channel_preserves(2)[OF hash_step]
        by simp
      show ?thesis
        using rec hash_pres by simp
    next
      case False
      from Cons.prems obtain x s1 where
        rest:
          "Some (x, s1) \<in>
            set_dist (execute (check_authentication_path (len div 2) (i - len div 2) v path) s)"
        and hash_step: "Some (h, t) \<in> set_dist (execute (hash (concat a x)) s1)"
        using False by (auto elim!: set_dist_bindE)
      have rec: "State s1 = State s \<and> Transcript s1 = Transcript s"
        using Cons.IH[OF rest] .
      have hash_pres: "State t = State s1 \<and> Transcript t = Transcript s1"
        using hash_channel_preserves(1)[OF hash_step]
          hash_channel_preserves(2)[OF hash_step]
        by simp
      show ?thesis
        using rec hash_pres by simp
    qed
  qed
  show "State t = State s"
    using both[OF assms] by simp
  show "Transcript t = Transcript s"
    using both[OF assms] by simp
qed

lemma honest_query_decommitment_no_failure:
  assumes created: "created_tree xs tree s0"
    and len_pow: "length xs = 2 ^ n"
    and idx: "i < length xs"
    and leaf: "v = xs ! i"
    and ext: "s0 \<le> s"
    and path_len: "length (get_authentication_path (length xs) i tree) = floor_log (length xs)"
    and root: "fr = value tree"
  shows
    "None \<notin> dom (dist (execute
      (do {
        qh \<leftarrow> read;
        qh_path \<leftarrow> ntimes read (floor_log (length xs));
        ap \<leftarrow> check_authentication_path (length xs) i qh qh_path;
        assert (ap = fr);
        return qh
      }) (s\<lparr>Transcript := v # get_authentication_path (length xs) i tree @ rest\<rparr>)))"
proof -
  let ?path = "get_authentication_path (length xs) i tree"
  let ?s = "s\<lparr>Transcript := v # ?path @ rest\<rparr>"
  let ?prefix =
    "do {
      qh \<leftarrow> read;
      qh_path \<leftarrow> ntimes read (floor_log (length xs));
      ap \<leftarrow> check_authentication_path (length xs) i qh qh_path;
      return (qh, qh_path, ap)
    }"
  have nf_read: "None \<notin> dom (dist (execute read ?s))"
    by (rule read_no_failure) simp
  have nf_after_read:
    "\<And>qh s1. Some (qh, s1) \<in> set_dist (execute read ?s) \<Longrightarrow>
      None \<notin> dom
        (dist (execute
          (ntimes read (floor_log (length xs)) \<bind>
            (\<lambda>qh_path. check_authentication_path (length xs) i qh qh_path \<bind>
              (\<lambda>ap. return (qh, qh_path, ap)))) s1))"
  proof -
    fix qh s1
    assume read_qh: "Some (qh, s1) \<in> set_dist (execute read ?s)"
    have read_qh_res:
      "s1 = s\<lparr>State := concat (State s) v, Transcript := ?path @ rest\<rparr>"
      using read_cons_outcome[OF read_qh] by simp
    have enough_path: "floor_log (length xs) \<le> length (Transcript s1)"
      using path_len unfolding read_qh_res by simp
    have nf_reads:
      "None \<notin> dom (dist (execute (ntimes read (floor_log (length xs))) s1))"
      by (rule ntimes_read_no_failure[OF enough_path])
    have nf_after_reads:
      "\<And>qh_path s2. Some (qh_path, s2) \<in>
        set_dist (execute (ntimes read (floor_log (length xs))) s1) \<Longrightarrow>
        None \<notin> dom
          (dist (execute
            (check_authentication_path (length xs) i qh qh_path \<bind>
              (\<lambda>ap. return (qh, qh_path, ap))) s2))"
    proof -
      fix qh_path s2
      assume "Some (qh_path, s2) \<in>
        set_dist (execute (ntimes read (floor_log (length xs))) s1)"
      have nf_check:
        "None \<notin> dom
          (dist (execute (check_authentication_path (length xs) i qh qh_path) s2))"
        by (rule check_authentication_path_no_failure)
	      show "None \<notin> dom
	        (dist (execute
	          (check_authentication_path (length xs) i qh qh_path \<bind>
	            (\<lambda>ap. return (qh, qh_path, ap))) s2))"
	      proof (rule no_failure_bindI[OF nf_check])
	        fix ap t
	        assume "Some (ap, t) \<in>
	          set_dist (execute (check_authentication_path (length xs) i qh qh_path) s2)"
	        show "None \<notin> dom (dist (execute (return (qh, qh_path, ap)) t))"
	          by simp
	      qed
    qed
    show "None \<notin> dom
      (dist (execute
        (ntimes read (floor_log (length xs)) \<bind>
          (\<lambda>qh_path. check_authentication_path (length xs) i qh qh_path \<bind>
            (\<lambda>ap. return (qh, qh_path, ap)))) s1))"
      using no_failure_bindI[OF nf_reads nf_after_reads] .
  qed
  have prefix_no_failure: "None \<notin> dom (dist (execute ?prefix ?s))"
    using no_failure_bindI[OF nf_read nf_after_read] .
  have full:
    "do {
      qh \<leftarrow> read;
      qh_path \<leftarrow> ntimes read (floor_log (length xs));
      ap \<leftarrow> check_authentication_path (length xs) i qh qh_path;
      assert (ap = fr);
      return qh
    } =
    (?prefix \<bind> (\<lambda>(qh, qh_path, ap). assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
    by (simp add: sm_bind_assoc split: prod.splits)
  show ?thesis
    unfolding full
  proof (rule no_failure_bindI[OF prefix_no_failure])
    fix out t
    assume out:
      "Some (out, t) \<in> set_dist (execute ?prefix ?s)"
    obtain qh qh_path ap where out_eq: "out = (qh, qh_path, ap)"
      by (cases out) auto
    from out[unfolded out_eq] obtain s1 s2 where
      read_leaf: "Some (qh, s1) \<in> set_dist (execute read ?s)"
      and read_path:
        "Some (qh_path, s2) \<in>
          set_dist (execute (ntimes read (floor_log (length xs))) s1)"
      and check:
        "Some (ap, t) \<in>
          set_dist (execute
            (check_authentication_path (length xs) i qh qh_path) s2)"
      by (auto elim!: set_dist_bindE)
    have read_leaf_res:
      "qh = v \<and>
       s1 = s\<lparr>State := concat (State s) v, Transcript := ?path @ rest\<rparr>"
      using read_cons_outcome[OF read_leaf] by simp
    let ?s_leaf = "s\<lparr>State := concat (State s) v\<rparr>"
    have s1_eq: "s1 = ?s_leaf\<lparr>Transcript := ?path @ rest\<rparr>"
      using read_leaf_res by simp
    have path_replay:
      "qh_path = ?path \<and>
       s2 = ?s_leaf\<lparr>
         State := foldl concat (State ?s_leaf) ?path,
         Transcript := rest\<rparr>"
      using ntimes_read_prefix_outcome[OF read_path[unfolded path_len[symmetric] s1_eq]]
      by simp
    have s0_s2: "s0 \<le> s2"
      using ext read_leaf_res path_replay
      unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    have check_honest:
      "Some (ap, t) \<in>
        set_dist (execute
          (check_authentication_path (length xs) i v ?path) s2)"
      using check read_leaf_res path_replay by simp
    have ap_eq: "ap = value tree"
      using check_created_tree_outcome[
        OF created len_pow idx leaf s0_s2 check_honest]
      by simp
    then show "None \<notin> dom
      (dist (execute
        ((case out of (qh, qh_path, ap) \<Rightarrow> assert (ap = fr) \<bind> (\<lambda>_. return qh))) t))"
      unfolding out_eq root assert_def by simp
  qed
qed

end

end
