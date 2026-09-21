(*  Title:      Stark/Channel_Core.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Channel_Core
  imports Hash_Monad Merkle_Tree
begin

section \<open>Channels\<close>

lemma no_failure_bindI:
  assumes m_no_fail: "None \<notin> dom (dist (execute m s))"
    and k_no_fail:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        None \<notin> dom (dist (execute (k x) t))"
  shows "None \<notin> dom (dist (execute (m \<bind> k) s))"
proof
  assume "None \<in> dom (dist (execute (m \<bind> k) s))"
  then have none:
    "None \<in> dom
      (map_bind (dist \<circ> execute m)
        (bind_cont_map (map_fun id dist \<circ> execute \<circ> k)) s)"
    unfolding sm_bind.rep_eq dist_bind.rep_eq
    by (simp add: o_def map_fun_def)
  then have
    "None \<in>
      (\<Union>i\<in>dom (dist (execute m s)).
        dom (bind_cont_map (map_fun id dist \<circ> execute \<circ> k) i))"
    using dom_map_bind[of "dist \<circ> execute m"
        "bind_cont_map (map_fun id dist \<circ> execute \<circ> k)" s]
    by (simp add: o_def)
  then obtain i where
    i_dom: "i \<in> dom (dist (execute m s))"
    and none_i:
      "None \<in> dom (bind_cont_map (map_fun id dist \<circ> execute \<circ> k) i)"
    by auto
  show False
  proof (cases i)
    case None
    then show ?thesis
      using i_dom m_no_fail by simp
  next
    case (Some xt)
    then obtain x t where xt: "i = Some (x, t)"
      by (cases xt) auto
    have i_set: "Some (x, t) \<in> set_dist (execute m s)"
      using i_dom unfolding xt set_dist_def .
    have "None \<notin> dom (dist (execute (k x) t))"
      by (rule k_no_fail[OF i_set])
    moreover have
      "dom (bind_cont_map (map_fun id dist \<circ> execute \<circ> k) (Some (x, t))) =
        dom (dist (execute (k x) t))"
      unfolding bind_cont_map_def by simp
    ultimately show ?thesis
      using none_i unfolding xt by simp
  qed
qed

lemma no_failure_return[simp]:
  "None \<notin> dom (dist (execute (return x) s))"
  unfolding return.rep_eq dist_return_def dist_delta_dist delta_map_def
  by simp

lemma no_failure_get[simp]:
  "None \<notin> dom (dist (execute get s))"
  unfolding get.rep_eq dist_get_def dist_delta_dist delta_map_def
  by simp

lemma no_failure_put[simp]:
  "None \<notin> dom (dist (execute (put s') s))"
  unfolding put.rep_eq dist_put_def dist_delta_dist delta_map_def
  by simp

lemma no_failure_lift[simp]:
  "None \<notin> dom (dist (execute (lift d) s))"
  unfolding lift.rep_eq lift_dist_def set_dist_def
  using set_dist_dist_map[of "\<lambda>a. Some (a, s)" "d s"]
  unfolding set_dist_def by auto

lemma no_failure_modify[simp]:
  "None \<notin> dom (dist (execute (modify f) s))"
  unfolding modify_def
  by (rule no_failure_bindI) simp_all

lemma throw_no_Some_set_dist:
  "Some x \<notin> set_dist (execute (throw :: ('a, 's) state_monad) s)"
  unfolding set_dist_def throw.rep_eq dist_throw_def dist_delta_dist
    delta_map_def
  by simp

record 'a channel = "('a, 'a) hash" +
  State :: 'a
  Transcript :: "'a list"

type_synonym ('a, 'b, 'c) c_monad = "('b, ('a, 'c) channel_scheme) state_monad"

definition receive_random_field_element :: "('a, 'a::finite, 'b) c_monad"
where
  "receive_random_field_element \<equiv>
    do {
      s \<leftarrow> get;
      r \<leftarrow> hash (State s);
      return r
    }"

record 'a protocol_channel = "('a protocol_hash_input, 'a) hash" +
  PState :: 'a
  PTranscript :: "'a list"
  PTraceFriCounter :: nat
  PCompositionFriCounter :: nat
  PAlphaCounter :: nat
  PQueryCounter :: nat

type_synonym ('a, 'b, 'c) protocol_c_monad =
  "('b, ('a, 'c) protocol_channel_scheme) state_monad"

definition protocol_receive_tagged_random_field_element
  :: "('a \<Rightarrow> 'a protocol_hash_input) \<Rightarrow>
      ('a, 'a::finite, 'b) protocol_c_monad"
where
  "protocol_receive_tagged_random_field_element tag \<equiv>
    do {
      s \<leftarrow> get;
      r \<leftarrow> hash (tag (PState s));
      return r
    }"

definition protocol_receive_random_field_element
  :: "('a, 'a::finite, 'b) protocol_c_monad"
where
  "protocol_receive_random_field_element \<equiv>
    protocol_receive_tagged_random_field_element FiatShamirChallenge"

definition protocol_receive_counted_tagged_random_field_element
  :: "((('a, 'b) protocol_channel_scheme) \<Rightarrow> nat) \<Rightarrow>
      ((('a, 'b) protocol_channel_scheme) \<Rightarrow> ('a, 'b) protocol_channel_scheme) \<Rightarrow>
      (nat \<Rightarrow> 'a \<Rightarrow> 'a protocol_hash_input) \<Rightarrow>
      ('a, 'a::finite, 'b) protocol_c_monad"
where
  "protocol_receive_counted_tagged_random_field_element counter bump tag \<equiv>
    do {
      s \<leftarrow> get;
      r \<leftarrow> hash (tag (counter s) (PState s));
      modify bump;
      return r
    }"

definition protocol_send
  :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow>
      ('a, unit, 'b) protocol_c_monad"
where
  "protocol_send absorb x \<equiv>
    modify
      (\<lambda>s. s\<lparr>
        PState := absorb (PState s) x,
        PTranscript := x # PTranscript s\<rparr>)"

definition protocol_read
  :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a, 'a, 'b) protocol_c_monad"
where
  "protocol_read absorb \<equiv>
    do {
      s \<leftarrow> get;
      assert (PTranscript s \<noteq> []);
      modify
        (\<lambda>s. s\<lparr>
          PState := absorb (PState s) (hd (PTranscript s)),
          PTranscript := tl (PTranscript s)\<rparr>);
      return (hd (PTranscript s))
    }"

definition protocol_absorb_message
  :: "'a::finite \<Rightarrow> ('a, unit, 'b) protocol_c_monad"
where
  "protocol_absorb_message x \<equiv>
    do {
      s \<leftarrow> get;
      h \<leftarrow> (hash (TranscriptAbsorb (PState s) x) ::
        ('a, 'a, 'b) protocol_c_monad);
      modify
        (\<lambda>s. s\<lparr>
          PState := h,
          PTranscript := x # PTranscript s\<rparr>)
    }"

definition protocol_absorb_read
  :: "('a::finite, 'a, 'b) protocol_c_monad"
where
  "protocol_absorb_read \<equiv>
    do {
      s \<leftarrow> get;
      assert (PTranscript s \<noteq> []);
      h \<leftarrow> (hash (TranscriptAbsorb (PState s) (hd (PTranscript s))) ::
        ('a, 'a, 'b) protocol_c_monad);
      modify
        (\<lambda>s. s\<lparr>
          PState := h,
          PTranscript := tl (PTranscript s)\<rparr>);
      return (hd (PTranscript s))
    }"

lemma protocol_hash_no_failure:
  "None \<notin> dom (dist (execute (hash x) s))"
  unfolding hash_def apply_hash_def modify_HashMap_def
  by (intro no_failure_bindI) simp_all

lemma protocol_receive_tagged_random_field_element_no_failure:
  "None \<notin>
    dom (dist
      (execute (protocol_receive_tagged_random_field_element tag) s))"
  unfolding protocol_receive_tagged_random_field_element_def
  by (intro no_failure_bindI) (simp_all add: protocol_hash_no_failure)

lemma protocol_receive_random_field_element_no_failure:
  "None \<notin>
    dom (dist (execute protocol_receive_random_field_element s))"
  unfolding protocol_receive_random_field_element_def
  by (rule protocol_receive_tagged_random_field_element_no_failure)

lemma protocol_receive_counted_tagged_random_field_element_no_failure:
  "None \<notin>
    dom (dist
      (execute
        (protocol_receive_counted_tagged_random_field_element counter bump tag) s))"
  unfolding protocol_receive_counted_tagged_random_field_element_def
  by (intro no_failure_bindI) (simp_all add: protocol_hash_no_failure)

lemma protocol_absorb_message_no_failure:
  "None \<notin> dom (dist (execute (protocol_absorb_message x) s))"
  unfolding protocol_absorb_message_def
  by (intro no_failure_bindI) (simp_all add: protocol_hash_no_failure)

lemma protocol_absorb_read_no_failure:
  assumes "PTranscript s \<noteq> []"
  shows "None \<notin> dom (dist (execute protocol_absorb_read s))"
  using assms
  unfolding protocol_absorb_read_def assert_def
  by (intro no_failure_bindI) (simp_all add: protocol_hash_no_failure)

lemma protocol_send_outcome:
  assumes "Some ((), t) \<in> set_dist (execute (protocol_send absorb x) s)"
  shows
    "t = s\<lparr>
      PState := absorb (PState s) x,
      PTranscript := x # PTranscript s\<rparr>"
  using assms
  unfolding protocol_send_def modify_def
  by (auto elim!: protocol_merkle.set_dist_bindE)

lemma protocol_read_cons_outcome:
  assumes "Some (y, t) \<in>
    set_dist (execute (protocol_read absorb)
      (s\<lparr>PTranscript := x # xs\<rparr>))"
  shows
    "y = x \<and>
     t = s\<lparr>
       PState := absorb (PState s) x,
       PTranscript := xs\<rparr>"
  using assms
  unfolding protocol_read_def modify_def assert_def
  by (auto elim!: protocol_merkle.set_dist_bindE)

lemma protocol_hash_channel_preserves:
  assumes "Some (h, t) \<in> set_dist (execute (hash x) s)"
  shows "PState t = PState s"
    and "PTranscript t = PTranscript s"
    and "PTraceFriCounter t = PTraceFriCounter s"
    and "PCompositionFriCounter t = PCompositionFriCounter s"
    and "PAlphaCounter t = PAlphaCounter s"
    and "PQueryCounter t = PQueryCounter s"
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
      by (rule protocol_merkle.set_dist_bindE) (rule that)
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
    by (elim protocol_merkle.set_dist_bindE)
  from mod have s2: "s2 = s1\<lparr>HashMap := fmupd x a (HashMap s1)\<rparr>"
    unfolding modify_HashMap_def modify_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  from ret have t: "t = s2"
    by auto
  show "PState t = PState s"
    unfolding t s2 s1 by simp
  show "PTranscript t = PTranscript s"
    unfolding t s2 s1 by simp
  show "PTraceFriCounter t = PTraceFriCounter s"
    unfolding t s2 s1 by simp
  show "PCompositionFriCounter t = PCompositionFriCounter s"
    unfolding t s2 s1 by simp
  show "PAlphaCounter t = PAlphaCounter s"
    unfolding t s2 s1 by simp
  show "PQueryCounter t = PQueryCounter s"
    unfolding t s2 s1 by simp
qed

lemma protocol_absorb_message_outcome:
  assumes "Some ((), t) \<in> set_dist (execute (protocol_absorb_message x) s)"
  obtains h u where
    "Some (h, u) \<in>
      set_dist (execute (hash (TranscriptAbsorb (PState s) x)) s)"
    "t = u\<lparr>PState := h, PTranscript := x # PTranscript u\<rparr>"
    "PState u = PState s"
    "PTranscript u = PTranscript s"
    "s \<le> u"
proof -
  from assms obtain h u where hash_out:
      "Some (h, u) \<in>
        set_dist (execute (hash (TranscriptAbsorb (PState s) x)) s)"
    and mod_out:
      "Some ((), t) \<in>
        set_dist
          (execute
            (modify
              (\<lambda>s. s\<lparr>PState := h,
                PTranscript := x # PTranscript s\<rparr>)) u)"
    unfolding protocol_absorb_message_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have t_eq:
    "t = u\<lparr>PState := h, PTranscript := x # PTranscript u\<rparr>"
    using mod_out unfolding modify_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have fields:
    "PState u = PState s"
    "PTranscript u = PTranscript s"
    using protocol_hash_channel_preserves(1,2)[OF hash_out] by simp_all
  have ext: "s \<le> u"
    using protocol_merkle.hash_outcome(1)[OF hash_out] .
  show ?thesis
    by (rule that[OF hash_out t_eq fields ext])
qed

lemma protocol_absorb_read_cons_outcome:
  assumes "Some (y, t) \<in>
    set_dist (execute protocol_absorb_read (s\<lparr>PTranscript := x # xs\<rparr>))"
  obtains h u where
    "y = x"
    "Some (h, u) \<in>
      set_dist
        (execute (hash (TranscriptAbsorb (PState s) x))
          (s\<lparr>PTranscript := x # xs\<rparr>))"
    "t = u\<lparr>PState := h, PTranscript := xs\<rparr>"
    "PState u = PState s"
    "PTranscript u = x # xs"
    "s\<lparr>PTranscript := x # xs\<rparr> \<le> u"
proof -
  let ?s = "s\<lparr>PTranscript := x # xs\<rparr>"
  from assms obtain h u where y_eq: "y = x"
    and hash_out:
      "Some (h, u) \<in>
        set_dist (execute (hash (TranscriptAbsorb (PState s) x)) ?s)"
    and mod_out:
      "Some ((), t) \<in>
        set_dist
          (execute
            (modify
              (\<lambda>s. s\<lparr>PState := h,
                PTranscript := tl (PTranscript s)\<rparr>)) u)"
    unfolding protocol_absorb_read_def assert_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have tr_u: "PTranscript u = x # xs"
    using protocol_hash_channel_preserves(2)[OF hash_out] by simp
  have st_u: "PState u = PState s"
    using protocol_hash_channel_preserves(1)[OF hash_out] by simp
  have t_eq: "t = u\<lparr>PState := h, PTranscript := xs\<rparr>"
    using mod_out tr_u unfolding modify_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have ext: "?s \<le> u"
    using protocol_merkle.hash_outcome(1)[OF hash_out] .
  show ?thesis
    by (rule that[OF y_eq hash_out t_eq st_u tr_u ext])
qed

lemma protocol_hash_preserves_other_lookup:
  assumes outcome: "Some (h, t) \<in> set_dist (execute (hash x) s)"
    and neq: "y \<noteq> x"
  shows "fmlookup (HashMap t) y = fmlookup (HashMap s) y"
proof -
  from outcome obtain a s1 where
    a: "Some (a, s1) \<in> set_dist (execute (apply_hash x) s)"
    and rest: "Some (h, t) \<in>
      set_dist (execute (modify_HashMap x a \<bind> (\<lambda>_. return a)) s1)"
  proof -
    have "Some (h, t) \<in>
      set_dist (execute
        (apply_hash x \<bind> (\<lambda>a. modify_HashMap x a \<bind> (\<lambda>_. return a))) s)"
      using outcome unfolding hash_def .
    then show ?thesis
      by (rule protocol_merkle.set_dist_bindE) (rule that)
  qed
  have s1: "s1 = s"
    using a
    unfolding apply_hash_def lift.rep_eq lift_dist_def
    by (auto simp: set_dist_dist_map)
  from rest obtain u s2 where
    mod: "Some (u, s2) \<in> set_dist (execute (modify_HashMap x a) s1)"
    and ret: "Some (h, t) \<in> set_dist (execute (return a) s2)"
    by (elim protocol_merkle.set_dist_bindE)
  have s2: "s2 = s1\<lparr>HashMap := fmupd x a (HashMap s1)\<rparr>"
    using mod unfolding modify_HashMap_def modify_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have t: "t = s2"
    using ret by auto
  show ?thesis
    unfolding t s2 s1 using neq by simp
qed

lemma protocol_receive_random_field_element_outcome:
  assumes outcome:
    "Some (r, t) \<in>
      set_dist (execute protocol_receive_random_field_element s)"
  shows
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t) (FiatShamirChallenge (PState s)) = Some r"
proof -
  from outcome obtain s0 where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and rest:
      "Some (r, t) \<in>
        set_dist
          (execute (hash (FiatShamirChallenge (PState s0)) \<bind> return) s0)"
    unfolding protocol_receive_random_field_element_def
      protocol_receive_tagged_random_field_element_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have s0: "s0 = s"
    using get_s by simp
  have hash_out:
    "Some (r, t) \<in>
      set_dist (execute (hash (FiatShamirChallenge (PState s))) s)"
    using rest unfolding s0 by simp
  show ?thesis
    using protocol_merkle.hash_outcome[OF hash_out]
      protocol_hash_channel_preserves[OF hash_out]
    by simp
qed

lemma protocol_receive_tagged_random_field_element_outcome:
  assumes outcome:
    "Some (r, t) \<in>
      set_dist
        (execute (protocol_receive_tagged_random_field_element tag) s)"
  shows
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t) (tag (PState s)) = Some r"
proof -
  from outcome obtain s0 where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and rest:
      "Some (r, t) \<in>
        set_dist (execute (hash (tag (PState s0)) \<bind> return) s0)"
    unfolding protocol_receive_tagged_random_field_element_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have s0: "s0 = s"
    using get_s by simp
  have hash_out:
    "Some (r, t) \<in> set_dist (execute (hash (tag (PState s))) s)"
    using rest unfolding s0 by simp
  show ?thesis
    using protocol_merkle.hash_outcome[OF hash_out]
      protocol_hash_channel_preserves[OF hash_out]
    by simp
qed

lemma protocol_receive_tagged_random_field_element_preserves_other_lookup:
  assumes outcome:
    "Some (r, t) \<in>
      set_dist
        (execute (protocol_receive_tagged_random_field_element tag) s)"
    and neq: "y \<noteq> tag (PState s)"
  shows "fmlookup (HashMap t) y = fmlookup (HashMap s) y"
proof -
  from outcome obtain s0 where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and rest:
      "Some (r, t) \<in>
        set_dist (execute (hash (tag (PState s0)) \<bind> return) s0)"
    unfolding protocol_receive_tagged_random_field_element_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have s0: "s0 = s"
    using get_s by simp
  from rest obtain h u where
    hash_out: "Some (h, u) \<in> set_dist (execute (hash (tag (PState s))) s)"
    and ret: "Some (r, t) \<in> set_dist (execute (return h) u)"
    unfolding s0 by (elim protocol_merkle.set_dist_bindE)
  have t: "t = u" and r: "r = h"
    using ret by auto
  show ?thesis
    unfolding t
    by (rule protocol_hash_preserves_other_lookup[OF hash_out neq])
qed

lemma protocol_receive_counted_tagged_random_field_element_outcome:
  assumes outcome:
    "Some (r, t) \<in>
      set_dist
        (execute
          (protocol_receive_counted_tagged_random_field_element counter bump tag) s)"
    and bump_hash: "\<And>u. HashMap (bump u) = HashMap u"
    and bump_state: "\<And>u. PState (bump u) = PState u"
    and bump_transcript: "\<And>u. PTranscript (bump u) = PTranscript u"
  shows
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t) (tag (counter s) (PState s)) = Some r"
proof -
  from outcome obtain s0 h u v where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and hash_out:
      "Some (h, u) \<in>
        set_dist (execute (hash (tag (counter s0) (PState s0))) s0)"
    and mod:
      "Some ((), v) \<in> set_dist (execute (modify bump) u)"
    and ret: "Some (r, t) \<in> set_dist (execute (return h) v)"
    unfolding protocol_receive_counted_tagged_random_field_element_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have s0: "s0 = s"
    using get_s by simp
  have v: "v = bump u"
    using mod unfolding modify_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have t: "t = v" and r: "r = h"
    using ret by auto
  have ext_su: "s \<le> u"
    using protocol_merkle.hash_outcome[OF hash_out[unfolded s0]]
    by simp
  have lookup_u:
    "fmlookup (HashMap u) (tag (counter s) (PState s)) = Some h"
    using protocol_merkle.hash_outcome[OF hash_out[unfolded s0]]
    by simp
  have channel_u:
    "PState u = PState s \<and> PTranscript u = PTranscript s"
    using protocol_hash_channel_preserves[OF hash_out[unfolded s0]]
    by simp
  have hash_t: "HashMap t = HashMap u"
    unfolding t v by (simp add: bump_hash)
  show ?thesis
    using ext_su lookup_u channel_u
    unfolding t v r less_eq_hash_ext_def
    by (simp add: bump_hash bump_state bump_transcript)
qed

lemma protocol_receive_counted_tagged_random_field_element_preserves_other_lookup:
  assumes outcome:
    "Some (r, t) \<in>
      set_dist
        (execute
          (protocol_receive_counted_tagged_random_field_element counter bump tag) s)"
    and neq: "y \<noteq> tag (counter s) (PState s)"
    and bump_hash: "\<And>u. HashMap (bump u) = HashMap u"
  shows "fmlookup (HashMap t) y = fmlookup (HashMap s) y"
proof -
  from outcome obtain s0 h u v where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and hash_out:
      "Some (h, u) \<in>
        set_dist (execute (hash (tag (counter s0) (PState s0))) s0)"
    and mod:
      "Some ((), v) \<in> set_dist (execute (modify bump) u)"
    and ret: "Some (r, t) \<in> set_dist (execute (return h) v)"
    unfolding protocol_receive_counted_tagged_random_field_element_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have s0: "s0 = s"
    using get_s by simp
  have v: "v = bump u"
    using mod unfolding modify_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have t: "t = v"
    using ret by auto
  have hash_pres:
    "fmlookup (HashMap u) y = fmlookup (HashMap s) y"
    by (rule protocol_hash_preserves_other_lookup[OF hash_out[unfolded s0] neq])
  show ?thesis
    unfolding t v using hash_pres by (simp add: bump_hash)
qed

lemma protocol_merkle_create_no_failure:
  "None \<notin> dom (dist (execute (protocol_merkle.create xs) s))"
proof (induction xs arbitrary: s rule: protocol_merkle.create.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case
    by (simp add: no_failure_bindI protocol_hash_no_failure)
next
  case (3 v vb vc)
  then show ?case
    by (simp add: Let_def no_failure_bindI protocol_hash_no_failure)
qed

lemma protocol_merkle_create_preserves_channel:
  assumes outcome:
    "Some (r, t) \<in> set_dist (execute (protocol_merkle.create xs) s)"
  shows "PState t = PState s"
    and "PTranscript t = PTranscript s"
    and "PTraceFriCounter t = PTraceFriCounter s"
    and "PCompositionFriCounter t = PCompositionFriCounter s"
    and "PAlphaCounter t = PAlphaCounter s"
    and "PQueryCounter t = PQueryCounter s"
proof -
  have both:
    "PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
    if outcome:
      "Some (r, t) \<in> set_dist (execute (protocol_merkle.create xs) s)"
    for xs r s t
    using outcome
  proof (induction xs arbitrary: r s t rule: protocol_merkle.create.induct)
    case 1
    then show ?case by simp
  next
    case (2 x)
    from "2.prems" obtain h u where
      h: "Some (h, u) \<in> set_dist (execute (hash x) s)"
      and ret:
        "Some (r, t) \<in>
          set_dist (execute (return \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>) u)"
      by (auto elim!: protocol_merkle.set_dist_bindE)
    have "PState u = PState s \<and>
      PTranscript u = PTranscript s \<and>
      PTraceFriCounter u = PTraceFriCounter s \<and>
      PCompositionFriCounter u = PCompositionFriCounter s \<and>
      PAlphaCounter u = PAlphaCounter s \<and>
      PQueryCounter u = PQueryCounter s"
      using protocol_hash_channel_preserves[OF h] by simp
    then show ?case
      using ret by simp
  next
    case (3 v vb vc)
    from "3.prems" obtain l s1 rn s2 val s3 where
      l:
        "Some (l, s1) \<in>
          set_dist (execute
            (protocol_merkle.create
              (v # take (length vc div 2) (vb # vc))) s)"
      and rn:
        "Some (rn, s2) \<in>
          set_dist (execute
            (protocol_merkle.create
              (drop (length vc div 2) (vb # vc))) s1)"
      and val:
        "Some (val, s3) \<in>
          set_dist (execute (hash (MerkleNode (value l) (value rn))) s2)"
      and ret:
        "Some (r, t) \<in>
          set_dist (execute (return \<langle>l, val, rn\<rangle>) s3)"
      by (auto simp: Let_def elim!: protocol_merkle.set_dist_bindE)
    have s1:
      "PState s1 = PState s \<and>
       PTranscript s1 = PTranscript s \<and>
       PTraceFriCounter s1 = PTraceFriCounter s \<and>
       PCompositionFriCounter s1 = PCompositionFriCounter s \<and>
       PAlphaCounter s1 = PAlphaCounter s \<and>
       PQueryCounter s1 = PQueryCounter s"
      using "3.IH"(1)[of "length (v # vb # vc) div 2" l s1 s] l
      by simp
    have s2:
      "PState s2 = PState s1 \<and>
       PTranscript s2 = PTranscript s1 \<and>
       PTraceFriCounter s2 = PTraceFriCounter s1 \<and>
       PCompositionFriCounter s2 = PCompositionFriCounter s1 \<and>
       PAlphaCounter s2 = PAlphaCounter s1 \<and>
       PQueryCounter s2 = PQueryCounter s1"
      using "3.IH"(2)[of "length (v # vb # vc) div 2" rn s2 s1] rn
      by simp
    have s3:
      "PState s3 = PState s2 \<and>
       PTranscript s3 = PTranscript s2 \<and>
       PTraceFriCounter s3 = PTraceFriCounter s2 \<and>
       PCompositionFriCounter s3 = PCompositionFriCounter s2 \<and>
       PAlphaCounter s3 = PAlphaCounter s2 \<and>
       PQueryCounter s3 = PQueryCounter s2"
      using protocol_hash_channel_preserves[OF val] by simp
    show ?case
      using s1 s2 s3 ret by simp
  qed
  show "PState t = PState s"
    using both[OF assms] by simp
  show "PTranscript t = PTranscript s"
    using both[OF assms] by simp
  show "PTraceFriCounter t = PTraceFriCounter s"
    using both[OF assms] by simp
  show "PCompositionFriCounter t = PCompositionFriCounter s"
    using both[OF assms] by simp
  show "PAlphaCounter t = PAlphaCounter s"
    using both[OF assms] by simp
  show "PQueryCounter t = PQueryCounter s"
    using both[OF assms] by simp
qed

lemma protocol_merkle_create_preserves_non_merkle_lookup:
  assumes outcome:
    "Some (r, t) \<in> set_dist (execute (protocol_merkle.create xs) s)"
    and not_leaf: "\<And>x. x \<in> set xs \<Longrightarrow> y \<noteq> x"
    and not_node: "\<And>x z. y \<noteq> MerkleNode x z"
  shows "fmlookup (HashMap t) y = fmlookup (HashMap s) y"
  using outcome not_leaf
proof (induction xs arbitrary: r s t rule: protocol_merkle.create.induct)
  case 1
  then show ?case
    by simp
next
  case (2 x)
  from "2.prems"(1) obtain h u where
    h: "Some (h, u) \<in> set_dist (execute (hash x) s)"
    and ret:
      "Some (r, t) \<in>
        set_dist (execute (return \<langle>\<langle>\<rangle>, h, \<langle>\<rangle>\<rangle>) u)"
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have h_pres: "fmlookup (HashMap u) y = fmlookup (HashMap s) y"
    by (rule protocol_hash_preserves_other_lookup[OF h])
      (rule "2.prems"(2), simp)
  show ?case
    using h_pres ret by simp
next
  case (3 v vb vc)
  let ?left = "v # take (length vc div 2) (vb # vc)"
  let ?right = "drop (length vc div 2) (vb # vc)"
  have left_eq:
    "?left = take (length (v # vb # vc) div 2) (v # vb # vc)"
    by simp
  have right_eq:
    "?right = drop (length (v # vb # vc) div 2) (v # vb # vc)"
    by simp
  from "3.prems"(1) obtain l s1 rn s2 val s3 where
    l:
      "Some (l, s1) \<in>
        set_dist (execute (protocol_merkle.create ?left) s)"
    and rn:
      "Some (rn, s2) \<in>
        set_dist (execute (protocol_merkle.create ?right) s1)"
    and val:
      "Some (val, s3) \<in>
        set_dist (execute (hash (MerkleNode (value l) (value rn))) s2)"
    and ret:
      "Some (r, t) \<in>
        set_dist (execute (return \<langle>l, val, rn\<rangle>) s3)"
    by (auto simp: Let_def elim!: protocol_merkle.set_dist_bindE)
  have left_not_leaf: "\<And>x. x \<in> set ?left \<Longrightarrow> y \<noteq> x"
  proof -
    fix x
    assume mem: "x \<in> set ?left"
    show "y \<noteq> x"
    proof (cases "x = v")
      case True
      then show ?thesis
        using "3.prems"(2)[of x] by simp
    next
      case False
      then have "x \<in> set (take (length vc div 2) (vb # vc))"
        using mem by simp
      then have "x \<in> set (vb # vc)"
        by (rule in_set_takeD)
      then show ?thesis
        using "3.prems"(2)[of x] by simp
    qed
  qed
  have right_not_leaf: "\<And>x. x \<in> set ?right \<Longrightarrow> y \<noteq> x"
  proof -
    fix x
    assume mem: "x \<in> set ?right"
    then have "x \<in> set (vb # vc)"
      by (rule in_set_dropD)
    then show "y \<noteq> x"
      using "3.prems"(2)[of x] by simp
  qed
  have l':
    "Some (l, s1) \<in>
      set_dist (execute
        (protocol_merkle.create
          (take (length (v # vb # vc) div 2) (v # vb # vc))) s)"
    using l by (simp only: left_eq[symmetric])
  have rn':
    "Some (rn, s2) \<in>
      set_dist (execute
        (protocol_merkle.create
          (drop (length (v # vb # vc) div 2) (v # vb # vc))) s1)"
    using rn by (simp only: right_eq[symmetric])
  have left_not_leaf':
    "\<And>x. x \<in> set (take (length (v # vb # vc) div 2) (v # vb # vc)) \<Longrightarrow>
      y \<noteq> x"
  proof -
    fix x
    assume mem: "x \<in> set (take (length (v # vb # vc) div 2) (v # vb # vc))"
    have "x \<in> set ?left"
      using mem by (simp only: left_eq)
    then show "y \<noteq> x"
      by (rule left_not_leaf)
  qed
  have right_not_leaf':
    "\<And>x. x \<in> set (drop (length (v # vb # vc) div 2) (v # vb # vc)) \<Longrightarrow>
      y \<noteq> x"
  proof -
    fix x
    assume mem: "x \<in> set (drop (length (v # vb # vc) div 2) (v # vb # vc))"
    have "x \<in> set ?right"
      using mem by (simp only: right_eq)
    then show "y \<noteq> x"
      by (rule right_not_leaf)
  qed
  have left_pres: "fmlookup (HashMap s1) y = fmlookup (HashMap s) y"
    by (rule "3.IH"(1)
        [of "length (v # vb # vc) div 2" l s1 s,
          OF refl l' left_not_leaf'])
  have right_pres: "fmlookup (HashMap s2) y = fmlookup (HashMap s1) y"
    by (rule "3.IH"(2)
        [of "length (v # vb # vc) div 2" rn s2 s1,
          OF refl rn' right_not_leaf'])
  have hash_pres: "fmlookup (HashMap s3) y = fmlookup (HashMap s2) y"
    by (rule protocol_hash_preserves_other_lookup[OF val])
      (rule not_node)
  show ?case
    using left_pres right_pres hash_pres ret by simp
qed

lemma protocol_create_preserves_non_merkle_lookup:
  assumes outcome: "Some (r, t) \<in> set_dist (execute (protocol_create xs) s)"
    and not_leaf: "\<And>x. y \<noteq> MerkleLeaf x"
    and not_node: "\<And>x z. y \<noteq> MerkleNode x z"
  shows "fmlookup (HashMap t) y = fmlookup (HashMap s) y"
proof -
  have outcome':
    "Some (r, t) \<in>
      set_dist (execute (protocol_merkle.create (map MerkleLeaf xs)) s)"
    using outcome unfolding protocol_create_def .
  show ?thesis
    by (rule protocol_merkle_create_preserves_non_merkle_lookup[OF outcome'])
      (use not_leaf not_node in auto)
qed

locale protocol_channel_compat =
  fixes concat :: "'a::finite \<Rightarrow> 'a \<Rightarrow> 'a"
begin

definition create
  :: "'a list \<Rightarrow> ('a protocol_hash_input, 'a, 'a tree, 'b) hash_monad"
  where "create xs = protocol_create xs"

definition check_authentication_path
  :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow>
      ('a protocol_hash_input, 'a, 'a, 'b) hash_monad"
  where
    "check_authentication_path len idx leaf path =
      protocol_check_authentication_path len idx leaf path"

definition created_tree
  :: "'a list \<Rightarrow> 'a tree \<Rightarrow>
      ('a protocol_hash_input, 'a, 'b) hash_scheme \<Rightarrow> bool"
  where "created_tree xs r s \<longleftrightarrow> protocol_created_tree xs r s"

definition receive_random_field_element
  :: "('a, 'a, 'b) protocol_c_monad"
  where
    "receive_random_field_element = protocol_receive_random_field_element"

definition receive_tagged_random_field_element
  :: "('a \<Rightarrow> 'a protocol_hash_input) \<Rightarrow>
      ('a, 'a, 'b) protocol_c_monad"
  where
    "receive_tagged_random_field_element tag =
      protocol_receive_tagged_random_field_element tag"

definition receive_trace_fri_challenge
  :: "('a, 'a, 'b) protocol_c_monad"
  where
    "receive_trace_fri_challenge =
      protocol_receive_counted_tagged_random_field_element
        PTraceFriCounter
        (\<lambda>s. s\<lparr>PTraceFriCounter := Suc (PTraceFriCounter s)\<rparr>)
        TraceFriChallenge"

definition receive_composition_fri_challenge
  :: "('a, 'a, 'b) protocol_c_monad"
  where
    "receive_composition_fri_challenge =
      protocol_receive_counted_tagged_random_field_element
        PCompositionFriCounter
        (\<lambda>s. s\<lparr>PCompositionFriCounter := Suc (PCompositionFriCounter s)\<rparr>)
        CompositionFriChallenge"

definition receive_alpha_challenge
  :: "('a, 'a, 'b) protocol_c_monad"
  where
    "receive_alpha_challenge =
      protocol_receive_counted_tagged_random_field_element
        PAlphaCounter
        (\<lambda>s. s\<lparr>PAlphaCounter := Suc (PAlphaCounter s)\<rparr>)
        AlphaChallenge"

definition receive_query_index_challenge
  :: "('a, 'a, 'b) protocol_c_monad"
  where
    "receive_query_index_challenge =
      protocol_receive_counted_tagged_random_field_element
        PQueryCounter
        (\<lambda>s. s\<lparr>PQueryCounter := Suc (PQueryCounter s)\<rparr>)
        QueryIndexChallenge"

definition send :: "'a \<Rightarrow> ('a, unit, 'b) protocol_c_monad"
  where "send x = protocol_send concat x"

definition read :: "('a, 'a, 'b) protocol_c_monad"
  where "read = protocol_read concat"

lemmas set_dist_bindE = protocol_merkle.set_dist_bindE
lemmas hash_outcome = protocol_merkle.hash_outcome
lemmas hash_ext_refl = protocol_merkle.hash_ext_refl
lemmas hash_ext_trans = protocol_merkle.hash_ext_trans
lemmas hash_extension_lookup = protocol_merkle.hash_extension_lookup

lemma hash_no_failure:
  "None \<notin> dom (dist (execute (hash x) s))"
  by (rule protocol_hash_no_failure)

lemmas hash_channel_preserves = protocol_hash_channel_preserves

lemma send_no_failure:
  "None \<notin> dom (dist (execute (send x) s))"
  unfolding send_def protocol_send_def
  by simp

lemma create_no_failure:
  "None \<notin> dom (dist (execute (create xs) s))"
  unfolding create_def protocol_create_def
  by (rule protocol_merkle_create_no_failure)

lemma created_tree_mono:
  assumes "created_tree xs r s0"
    and "s0 \<le> s"
  shows "created_tree xs r s"
  using assms
  unfolding created_tree_def
  by (rule protocol_created_tree_mono)

lemma create_outcome:
  assumes "Some (r, t) \<in> set_dist (execute (create xs) s)"
  shows "s \<le> t \<and> created_tree xs r t"
  using protocol_create_outcome[OF assms[unfolded create_def]]
  unfolding created_tree_def by simp

lemma create_get_authentication_path_len:
  assumes "Some (r, t) \<in> set_dist (execute (create xs) s)"
    and "0 < lgth"
    and "lgth \<le> length xs"
  shows "length (get_authentication_path lgth idx r) = floor_log lgth"
  using protocol_merkle.create_get_authentication_path_len
      [OF assms(1)[unfolded create_def protocol_create_def] assms(2)]
    assms(3)
  by simp

lemma create_preserves_channel:
  assumes "Some (r, t) \<in> set_dist (execute (create xs) s)"
  shows "PState t = PState s"
    and "PTranscript t = PTranscript s"
    and "PTraceFriCounter t = PTraceFriCounter s"
    and "PCompositionFriCounter t = PCompositionFriCounter s"
    and "PAlphaCounter t = PAlphaCounter s"
    and "PQueryCounter t = PQueryCounter s"
  using protocol_merkle_create_preserves_channel
      [OF assms[unfolded create_def protocol_create_def]]
  by simp_all

lemma create_preserves_non_merkle_lookup:
  assumes outcome: "Some (r, t) \<in> set_dist (execute (create xs) s)"
    and not_leaf: "\<And>x. y \<noteq> MerkleLeaf x"
    and not_node: "\<And>x z. y \<noteq> MerkleNode x z"
  shows "fmlookup (HashMap t) y = fmlookup (HashMap s) y"
  using protocol_create_preserves_non_merkle_lookup
      [OF outcome[unfolded create_def] not_leaf not_node]
  by simp

lemma create_preserves_challenge_lookups:
  assumes outcome: "Some (r, t) \<in> set_dist (execute (create xs) s)"
  shows
    "fmlookup (HashMap t) (AlphaChallenge i x) =
      fmlookup (HashMap s) (AlphaChallenge i x)"
    "fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s) (QueryIndexChallenge i x)"
    "fmlookup (HashMap t) (TraceFriChallenge i x) =
      fmlookup (HashMap s) (TraceFriChallenge i x)"
    "fmlookup (HashMap t) (CompositionFriChallenge i x) =
      fmlookup (HashMap s) (CompositionFriChallenge i x)"
proof -
  show "fmlookup (HashMap t) (AlphaChallenge i x) =
      fmlookup (HashMap s) (AlphaChallenge i x)"
    by (rule create_preserves_non_merkle_lookup[OF outcome]) simp_all
  show "fmlookup (HashMap t) (QueryIndexChallenge i x) =
      fmlookup (HashMap s) (QueryIndexChallenge i x)"
    by (rule create_preserves_non_merkle_lookup[OF outcome]) simp_all
  show "fmlookup (HashMap t) (TraceFriChallenge i x) =
      fmlookup (HashMap s) (TraceFriChallenge i x)"
    by (rule create_preserves_non_merkle_lookup[OF outcome]) simp_all
  show "fmlookup (HashMap t) (CompositionFriChallenge i x) =
      fmlookup (HashMap s) (CompositionFriChallenge i x)"
    by (rule create_preserves_non_merkle_lookup[OF outcome]) simp_all
qed

lemma check_created_tree_outcome:
  assumes created: "created_tree xs r s0"
    and length_xs: "length xs = 2 ^ n"
    and i_bound: "i < length xs"
    and v: "v = xs ! i"
    and ext: "s0 \<le> s"
    and check:
      "Some (h, t) \<in> set_dist (execute
        (check_authentication_path (length xs) i v
          (get_authentication_path (length xs) i r)) s)"
  shows "h = value r \<and> s \<le> t"
  using protocol_check_created_tree_outcome
      [OF created[unfolded created_tree_def] length_xs i_bound v ext
        check[unfolded check_authentication_path_def]]
  by simp

lemma receive_random_field_element_no_failure:
  "None \<notin> dom (dist (execute receive_random_field_element s))"
  unfolding receive_random_field_element_def
  by (rule protocol_receive_random_field_element_no_failure)

lemma receive_tagged_random_field_element_no_failure:
  "None \<notin>
    dom (dist (execute (receive_tagged_random_field_element tag) s))"
  unfolding receive_tagged_random_field_element_def
  by (rule protocol_receive_tagged_random_field_element_no_failure)

lemma receive_trace_fri_challenge_no_failure:
  "None \<notin> dom (dist (execute receive_trace_fri_challenge s))"
  unfolding receive_trace_fri_challenge_def
  by (rule protocol_receive_counted_tagged_random_field_element_no_failure)

lemma receive_composition_fri_challenge_no_failure:
  "None \<notin> dom (dist (execute receive_composition_fri_challenge s))"
  unfolding receive_composition_fri_challenge_def
  by (rule protocol_receive_counted_tagged_random_field_element_no_failure)

lemma receive_alpha_challenge_no_failure:
  "None \<notin> dom (dist (execute receive_alpha_challenge s))"
  unfolding receive_alpha_challenge_def
  by (rule protocol_receive_counted_tagged_random_field_element_no_failure)

lemma receive_query_index_challenge_no_failure:
  "None \<notin> dom (dist (execute receive_query_index_challenge s))"
  unfolding receive_query_index_challenge_def
  by (rule protocol_receive_counted_tagged_random_field_element_no_failure)

lemma receive_random_field_element_outcome:
  assumes "Some (r, t) \<in>
    set_dist (execute receive_random_field_element s)"
  shows
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t) (FiatShamirChallenge (PState s)) = Some r"
  using protocol_receive_random_field_element_outcome
      [OF assms[unfolded receive_random_field_element_def]]
  by simp

lemma receive_tagged_random_field_element_outcome:
  assumes "Some (r, t) \<in>
    set_dist (execute (receive_tagged_random_field_element tag) s)"
  shows
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t) (tag (PState s)) = Some r"
  using protocol_receive_tagged_random_field_element_outcome
      [OF assms[unfolded receive_tagged_random_field_element_def]]
  by simp

lemma receive_tagged_random_field_element_preserves_other_lookup:
  assumes "Some (r, t) \<in>
    set_dist (execute (receive_tagged_random_field_element tag) s)"
    and "y \<noteq> tag (PState s)"
  shows "fmlookup (HashMap t) y = fmlookup (HashMap s) y"
  using protocol_receive_tagged_random_field_element_preserves_other_lookup
      [OF assms(1)[unfolded receive_tagged_random_field_element_def] assms(2)]
  by simp

lemma receive_trace_fri_challenge_outcome:
  assumes "Some (r, t) \<in> set_dist (execute receive_trace_fri_challenge s)"
  shows
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t)
       (TraceFriChallenge (PTraceFriCounter s) (PState s)) = Some r"
  using protocol_receive_counted_tagged_random_field_element_outcome
      [OF assms[unfolded receive_trace_fri_challenge_def]]
  by simp

lemma receive_composition_fri_challenge_outcome:
  assumes "Some (r, t) \<in>
    set_dist (execute receive_composition_fri_challenge s)"
  shows
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t)
       (CompositionFriChallenge (PCompositionFriCounter s) (PState s)) =
        Some r"
  using protocol_receive_counted_tagged_random_field_element_outcome
      [OF assms[unfolded receive_composition_fri_challenge_def]]
  by simp

lemma receive_alpha_challenge_outcome:
  assumes "Some (r, t) \<in> set_dist (execute receive_alpha_challenge s)"
  shows
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t)
       (AlphaChallenge (PAlphaCounter s) (PState s)) = Some r"
  using protocol_receive_counted_tagged_random_field_element_outcome
      [OF assms[unfolded receive_alpha_challenge_def]]
  by simp

lemma receive_query_index_challenge_outcome:
  assumes "Some (r, t) \<in> set_dist (execute receive_query_index_challenge s)"
  shows
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t)
       (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some r"
  using protocol_receive_counted_tagged_random_field_element_outcome
      [OF assms[unfolded receive_query_index_challenge_def]]
  by simp

lemma receive_trace_fri_challenge_preserves_other_lookup:
  assumes "Some (r, t) \<in> set_dist (execute receive_trace_fri_challenge s)"
    and "y \<noteq> TraceFriChallenge (PTraceFriCounter s) (PState s)"
  shows "fmlookup (HashMap t) y = fmlookup (HashMap s) y"
  using protocol_receive_counted_tagged_random_field_element_preserves_other_lookup
      [OF assms(1)[unfolded receive_trace_fri_challenge_def] assms(2)]
  by simp

lemma receive_composition_fri_challenge_preserves_other_lookup:
  assumes "Some (r, t) \<in>
    set_dist (execute receive_composition_fri_challenge s)"
    and "y \<noteq> CompositionFriChallenge (PCompositionFriCounter s) (PState s)"
  shows "fmlookup (HashMap t) y = fmlookup (HashMap s) y"
  using protocol_receive_counted_tagged_random_field_element_preserves_other_lookup
      [OF assms(1)[unfolded receive_composition_fri_challenge_def] assms(2)]
  by simp

lemma receive_alpha_challenge_preserves_other_lookup:
  assumes "Some (r, t) \<in> set_dist (execute receive_alpha_challenge s)"
    and "y \<noteq> AlphaChallenge (PAlphaCounter s) (PState s)"
  shows "fmlookup (HashMap t) y = fmlookup (HashMap s) y"
  using protocol_receive_counted_tagged_random_field_element_preserves_other_lookup
      [OF assms(1)[unfolded receive_alpha_challenge_def] assms(2)]
  by simp

lemma receive_query_index_challenge_preserves_other_lookup:
  assumes "Some (r, t) \<in> set_dist (execute receive_query_index_challenge s)"
    and "y \<noteq> QueryIndexChallenge (PQueryCounter s) (PState s)"
  shows "fmlookup (HashMap t) y = fmlookup (HashMap s) y"
  using protocol_receive_counted_tagged_random_field_element_preserves_other_lookup
      [OF assms(1)[unfolded receive_query_index_challenge_def] assms(2)]
  by simp

lemma receive_trace_fri_challenge_counter_outcome:
  assumes "Some (r, t) \<in> set_dist (execute receive_trace_fri_challenge s)"
  shows
    "PTraceFriCounter t = Suc (PTraceFriCounter s) \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
proof -
  from assms obtain s0 h u v where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and hash_out:
      "Some (h, u) \<in>
        set_dist (execute
          (hash (TraceFriChallenge (PTraceFriCounter s0) (PState s0))) s0)"
    and mod:
      "Some ((), v) \<in>
        set_dist (execute
          (modify (\<lambda>s. s\<lparr>PTraceFriCounter := Suc (PTraceFriCounter s)\<rparr>)) u)"
    and ret: "Some (r, t) \<in> set_dist (execute (return h) v)"
    unfolding receive_trace_fri_challenge_def
      protocol_receive_counted_tagged_random_field_element_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have s0: "s0 = s"
    using get_s by simp
  have v: "v = u\<lparr>PTraceFriCounter := Suc (PTraceFriCounter u)\<rparr>"
    using mod unfolding modify_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have t: "t = v"
    using ret by simp
  have counters_u:
    "PTraceFriCounter u = PTraceFriCounter s \<and>
     PCompositionFriCounter u = PCompositionFriCounter s \<and>
     PAlphaCounter u = PAlphaCounter s \<and>
     PQueryCounter u = PQueryCounter s"
    using protocol_hash_channel_preserves[OF hash_out[unfolded s0]]
    by simp
  show ?thesis
    unfolding t v using counters_u by simp
qed

lemma receive_composition_fri_challenge_counter_outcome:
  assumes "Some (r, t) \<in> set_dist (execute receive_composition_fri_challenge s)"
  shows
    "PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = Suc (PCompositionFriCounter s) \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
proof -
  from assms obtain s0 h u v where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and hash_out:
      "Some (h, u) \<in>
        set_dist (execute
          (hash (CompositionFriChallenge
            (PCompositionFriCounter s0) (PState s0))) s0)"
    and mod:
      "Some ((), v) \<in>
        set_dist (execute
          (modify (\<lambda>s. s\<lparr>
            PCompositionFriCounter := Suc (PCompositionFriCounter s)\<rparr>)) u)"
    and ret: "Some (r, t) \<in> set_dist (execute (return h) v)"
    unfolding receive_composition_fri_challenge_def
      protocol_receive_counted_tagged_random_field_element_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have s0: "s0 = s"
    using get_s by simp
  have v: "v = u\<lparr>
      PCompositionFriCounter := Suc (PCompositionFriCounter u)\<rparr>"
    using mod unfolding modify_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have t: "t = v"
    using ret by simp
  have counters_u:
    "PTraceFriCounter u = PTraceFriCounter s \<and>
     PCompositionFriCounter u = PCompositionFriCounter s \<and>
     PAlphaCounter u = PAlphaCounter s \<and>
     PQueryCounter u = PQueryCounter s"
    using protocol_hash_channel_preserves[OF hash_out[unfolded s0]]
    by simp
  show ?thesis
    unfolding t v using counters_u by simp
qed

lemma receive_alpha_challenge_counter_outcome:
  assumes "Some (r, t) \<in> set_dist (execute receive_alpha_challenge s)"
  shows
    "PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = Suc (PAlphaCounter s) \<and>
     PQueryCounter t = PQueryCounter s"
proof -
  from assms obtain s0 h u v where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and hash_out:
      "Some (h, u) \<in>
        set_dist (execute
          (hash (AlphaChallenge (PAlphaCounter s0) (PState s0))) s0)"
    and mod:
      "Some ((), v) \<in>
        set_dist (execute
          (modify (\<lambda>s. s\<lparr>PAlphaCounter := Suc (PAlphaCounter s)\<rparr>)) u)"
    and ret: "Some (r, t) \<in> set_dist (execute (return h) v)"
    unfolding receive_alpha_challenge_def
      protocol_receive_counted_tagged_random_field_element_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have s0: "s0 = s"
    using get_s by simp
  have v: "v = u\<lparr>PAlphaCounter := Suc (PAlphaCounter u)\<rparr>"
    using mod unfolding modify_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have t: "t = v"
    using ret by simp
  have counters_u:
    "PTraceFriCounter u = PTraceFriCounter s \<and>
     PCompositionFriCounter u = PCompositionFriCounter s \<and>
     PAlphaCounter u = PAlphaCounter s \<and>
     PQueryCounter u = PQueryCounter s"
    using protocol_hash_channel_preserves[OF hash_out[unfolded s0]]
    by simp
  show ?thesis
    unfolding t v using counters_u by simp
qed

lemma receive_random_field_element_counter_outcome:
  assumes "Some (r, t) \<in> set_dist (execute receive_random_field_element s)"
  shows
    "PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
proof -
  from assms obtain s0 where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and hash_out:
      "Some (r, t) \<in>
        set_dist (execute (hash (FiatShamirChallenge (PState s0)) \<bind> return) s0)"
    unfolding receive_random_field_element_def
      protocol_receive_random_field_element_def
      protocol_receive_tagged_random_field_element_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have s0: "s0 = s"
    using get_s by simp
  from hash_out obtain h u where
    hash_u:
      "Some (h, u) \<in>
        set_dist (execute (hash (FiatShamirChallenge (PState s))) s)"
    and ret: "Some (r, t) \<in> set_dist (execute (return h) u)"
    unfolding s0 by (auto elim!: protocol_merkle.set_dist_bindE)
  have t: "t = u"
    using ret by simp
  show ?thesis
    using protocol_hash_channel_preserves[OF hash_u]
    unfolding t by simp
qed

lemma receive_query_index_challenge_counter_outcome:
  assumes "Some (r, t) \<in> set_dist (execute receive_query_index_challenge s)"
  shows
    "PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = Suc (PQueryCounter s)"
proof -
  from assms obtain s0 h u v where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and hash_out:
      "Some (h, u) \<in>
        set_dist (execute
          (hash (QueryIndexChallenge (PQueryCounter s0) (PState s0))) s0)"
    and mod:
      "Some ((), v) \<in>
        set_dist (execute
          (modify (\<lambda>s. s\<lparr>PQueryCounter := Suc (PQueryCounter s)\<rparr>)) u)"
    and ret: "Some (r, t) \<in> set_dist (execute (return h) v)"
    unfolding receive_query_index_challenge_def
      protocol_receive_counted_tagged_random_field_element_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have s0: "s0 = s"
    using get_s by simp
  have v: "v = u\<lparr>PQueryCounter := Suc (PQueryCounter u)\<rparr>"
    using mod unfolding modify_def
    by (auto elim!: protocol_merkle.set_dist_bindE)
  have t: "t = v"
    using ret by simp
  have counters_u:
    "PTraceFriCounter u = PTraceFriCounter s \<and>
     PCompositionFriCounter u = PCompositionFriCounter s \<and>
     PAlphaCounter u = PAlphaCounter s \<and>
     PQueryCounter u = PQueryCounter s"
    using protocol_hash_channel_preserves[OF hash_out[unfolded s0]]
    by simp
  show ?thesis
    unfolding t v using counters_u by simp
qed

lemma bind_preserves_lookup:
  fixes m :: "('x, ('a, 'b) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('a, 'b) protocol_channel_scheme) state_monad"
  assumes outcome: "Some (y, t) \<in> set_dist (execute (m \<bind> k) s)"
    and m_pres:
      "\<And>x u. Some (x, u) \<in> set_dist (execute m s) \<Longrightarrow>
        fmlookup (HashMap u) key = fmlookup (HashMap s) key"
    and k_pres:
      "\<And>x u y t. Some (x, u) \<in> set_dist (execute m s) \<Longrightarrow>
        Some (y, t) \<in> set_dist (execute (k x) u) \<Longrightarrow>
        fmlookup (HashMap t) key = fmlookup (HashMap u) key"
  shows "fmlookup (HashMap t) key = fmlookup (HashMap s) key"
proof -
  from outcome obtain x u where
    m_out: "Some (x, u) \<in> set_dist (execute m s)"
    and k_out: "Some (y, t) \<in> set_dist (execute (k x) u)"
    by (elim set_dist_bindE)
  have "fmlookup (HashMap t) key = fmlookup (HashMap u) key"
    by (rule k_pres[OF m_out k_out])
  also have "... = fmlookup (HashMap s) key"
    by (rule m_pres[OF m_out])
  finally show ?thesis .
qed

lemma mmap_preserves_lookup:
  fixes ms :: "('x, ('a, 'b) protocol_channel_scheme) state_monad list"
  assumes step:
      "\<And>m x s t. m \<in> set ms \<Longrightarrow>
        Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        fmlookup (HashMap t) key = fmlookup (HashMap s) key"
    and outcome: "Some (xs, t) \<in> set_dist (execute (mmap ms) s)"
  shows "fmlookup (HashMap t) key = fmlookup (HashMap s) key"
  using step outcome
proof (induction ms arbitrary: xs s t)
  case Nil
  then show ?case
    by simp
next
  case (Cons m ms)
  from Cons.prems(2) obtain x u ys where
    m_out: "Some (x, u) \<in> set_dist (execute m s)"
    and tail_out: "Some (ys, t) \<in> set_dist (execute (mmap ms) u)"
    and xs_eq: "xs = x # ys"
    by (auto elim!: set_dist_bindE)
  have head_pres: "fmlookup (HashMap u) key = fmlookup (HashMap s) key"
    by (rule Cons.prems(1)) (use m_out in simp_all)
  have step_tail:
    "\<And>m x s t. m \<in> set ms \<Longrightarrow>
      Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
      fmlookup (HashMap t) key = fmlookup (HashMap s) key"
  proof -
    fix m x s t
    assume mem: "m \<in> set ms"
      and out: "Some (x, t) \<in> set_dist (execute m s)"
    show "fmlookup (HashMap t) key = fmlookup (HashMap s) key"
      by (rule Cons.prems(1)) (use mem out in simp_all)
  qed
  have tail_pres: "fmlookup (HashMap t) key = fmlookup (HashMap u) key"
    by (rule Cons.IH[OF step_tail tail_out])
  show ?case
    using head_pres tail_pres by simp
qed

lemma mfold2_preserves_lookup:
  fixes f :: "'x \<Rightarrow> (unit, ('a, 'b) protocol_channel_scheme) state_monad"
  assumes step:
      "\<And>x s t. x \<in> set xs \<Longrightarrow>
        Some ((), t) \<in> set_dist (execute (f x) s) \<Longrightarrow>
        fmlookup (HashMap t) key = fmlookup (HashMap s) key"
    and outcome: "Some ((), t) \<in> set_dist (execute (mfold2 f xs) s)"
  shows "fmlookup (HashMap t) key = fmlookup (HashMap s) key"
  using step outcome
proof (induction xs arbitrary: s t)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  from Cons.prems(2) obtain u where
    head_out: "Some ((), u) \<in> set_dist (execute (f x) s)"
    and tail_out: "Some ((), t) \<in> set_dist (execute (mfold2 f xs) u)"
    by (auto elim!: set_dist_bindE)
  have head_pres: "fmlookup (HashMap u) key = fmlookup (HashMap s) key"
    by (rule Cons.prems(1)) (use head_out in simp_all)
  have step_tail:
    "\<And>x s t. x \<in> set xs \<Longrightarrow>
      Some ((), t) \<in> set_dist (execute (f x) s) \<Longrightarrow>
      fmlookup (HashMap t) key = fmlookup (HashMap s) key"
  proof -
    fix x s t
    assume mem: "x \<in> set xs"
      and out: "Some ((), t) \<in> set_dist (execute (f x) s)"
    show "fmlookup (HashMap t) key = fmlookup (HashMap s) key"
      by (rule Cons.prems(1)) (use mem out in simp_all)
  qed
  have tail_pres: "fmlookup (HashMap t) key = fmlookup (HashMap u) key"
    by (rule Cons.IH[OF step_tail tail_out])
  show ?case
    using head_pres tail_pres by simp
qed

lemma mfold_preserves_lookup:
  fixes ms :: "('x \<Rightarrow> ('x, ('a, 'b) protocol_channel_scheme) state_monad) list"
  assumes step:
      "\<And>m a x s t. m \<in> set ms \<Longrightarrow>
        Some (x, t) \<in> set_dist (execute (m a) s) \<Longrightarrow>
        fmlookup (HashMap t) key = fmlookup (HashMap s) key"
    and outcome: "Some (x, t) \<in> set_dist (execute (mfold a ms) s)"
  shows "fmlookup (HashMap t) key = fmlookup (HashMap s) key"
  using step outcome
proof (induction ms arbitrary: a x s t)
  case Nil
  then show ?case
    by simp
next
  case (Cons m ms)
  from Cons.prems(2) obtain y u where
    head_out: "Some (y, u) \<in> set_dist (execute (m a) s)"
    and tail_out: "Some (x, t) \<in> set_dist (execute (mfold y ms) u)"
    by (auto elim!: set_dist_bindE)
  have head_pres: "fmlookup (HashMap u) key = fmlookup (HashMap s) key"
    by (rule Cons.prems(1)) (use head_out in simp_all)
  have step_tail:
    "\<And>m a x s t. m \<in> set ms \<Longrightarrow>
      Some (x, t) \<in> set_dist (execute (m a) s) \<Longrightarrow>
      fmlookup (HashMap t) key = fmlookup (HashMap s) key"
  proof -
    fix m a x s t
    assume mem: "m \<in> set ms"
      and out: "Some (x, t) \<in> set_dist (execute (m a) s)"
    show "fmlookup (HashMap t) key = fmlookup (HashMap s) key"
      by (rule Cons.prems(1)) (use mem out in simp_all)
  qed
  have tail_pres: "fmlookup (HashMap t) key = fmlookup (HashMap u) key"
    by (rule Cons.IH[OF step_tail tail_out])
  show ?case
    using head_pres tail_pres by simp
qed

lemma ntimes_preserves_lookup:
  fixes m :: "('x, ('a, 'b) protocol_channel_scheme) state_monad"
  assumes step:
      "\<And>x s t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        fmlookup (HashMap t) key = fmlookup (HashMap s) key"
    and outcome: "Some (xs, t) \<in> set_dist (execute (ntimes m n) s)"
  shows "fmlookup (HashMap t) key = fmlookup (HashMap s) key"
  using step outcome
proof (induction n arbitrary: xs s t)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems(2) obtain x u ys where
    head_out: "Some (x, u) \<in> set_dist (execute m s)"
    and tail_out: "Some (ys, t) \<in> set_dist (execute (ntimes m n) u)"
    and xs_eq: "xs = x # ys"
    by (auto elim!: set_dist_bindE)
  have head_pres: "fmlookup (HashMap u) key = fmlookup (HashMap s) key"
    by (rule Suc.prems(1)[OF head_out])
  have tail_pres: "fmlookup (HashMap t) key = fmlookup (HashMap u) key"
    by (rule Suc.IH[OF Suc.prems(1) tail_out])
  show ?case
    using head_pres tail_pres by simp
qed

lemma receive_random_field_element_known_outcome:
  assumes lookup:
      "fmlookup (HashMap s) (FiatShamirChallenge (PState s)) = Some r"
    and outcome:
      "Some (r', t) \<in> set_dist (execute receive_random_field_element s)"
  shows
    "r' = r \<and> PState t = PState s \<and>
     PTranscript t = PTranscript s \<and> s \<le> t"
proof -
  have out:
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t) (FiatShamirChallenge (PState s)) = Some r'"
    by (rule receive_random_field_element_outcome[OF outcome])
  have old:
    "fmlookup (HashMap t) (FiatShamirChallenge (PState s)) = Some r"
    using lookup out
    by (meson protocol_merkle.hash_extension_lookup)
  show ?thesis
    using out old by auto
qed

lemma receive_tagged_random_field_element_known_outcome:
  assumes lookup:
      "fmlookup (HashMap s) (tag (PState s)) = Some r"
    and outcome:
      "Some (r', t) \<in>
        set_dist (execute (receive_tagged_random_field_element tag) s)"
  shows
    "r' = r \<and> PState t = PState s \<and>
     PTranscript t = PTranscript s \<and> s \<le> t"
proof -
  have out:
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t) (tag (PState s)) = Some r'"
    by (rule receive_tagged_random_field_element_outcome[OF outcome])
  have old:
    "fmlookup (HashMap t) (tag (PState s)) = Some r"
    using lookup out
    by (meson protocol_merkle.hash_extension_lookup)
  show ?thesis
    using out old by auto
qed

lemma receive_trace_fri_challenge_known_outcome:
  assumes "fmlookup (HashMap s)
      (TraceFriChallenge (PTraceFriCounter s) (PState s)) = Some r"
    and "Some (r', t) \<in> set_dist (execute receive_trace_fri_challenge s)"
  shows
    "r' = r \<and> PState t = PState s \<and>
     PTranscript t = PTranscript s \<and> s \<le> t"
proof -
  have out:
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t)
       (TraceFriChallenge (PTraceFriCounter s) (PState s)) = Some r'"
    by (rule receive_trace_fri_challenge_outcome[OF assms(2)])
  have old:
    "fmlookup (HashMap t)
       (TraceFriChallenge (PTraceFriCounter s) (PState s)) = Some r"
    using assms(1) out
    by (meson protocol_merkle.hash_extension_lookup)
  show ?thesis
    using out old by auto
qed

lemma receive_composition_fri_challenge_known_outcome:
  assumes "fmlookup (HashMap s)
      (CompositionFriChallenge (PCompositionFriCounter s) (PState s)) = Some r"
    and "Some (r', t) \<in> set_dist (execute receive_composition_fri_challenge s)"
  shows
    "r' = r \<and> PState t = PState s \<and>
     PTranscript t = PTranscript s \<and> s \<le> t"
proof -
  have out:
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t)
       (CompositionFriChallenge (PCompositionFriCounter s) (PState s)) =
        Some r'"
    by (rule receive_composition_fri_challenge_outcome[OF assms(2)])
  have old:
    "fmlookup (HashMap t)
       (CompositionFriChallenge (PCompositionFriCounter s) (PState s)) =
        Some r"
    using assms(1) out
    by (meson protocol_merkle.hash_extension_lookup)
  show ?thesis
    using out old by auto
qed

lemma receive_alpha_challenge_known_outcome:
  assumes "fmlookup (HashMap s)
      (AlphaChallenge (PAlphaCounter s) (PState s)) = Some r"
    and "Some (r', t) \<in> set_dist (execute receive_alpha_challenge s)"
  shows
    "r' = r \<and> PState t = PState s \<and>
     PTranscript t = PTranscript s \<and> s \<le> t"
proof -
  have out:
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t)
       (AlphaChallenge (PAlphaCounter s) (PState s)) = Some r'"
    by (rule receive_alpha_challenge_outcome[OF assms(2)])
  have old:
    "fmlookup (HashMap t)
       (AlphaChallenge (PAlphaCounter s) (PState s)) = Some r"
    using assms(1) out
    by (meson protocol_merkle.hash_extension_lookup)
  show ?thesis
    using out old by auto
qed

lemma receive_query_index_challenge_known_outcome:
  assumes "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some r"
    and "Some (r', t) \<in> set_dist (execute receive_query_index_challenge s)"
  shows
    "r' = r \<and> PState t = PState s \<and>
     PTranscript t = PTranscript s \<and> s \<le> t"
proof -
  have out:
    "s \<le> t \<and>
     PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     fmlookup (HashMap t)
       (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some r'"
    by (rule receive_query_index_challenge_outcome[OF assms(2)])
  have old:
    "fmlookup (HashMap t)
       (QueryIndexChallenge (PQueryCounter s) (PState s)) = Some r"
    using assms(1) out
    by (meson protocol_merkle.hash_extension_lookup)
  show ?thesis
    using out old by auto
qed

lemma read_no_failure:
  assumes "PTranscript s \<noteq> []"
  shows "None \<notin> dom (dist (execute read s))"
  using assms
  unfolding read_def protocol_read_def assert_def
  by (intro no_failure_bindI) simp_all

lemma read_hash_extends:
  assumes "Some (x, t) \<in> set_dist (execute read s)"
  shows "s \<le> t"
proof (cases "PTranscript s")
  case Nil
  from assms obtain s0 u where
    get_s: "Some (s0, s0) \<in> set_dist (execute get s)"
    and assert_u:
      "Some ((), u) \<in>
        set_dist (execute (assert (PTranscript s0 \<noteq> [])) s0)"
    unfolding read_def protocol_read_def
    by (auto elim!: set_dist_bindE)
  have "s0 = s"
    using get_s by simp
  with Nil assert_u have False
    unfolding assert_def
    using throw_no_Some_set_dist by force
  then show ?thesis by simp
next
  case (Cons a list)
  then show ?thesis
    using assms
    unfolding read_def protocol_read_def assert_def
      less_eq_hash_ext_def less_eq_fmap_def modify_def
    by (auto elim!: set_dist_bindE)
qed

lemma receive_random_field_element_extends:
  assumes "Some (r, t) \<in>
    set_dist (execute receive_random_field_element s)"
  shows "s \<le> t"
  using receive_random_field_element_outcome[OF assms] by simp

lemma receive_tagged_random_field_element_extends:
  assumes "Some (r, t) \<in>
    set_dist (execute (receive_tagged_random_field_element tag) s)"
  shows "s \<le> t"
  using receive_tagged_random_field_element_outcome[OF assms] by simp

lemma receive_trace_fri_challenge_extends:
  assumes "Some (r, t) \<in> set_dist (execute receive_trace_fri_challenge s)"
  shows "s \<le> t"
  using receive_trace_fri_challenge_outcome[OF assms] by simp

lemma receive_composition_fri_challenge_extends:
  assumes "Some (r, t) \<in>
    set_dist (execute receive_composition_fri_challenge s)"
  shows "s \<le> t"
  using receive_composition_fri_challenge_outcome[OF assms] by simp

lemma receive_alpha_challenge_extends:
  assumes "Some (r, t) \<in> set_dist (execute receive_alpha_challenge s)"
  shows "s \<le> t"
  using receive_alpha_challenge_outcome[OF assms] by simp

lemma receive_query_index_challenge_extends:
  assumes "Some (r, t) \<in> set_dist (execute receive_query_index_challenge s)"
  shows "s \<le> t"
  using receive_query_index_challenge_outcome[OF assms] by simp

lemma send_outcome:
  assumes "Some ((), t) \<in> set_dist (execute (send x) s)"
  shows
    "t = s\<lparr>
      PState := concat (PState s) x,
      PTranscript := x # PTranscript s\<rparr>"
  using protocol_send_outcome[OF assms[unfolded send_def]] .

lemma read_cons_outcome:
  assumes "Some (y, t) \<in>
    set_dist (execute read (s\<lparr>PTranscript := x # xs\<rparr>))"
  shows
    "y = x \<and>
     t = s\<lparr>
       PState := concat (PState s) x,
       PTranscript := xs\<rparr>"
  using protocol_read_cons_outcome[OF assms[unfolded read_def]] .

lemma read_nonempty_outcome:
  assumes out: "Some (y, t) \<in> set_dist (execute read s)"
    and tr: "PTranscript s = x # xs"
  shows
    "y = x \<and>
     t = s\<lparr>PState := concat (PState s) x, PTranscript := xs\<rparr>"
proof -
  have s_eq: "s\<lparr>PTranscript := x # xs\<rparr> = s"
    using tr by (cases s) simp
  have out': "Some (y, t) \<in>
    set_dist (execute read (s\<lparr>PTranscript := x # xs\<rparr>))"
    using out unfolding s_eq .
  show ?thesis
    using read_cons_outcome[OF out'] tr by simp
qed

lemma random_then_read_cons_outcome:
  assumes lookup: "fmlookup (HashMap s) (FiatShamirChallenge (PState s)) = Some x"
    and outcome:
      "Some ((r, y), t) \<in>
        set_dist (execute
          (do {
            r \<leftarrow> receive_random_field_element;
            y \<leftarrow> read;
            return (r, y)
          }) (s\<lparr>PTranscript := x # xs\<rparr>))"
  shows
    "r = x \<and>
     y = x \<and>
     PState t = concat (PState s) x \<and>
     PTranscript t = xs"
proof -
  let ?s = "s\<lparr>PTranscript := x # xs\<rparr>"
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
  have lookup': "fmlookup (HashMap ?s) (FiatShamirChallenge (PState ?s)) = Some x"
    using lookup by simp
  have rand_res:
    "r = x \<and> PState r_state = PState s \<and> PTranscript r_state = x # xs"
    using receive_random_field_element_known_outcome[OF lookup' rand] by simp
  have r_state_update: "r_state\<lparr>PTranscript := x # xs\<rparr> = r_state"
    using rand_res by simp
  have read_y':
    "Some (y, t) \<in> set_dist (execute read (r_state\<lparr>PTranscript := x # xs\<rparr>))"
    using read_y unfolding r_state_update .
  have read_res:
    "y = x \<and> PState t = concat (PState s) x \<and> PTranscript t = xs"
    using read_cons_outcome[OF read_y'] rand_res by simp
  show ?thesis
    using rand_res read_res by simp
qed

lemma random_then_read_assert_no_failure:
  assumes lookup:
    "fmlookup (HashMap s) (FiatShamirChallenge (PState s)) = Some x"
  shows
    "None \<notin> dom (dist (execute
      (do {
        r \<leftarrow> receive_random_field_element;
        y \<leftarrow> read;
        assert (r = y);
        return y
      }) (s\<lparr>PTranscript := x # xs\<rparr>)))"
proof -
  let ?s = "s\<lparr>PTranscript := x # xs\<rparr>"
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
    have lookup_s:
      "fmlookup (HashMap ?s) (FiatShamirChallenge (PState ?s)) = Some x"
      using lookup by simp
    have tr_t: "PTranscript t = x # xs"
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
    "fmlookup (HashMap s)
      (FiatShamirChallenge (concat (PState s) x)) = Some r"
    and outcome:
      "Some ((y, r'), t) \<in>
        set_dist (execute
          (do {
            y \<leftarrow> read;
            r \<leftarrow> receive_random_field_element;
            return (y, r)
          }) (s\<lparr>PTranscript := x # xs\<rparr>))"
  shows
    "y = x \<and>
     r' = r \<and>
     PState t = concat (PState s) x \<and>
     PTranscript t = xs"
proof -
  let ?s = "s\<lparr>PTranscript := x # xs\<rparr>"
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
     read_state = s\<lparr>PState := concat (PState s) x, PTranscript := xs\<rparr>"
    using read_cons_outcome[OF read_y] by simp
  have rand_res:
    "r' = r \<and>
     PState t = concat (PState s) x \<and>
     PTranscript t = xs"
    using receive_random_field_element_known_outcome[OF _ rand] lookup read_res by simp
  show ?thesis
    using read_res rand_res by simp
qed

lemma mfold2_send_outcome:
  assumes "Some ((), t) \<in> set_dist (execute (mfold2 send xs) s)"
  shows
    "t = s\<lparr>
      PState := foldl concat (PState s) xs,
      PTranscript := rev xs @ PTranscript s\<rparr>"
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
    "s1 = s\<lparr>PState := concat (PState s) x,
      PTranscript := x # PTranscript s\<rparr>"
    using send_outcome[OF send_x] .
  show ?case
    using Cons.IH[OF rest] unfolding s1 by simp
qed

lemma ntimes_read_outcome:
  assumes "Some (ys, t) \<in>
    set_dist (execute (ntimes read (length xs)) (s\<lparr>PTranscript := xs\<rparr>))"
  shows
    "ys = xs \<and>
     t = s\<lparr>PState := foldl concat (PState s) xs, PTranscript := []\<rparr>"
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
        (s\<lparr>PTranscript := x # xs\<rparr>))"
    using Cons.prems by simp
  from prems' obtain y s1 where
    read_x: "Some (y, s1) \<in> set_dist (execute read (s\<lparr>PTranscript := x # xs\<rparr>))"
    and rest1:
      "Some (ys, t) \<in>
        set_dist (execute (ntimes read (length xs) \<bind> (\<lambda>ys. return (y # ys))) s1)"
    by (rule set_dist_bindE) blast
  from rest1 obtain ys' s2 where
    reads: "Some (ys', s2) \<in> set_dist (execute (ntimes read (length xs)) s1)"
    and ret: "Some (ys, t) \<in> set_dist (execute (return (y # ys')) s2)"
    by (auto elim!: set_dist_bindE)
  have read_res:
    "y = x \<and> s1 = s\<lparr>PState := concat (PState s) x, PTranscript := xs\<rparr>"
    using read_cons_outcome[OF read_x] .
  let ?s0 = "s\<lparr>PState := concat (PState s) x\<rparr>"
  have s1: "s1 = ?s0\<lparr>PTranscript := xs\<rparr>"
    using read_res by simp
  have tail:
    "ys' = xs \<and>
     s2 = ?s0\<lparr>PState := foldl concat (PState ?s0) xs, PTranscript := []\<rparr>"
    using Cons.IH[OF reads[unfolded s1]] .
  have ys_t: "ys = y # ys' \<and> t = s2"
    using ret by simp
  show ?case
    using read_res tail ys_t by simp
qed

theorem honest_transcript_replay_mfold2_ntimes:
  assumes init: "PTranscript s = []"
    and sent: "Some ((), sent) \<in> set_dist (execute (mfold2 send xs) s)"
    and replay:
      "Some (ys, replayed) \<in>
        set_dist (execute
          (ntimes read (length xs))
          (sent\<lparr>PState := PState s, PTranscript := rev (PTranscript sent)\<rparr>))"
  shows "ys = xs \<and> replayed = sent\<lparr>PTranscript := []\<rparr>"
proof -
  have sent_eq:
    "sent =
      s\<lparr>
        PState := foldl concat (PState s) xs,
        PTranscript := rev xs
      \<rparr>"
    using mfold2_send_outcome[OF sent] init by simp
  let ?replay_start = "sent\<lparr>PState := PState s\<rparr>"
  have start_eq:
    "sent\<lparr>PState := PState s, PTranscript := rev (PTranscript sent)\<rparr> =
      ?replay_start\<lparr>PTranscript := xs\<rparr>"
    using sent_eq by simp
  have replay_out:
    "ys = xs \<and>
     replayed =
      ?replay_start\<lparr>
        PState := foldl concat (PState ?replay_start) xs,
        PTranscript := []
      \<rparr>"
    using ntimes_read_outcome[OF replay[unfolded start_eq]] .
  then show ?thesis
    using sent_eq by simp
qed

lemma ntimes_read_prefix_outcome:
  assumes "Some (ys, t) \<in>
    set_dist (execute (ntimes read (length xs)) (s\<lparr>PTranscript := xs @ rest\<rparr>))"
  shows
    "ys = xs \<and>
     t = s\<lparr>PState := foldl concat (PState s) xs, PTranscript := rest\<rparr>"
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
        (s\<lparr>PTranscript := x # xs @ rest\<rparr>))"
    using Cons.prems by simp
  from prems' obtain y s1 where
    read_x: "Some (y, s1) \<in> set_dist (execute read (s\<lparr>PTranscript := x # xs @ rest\<rparr>))"
    and rest1:
      "Some (ys, t) \<in>
        set_dist (execute (ntimes read (length xs) \<bind> (\<lambda>ys. return (y # ys))) s1)"
    by (rule set_dist_bindE) blast
  from rest1 obtain ys' s2 where
    reads: "Some (ys', s2) \<in> set_dist (execute (ntimes read (length xs)) s1)"
    and ret: "Some (ys, t) \<in> set_dist (execute (return (y # ys')) s2)"
    by (auto elim!: set_dist_bindE)
  have read_res:
    "y = x \<and> s1 = s\<lparr>PState := concat (PState s) x, PTranscript := xs @ rest\<rparr>"
    using read_cons_outcome[OF read_x] .
  let ?s0 = "s\<lparr>PState := concat (PState s) x\<rparr>"
  have s1: "s1 = ?s0\<lparr>PTranscript := xs @ rest\<rparr>"
    using read_res by simp
  have tail:
    "ys' = xs \<and>
     s2 = ?s0\<lparr>PState := foldl concat (PState ?s0) xs, PTranscript := rest\<rparr>"
    using Cons.IH[OF reads[unfolded s1]] .
  have ys_t: "ys = y # ys' \<and> t = s2"
    using ret by simp
  show ?case
    using read_res tail ys_t by simp
qed

lemma ntimes_read_no_failure:
  assumes "n \<le> length (PTranscript s)"
  shows "None \<notin> dom (dist (execute (ntimes read n) s))"
  using assms
proof (induction n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have nonempty: "PTranscript s \<noteq> []"
    using Suc.prems by (cases "PTranscript s") auto
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
    obtain y ys where tr: "PTranscript s = y # ys"
      using nonempty by (cases "PTranscript s") auto
    have t_eq:
      "t = s\<lparr>PState := concat (PState s) y, PTranscript := ys\<rparr>"
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
    unfolding ntimes.simps
    by (rule no_failure_bindI[OF nf_read nf_cont])
qed

lemma ntimes_read_hash_extends:
  assumes "Some (xs, t) \<in> set_dist (execute (ntimes read n) s)"
  shows "s \<le> t"
  using assms
proof (induction n arbitrary: xs s t)
  case 0
  then show ?case by (simp add: hash_ext_refl)
next
  case (Suc n)
  from Suc.prems obtain x ys u where
    read: "Some (x, u) \<in> set_dist (execute read s)"
    and reads: "Some (ys, t) \<in> set_dist (execute (ntimes read n) u)"
    by (auto elim!: set_dist_bindE)
  have "s \<le> u"
    by (rule read_hash_extends[OF read])
  moreover have "u \<le> t"
    by (rule Suc.IH[OF reads])
  ultimately show ?case
    by (rule hash_ext_trans)
qed

lemma check_authentication_path_no_failure:
  "None \<notin> dom (dist (execute (check_authentication_path len i v path) s))"
  unfolding check_authentication_path_def protocol_check_authentication_path_def
proof (induction path arbitrary: len i v s)
  case Nil
  then show ?case
    by (simp add: protocol_hash_no_failure)
next
  case (Cons a path)
  show ?case
  proof (cases "i < len div 2")
    case True
    then show ?thesis
      by (simp add: no_failure_bindI protocol_hash_no_failure Cons.IH)
  next
    case False
    then show ?thesis
      by (simp add: no_failure_bindI protocol_hash_no_failure Cons.IH)
  qed
qed

lemma check_authentication_path_hash_extends:
  assumes outcome:
    "Some (h, t) \<in>
      set_dist (execute (check_authentication_path len i v path) s)"
  shows "s \<le> t"
  using outcome
  unfolding check_authentication_path_def protocol_check_authentication_path_def
proof (induction path arbitrary: len i v s h t)
  case Nil
  then have hash_step:
    "Some (h, t) \<in> set_dist (execute (hash (MerkleLeaf v)) s)"
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
        "Some (h, t) \<in> set_dist (execute (hash (MerkleNode x a)) u)"
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
        "Some (h, t) \<in> set_dist (execute (hash (MerkleNode a x)) u)"
      using False by (auto elim!: set_dist_bindE)
    have "s \<le> u"
      by (rule Cons.IH[OF rec])
    moreover have "u \<le> t"
      using hash_outcome(1)[OF hash] .
    ultimately show ?thesis
      by (rule hash_ext_trans)
  qed
qed

lemma check_authentication_path_preserves_channel:
  assumes "Some (h, t) \<in>
    set_dist (execute (check_authentication_path len i v path) s)"
  shows "PState t = PState s"
    and "PTranscript t = PTranscript s"
    and "PTraceFriCounter t = PTraceFriCounter s"
    and "PCompositionFriCounter t = PCompositionFriCounter s"
    and "PAlphaCounter t = PAlphaCounter s"
    and "PQueryCounter t = PQueryCounter s"
proof -
  have both:
    "PState t = PState s \<and>
     PTranscript t = PTranscript s \<and>
     PTraceFriCounter t = PTraceFriCounter s \<and>
     PCompositionFriCounter t = PCompositionFriCounter s \<and>
     PAlphaCounter t = PAlphaCounter s \<and>
     PQueryCounter t = PQueryCounter s"
    if outcome:
      "Some (h, t) \<in>
        set_dist (execute (check_authentication_path len i v path) s)"
    for len i v s h t
    using outcome
    unfolding check_authentication_path_def protocol_check_authentication_path_def
  proof (induction path arbitrary: len i v s h t)
    case Nil
    have hash_step:
      "Some (h, t) \<in> set_dist (execute (hash (MerkleLeaf v)) s)"
      using Nil.prems by simp
    show ?case
      using hash_channel_preserves(1)[OF hash_step]
        hash_channel_preserves(2)[OF hash_step]
        hash_channel_preserves(3)[OF hash_step]
        hash_channel_preserves(4)[OF hash_step]
        hash_channel_preserves(5)[OF hash_step]
        hash_channel_preserves(6)[OF hash_step]
      by simp
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
          "Some (h, t) \<in> set_dist (execute (hash (MerkleNode x a)) u)"
        using True by (auto elim!: set_dist_bindE)
      have rec_pres:
        "PState u = PState s \<and>
         PTranscript u = PTranscript s \<and>
         PTraceFriCounter u = PTraceFriCounter s \<and>
         PCompositionFriCounter u = PCompositionFriCounter s \<and>
         PAlphaCounter u = PAlphaCounter s \<and>
         PQueryCounter u = PQueryCounter s"
        using Cons.IH[OF rec] .
      have hash_pres:
        "PState t = PState u \<and>
         PTranscript t = PTranscript u \<and>
         PTraceFriCounter t = PTraceFriCounter u \<and>
         PCompositionFriCounter t = PCompositionFriCounter u \<and>
         PAlphaCounter t = PAlphaCounter u \<and>
         PQueryCounter t = PQueryCounter u"
        using hash_channel_preserves(1)[OF hash]
          hash_channel_preserves(2)[OF hash]
          hash_channel_preserves(3)[OF hash]
          hash_channel_preserves(4)[OF hash]
          hash_channel_preserves(5)[OF hash]
          hash_channel_preserves(6)[OF hash] by simp
      show ?thesis
        using rec_pres hash_pres by simp
    next
      case False
      from Cons.prems obtain x u where
        rec:
          "Some (x, u) \<in>
            set_dist (execute
              (protocol_merkle.check_authentication_path
                (len div 2) (i - len div 2) (MerkleLeaf v) path) s)"
      and hash:
          "Some (h, t) \<in> set_dist (execute (hash (MerkleNode a x)) u)"
        using False by (auto elim!: set_dist_bindE)
      have rec_pres:
        "PState u = PState s \<and>
         PTranscript u = PTranscript s \<and>
         PTraceFriCounter u = PTraceFriCounter s \<and>
         PCompositionFriCounter u = PCompositionFriCounter s \<and>
         PAlphaCounter u = PAlphaCounter s \<and>
         PQueryCounter u = PQueryCounter s"
        using Cons.IH[OF rec] .
      have hash_pres:
        "PState t = PState u \<and>
         PTranscript t = PTranscript u \<and>
         PTraceFriCounter t = PTraceFriCounter u \<and>
         PCompositionFriCounter t = PCompositionFriCounter u \<and>
         PAlphaCounter t = PAlphaCounter u \<and>
         PQueryCounter t = PQueryCounter u"
        using hash_channel_preserves(1)[OF hash]
          hash_channel_preserves(2)[OF hash]
          hash_channel_preserves(3)[OF hash]
          hash_channel_preserves(4)[OF hash]
          hash_channel_preserves(5)[OF hash]
          hash_channel_preserves(6)[OF hash] by simp
      show ?thesis
        using rec_pres hash_pres by simp
    qed
  qed
  show "PState t = PState s"
    using both[OF assms] by simp
  show "PTranscript t = PTranscript s"
    using both[OF assms] by simp
  show "PTraceFriCounter t = PTraceFriCounter s"
    using both[OF assms] by simp
  show "PCompositionFriCounter t = PCompositionFriCounter s"
    using both[OF assms] by simp
  show "PAlphaCounter t = PAlphaCounter s"
    using both[OF assms] by simp
  show "PQueryCounter t = PQueryCounter s"
    using both[OF assms] by simp
qed

lemma check_authentication_path_preserves_non_merkle_lookup:
  assumes outcome: "Some (h, t) \<in>
    set_dist (execute (check_authentication_path len i v path) s)"
    and not_leaf: "\<And>x. y \<noteq> MerkleLeaf x"
    and not_node: "\<And>x z. y \<noteq> MerkleNode x z"
  shows "fmlookup (HashMap t) y = fmlookup (HashMap s) y"
  using outcome
  unfolding check_authentication_path_def protocol_check_authentication_path_def
proof (induction path arbitrary: len i v s h t)
  case Nil
  have hash_step:
    "Some (h, t) \<in> set_dist (execute (hash (MerkleLeaf v)) s)"
    using Nil.prems by simp
  show ?case
    by (rule protocol_hash_preserves_other_lookup[OF hash_step])
      (rule not_leaf)
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
      and hash_step:
        "Some (h, t) \<in> set_dist (execute (hash (MerkleNode x a)) u)"
      using True by (auto elim!: set_dist_bindE)
    have rec_pres:
      "fmlookup (HashMap u) y = fmlookup (HashMap s) y"
      by (rule Cons.IH[OF rec])
    have hash_pres:
      "fmlookup (HashMap t) y = fmlookup (HashMap u) y"
      by (rule protocol_hash_preserves_other_lookup[OF hash_step])
        (rule not_node)
    show ?thesis
      using hash_pres rec_pres by simp
  next
    case False
    from Cons.prems obtain x u where
      rec:
        "Some (x, u) \<in>
          set_dist (execute
            (protocol_merkle.check_authentication_path
              (len div 2) (i - len div 2) (MerkleLeaf v) path) s)"
      and hash_step:
        "Some (h, t) \<in> set_dist (execute (hash (MerkleNode a x)) u)"
      using False by (auto elim!: set_dist_bindE)
    have rec_pres:
      "fmlookup (HashMap u) y = fmlookup (HashMap s) y"
      by (rule Cons.IH[OF rec])
    have hash_pres:
      "fmlookup (HashMap t) y = fmlookup (HashMap u) y"
      by (rule protocol_hash_preserves_other_lookup[OF hash_step])
        (rule not_node)
    show ?thesis
      using hash_pres rec_pres by simp
  qed
qed

lemma check_authentication_path_preserves_challenge_lookups:
  assumes outcome: "Some (h, t) \<in>
    set_dist (execute (check_authentication_path len i v path) s)"
  shows
    "fmlookup (HashMap t) (AlphaChallenge j x) =
      fmlookup (HashMap s) (AlphaChallenge j x)"
    "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
    "fmlookup (HashMap t) (TraceFriChallenge j x) =
      fmlookup (HashMap s) (TraceFriChallenge j x)"
    "fmlookup (HashMap t) (CompositionFriChallenge j x) =
      fmlookup (HashMap s) (CompositionFriChallenge j x)"
proof -
  show "fmlookup (HashMap t) (AlphaChallenge j x) =
      fmlookup (HashMap s) (AlphaChallenge j x)"
    by (rule check_authentication_path_preserves_non_merkle_lookup[
        OF outcome]) simp_all
  show "fmlookup (HashMap t) (QueryIndexChallenge j x) =
      fmlookup (HashMap s) (QueryIndexChallenge j x)"
    by (rule check_authentication_path_preserves_non_merkle_lookup[
        OF outcome]) simp_all
  show "fmlookup (HashMap t) (TraceFriChallenge j x) =
      fmlookup (HashMap s) (TraceFriChallenge j x)"
    by (rule check_authentication_path_preserves_non_merkle_lookup[
        OF outcome]) simp_all
  show "fmlookup (HashMap t) (CompositionFriChallenge j x) =
      fmlookup (HashMap s) (CompositionFriChallenge j x)"
    by (rule check_authentication_path_preserves_non_merkle_lookup[
        OF outcome]) simp_all
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
      }) (s\<lparr>PTranscript := v # get_authentication_path (length xs) i tree @ rest\<rparr>)))"
proof -
  let ?path = "get_authentication_path (length xs) i tree"
  let ?s = "s\<lparr>PTranscript := v # ?path @ rest\<rparr>"
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
      "s1 = s\<lparr>PState := concat (PState s) v, PTranscript := ?path @ rest\<rparr>"
      using read_cons_outcome[OF read_qh] by simp
    have enough_path: "floor_log (length xs) \<le> length (PTranscript s1)"
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
        by (rule no_failure_bindI[OF nf_check]) simp
    qed
    show "None \<notin> dom
      (dist (execute
        (ntimes read (floor_log (length xs)) \<bind>
          (\<lambda>qh_path. check_authentication_path (length xs) i qh qh_path \<bind>
            (\<lambda>ap. return (qh, qh_path, ap)))) s1))"
      by (rule no_failure_bindI[OF nf_reads nf_after_reads])
  qed
  have prefix_nf:
    "None \<notin> dom (dist (execute ?prefix ?s))"
    by (rule no_failure_bindI[OF nf_read nf_after_read])
  have prefix_out:
    "\<And>res t. Some (res, t) \<in> set_dist (execute ?prefix ?s) \<Longrightarrow>
      case res of (qh, qh_path, ap) \<Rightarrow> ap = fr"
  proof -
    fix res t
    assume out: "Some (res, t) \<in> set_dist (execute ?prefix ?s)"
    obtain qh qh_path ap where res_eq: "res = (qh, qh_path, ap)"
      by (cases res) auto
    from out[unfolded res_eq] obtain s1 s2 where
      read_qh: "Some (qh, s1) \<in> set_dist (execute read ?s)"
      and reads:
        "Some (qh_path, s2) \<in>
          set_dist (execute (ntimes read (floor_log (length xs))) s1)"
      and check:
        "Some (ap, t) \<in>
          set_dist (execute (check_authentication_path (length xs) i qh qh_path) s2)"
      by (auto elim!: set_dist_bindE)
    have qh_eq: "qh = v"
      using read_cons_outcome[OF read_qh] by simp
    have s1_eq:
      "s1 = s\<lparr>PState := concat (PState s) v, PTranscript := ?path @ rest\<rparr>"
      using read_cons_outcome[OF read_qh] by simp
    have reads_out:
      "qh_path = ?path"
      using ntimes_read_prefix_outcome[OF reads[unfolded path_len[symmetric] s1_eq]]
      by simp
    have s_start: "s \<le> ?s"
      unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
    have start_s1: "?s \<le> s1"
      by (rule read_hash_extends[OF read_qh])
    have s1_s2: "s1 \<le> s2"
      by (rule ntimes_read_hash_extends[OF reads])
    have s0_s2: "s0 \<le> s2"
      using ext s_start start_s1 s1_s2 by (meson hash_ext_trans)
    have "ap = value tree"
      using check_created_tree_outcome
        [OF created len_pow idx leaf s0_s2 check[unfolded qh_eq reads_out]]
      by simp
    then show "case res of (qh, qh_path, ap) \<Rightarrow> ap = fr"
      unfolding res_eq root by simp
  qed
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
  proof (rule no_failure_bindI[OF prefix_nf])
    fix res t
    assume out: "Some (res, t) \<in> set_dist (execute ?prefix ?s)"
    obtain qh qh_path ap where res_eq: "res = (qh, qh_path, ap)"
      by (cases res) auto
    have ap_eq: "ap = fr"
      using prefix_out[OF out] unfolding res_eq by simp
    show "None \<notin> dom
      (dist (execute
        ((case res of (qh, qh_path, ap) \<Rightarrow>
          assert (ap = fr) \<bind> (\<lambda>_. return qh))) t))"
      unfolding res_eq ap_eq assert_def by simp
  qed
qed

end

end
