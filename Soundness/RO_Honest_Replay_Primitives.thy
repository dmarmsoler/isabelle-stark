(*  License: BSD-3-Clause *)
theory RO_Honest_Replay_Primitives
  imports Staged_Security_Experiment_RO_Verify_Header_Replay
begin

section \<open>Hash-only reconstruction in persistent oracle maps\<close>

text \<open>These are proof helpers for an explicitly chosen honest producer.
  They do not restrict the adversary model. Re-querying a known key returns
  its stored answer and leaves the entire channel unchanged; neither
  injectivity nor freshness of hash outputs is required.\<close>

primrec shadow_absorb
  :: "'f::finite list \<Rightarrow> 'f \<Rightarrow> ('f, 'f protocol_channel) state_monad"
where
  "shadow_absorb [] cursor = return cursor"
| "shadow_absorb (x#xs) cursor =
    (hash (TranscriptAbsorb cursor x) \<bind> shadow_absorb xs)"

context soundness
begin

lemma shadow_absorb_controlled:
  "controlled_ro_program (length xs) (shadow_absorb xs cursor)"
  by (induction xs arbitrary: cursor) auto

lemma shadow_absorb_preserves_fields:
  "protocol_fields_preserving (shadow_absorb xs cursor)"
  by (rule controlled_ro_program_preserves_protocol_fields[OF shadow_absorb_controlled])

end

lemma hash_known_wp:
  assumes known: "fmlookup (HashMap s) key = Some y"
  shows "wp (hash key) Q s = Q (Some (y,s))"
proof -
  have update: "fmupd key y (HashMap s) = HashMap s"
    by (rule fmap_ext) (auto simp: known)
  show ?thesis using known update
    by (simp add: wp_hash hash_dist_def option_default_dist_def)
qed

lemma shadow_absorb_known_wp:
  assumes chain: "ro_absorb_lookup_chain s cursor xs final"
  shows "wp (shadow_absorb xs cursor) Q s = Q (Some (final,s))"
  using chain
proof (induction xs arbitrary: cursor)
  case Nil
  then show ?case by (simp add: wp_return)
next
  case (Cons x xs)
  then obtain nxt where key:
    "fmlookup (HashMap s) (TranscriptAbsorb cursor x) = Some nxt"
    and tail: "ro_absorb_lookup_chain s nxt xs final" by auto
  show ?case
    by (simp add: wp_bind hash_known_wp[OF key] Cons.IH[OF tail])
qed

lemma shadow_absorb_known_extension_wp:
  assumes chain: "ro_absorb_lookup_chain sent cursor xs final" and ext: "sent \<le> s"
  shows "wp (shadow_absorb xs cursor) Q s = Q (Some (final,s))"
  by (rule shadow_absorb_known_wp[OF ro_absorb_lookup_chain_mono[OF chain ext]])

lemma recorded_absorption_has_frozen_function:
  fixes s :: "('f::zero, 'a) protocol_channel_scheme"
  assumes chain: "ro_absorb_lookup_chain s cursor xs final"
  shows "foldl (\<lambda>st x. case fmlookup (HashMap s) (TranscriptAbsorb st x)
      of None \<Rightarrow> 0 | Some y \<Rightarrow> y) cursor xs = final"
  using chain by (induction xs arbitrary: cursor) auto

definition shadow_alpha
  :: "nat \<Rightarrow> 'f::finite \<Rightarrow> ('f \<times> 'f, 'f protocol_channel) state_monad"
where
  "shadow_alpha i cursor =
    (hash (AlphaChallenge i cursor) \<bind> (\<lambda>a.
      hash (TranscriptAbsorb cursor a) \<bind> (\<lambda>final.
        return (a, final))))"

context soundness
begin

lemma shadow_alpha_controlled:
  "controlled_ro_program 2 (shadow_alpha i cursor)"
  unfolding shadow_alpha_def numeral_2_eq_2 by auto

lemma shadow_alpha_preserves_fields:
  "protocol_fields_preserving (shadow_alpha i cursor)"
  by (rule controlled_ro_program_preserves_protocol_fields[OF shadow_alpha_controlled])

end

lemma shadow_alpha_known_wp:
  assumes challenge: "fmlookup (HashMap s) (AlphaChallenge i cursor) = Some a"
    and absorption: "fmlookup (HashMap s) (TranscriptAbsorb cursor a) = Some final"
  shows "wp (shadow_alpha i cursor) Q s = Q (Some ((a,final),s))"
  unfolding shadow_alpha_def
  by (simp add: wp_bind wp_return hash_known_wp[OF challenge] hash_known_wp[OF absorption])

context soundness
begin

lemma shadow_alpha_replays_actual_round:
  assumes received: "Some (a,t) \<in> set_dist (execute receive_alpha_challenge s)"
    and recorded: "Some ((),u) \<in> set_dist (execute (ro_record_staged_message a) t)"
    and extension: "u \<le> v"
  shows "wp (shadow_alpha (PAlphaCounter s) (PState s)) Q v =
    Q (Some ((a,PState u),v))"
proof -
  have r: "t \<le> u"
    and absorb: "fmlookup (HashMap u) (TranscriptAbsorb (PState t) a) = Some (PState u)"
    using ro_record_staged_message_absorb_lookup_state[OF recorded] by auto
  have cursor: "PState t = PState s"
    and key: "fmlookup (HashMap t) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    using receive_alpha_challenge_outcome[OF received] by auto
  have challenge_u: "fmlookup (HashMap u) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    by (rule hash_extension_lookup[OF key r])
  have challenge_v: "fmlookup (HashMap v) (AlphaChallenge (PAlphaCounter s) (PState s)) = Some a"
    by (rule hash_extension_lookup[OF challenge_u extension])
  have absorb_v: "fmlookup (HashMap v) (TranscriptAbsorb (PState s) a) = Some (PState u)"
    using hash_extension_lookup[OF absorb extension] cursor by simp
  show ?thesis by (rule shadow_alpha_known_wp[OF challenge_v absorb_v])
qed

end

text \<open>Replayability is an exact weakest-precondition identity for every
  postcondition and every extension of a reached oracle map.\<close>

definition replayable_ro
  :: "('a, 'f::finite protocol_channel) state_monad \<Rightarrow> bool"
where
  "replayable_ro m \<longleftrightarrow> (\<forall>s x t u Q.
    Some (x,t) \<in> set_dist (execute m s) \<longrightarrow> t \<le> u \<longrightarrow>
    wp m Q u = Q (Some (x,u)))"

context soundness
begin

lemma replayable_ro_return:
  "replayable_ro (return x)"
  unfolding replayable_ro_def by (simp add: wp_return)

lemma replayable_ro_hash:
  "replayable_ro (hash key)"
  unfolding replayable_ro_def
  by (meson hash_known_wp protocol_merkle.hash_outcome(2) hash_extension_lookup)

lemma replayable_ro_bind:
  assumes replay_m: "replayable_ro m"
    and replay_k: "\<And>x. replayable_ro (k x)"
    and extends_k: "\<And>x. hash_extension_preserving (k x)"
  shows "replayable_ro (m \<bind> k)"
proof (unfold replayable_ro_def, intro allI impI)
  fix s x t u Q
  assume out: "Some (x,t) \<in> set_dist (execute (m \<bind> k) s)"
    and ext: "t \<le> u"
  obtain y v where first: "Some (y,v) \<in> set_dist (execute m s)"
    and last: "Some (x,t) \<in> set_dist (execute (k y) v)"
    using out by (auto elim!: set_dist_bindE)
  have vt: "v \<le> t" using extends_k[of y] last
    unfolding hash_extension_preserving_def by blast
  have vu: "v \<le> u" by (rule hash_ext_trans[OF vt ext])
  have first_wp: "wp m F u = F (Some (y,u))" for F
    using replay_m first vu unfolding replayable_ro_def by blast
  have last_wp: "wp (k y) Q u = Q (Some (x,u))"
    using replay_k[of y] last ext unfolding replayable_ro_def by blast
  show "wp (m \<bind> k) Q u = Q (Some (x,u))"
    by (simp add: wp_bind first_wp last_wp)
qed

lemma hash_extension_preserving_raw_create:
  "hash_extension_preserving (protocol_merkle.create xs)"
  unfolding hash_extension_preserving_def
  by (auto dest: protocol_merkle.create_outcome)

lemma replayable_ro_create:
  fixes xs :: "'f protocol_hash_input list"
  shows "replayable_ro (protocol_merkle.create xs)"
proof (induction xs rule: protocol_merkle.create.induct)
  case 1
  show ?case by (simp add: replayable_ro_return)
next
  case (2 x)
  show ?case
    apply simp
    apply (rule replayable_ro_bind)
      apply (rule replayable_ro_hash)
     apply (rule replayable_ro_return)
    apply (rule hash_extension_preserving_return)
    done
next
  case (3 v vb vc)
  show ?case
    apply (subst protocol_merkle.create.simps(3))
    unfolding Let_def
    using 3
    by (auto intro!: replayable_ro_bind replayable_ro_hash replayable_ro_return
      hash_extension_preserving_bind hash_extension_preserving_hash
      hash_extension_preserving_return hash_extension_preserving_raw_create)
qed

lemma replayable_ro_protocol_create:
  fixes xs :: "'f list"
  shows "replayable_ro (protocol_create xs)"
  unfolding protocol_create_def by (rule replayable_ro_create)

lemma controlled_ro_create:
  "controlled_ro_program (2 * length xs - 1) (protocol_merkle.create xs)"
proof (induction xs rule: protocol_merkle.create.induct)
  case 1
  show ?case by auto
next
  case (2 x)
  show ?case by auto
next
  case (3 x y zs)
  let ?xs = "x # y # zs"
  let ?i = "length ?xs div 2"
  have lpos: "0 < length (take ?i ?xs)" and rpos: "0 < length (drop ?i ?xs)" by auto
  have budget:
    "(2 * length (take ?i ?xs) - 1) +
      ((2 * length (drop ?i ?xs) - 1) + 1) = 2 * length ?xs - 1"
    using lpos rpos by simp
  have control:
    "controlled_ro_program ((2 * length (take ?i ?xs) - 1) +
      ((2 * length (drop ?i ?xs) - 1) + 1))
      (protocol_merkle.create (take ?i ?xs) \<bind> (\<lambda>l.
       protocol_merkle.create (drop ?i ?xs) \<bind> (\<lambda>r.
       hash (MerkleNode (value l) (value r)) \<bind> (\<lambda>h.
       return (Node l h r)))))"
    by (intro controlled_ro_program.Bind allI 3)
      (auto simp: numeral_2_eq_2)
  show ?case using control budget by (simp add: Let_def)
qed

lemma controlled_ro_protocol_create:
  "controlled_ro_program (2 * length xs - 1) (protocol_create xs)"
  unfolding protocol_create_def using controlled_ro_create[of "map MerkleLeaf xs"] by simp

text \<open>The following internal inductive predicate permits only return and
  hash operations, with a finite query bound. Its heterogeneous composition
  rule is derived by induction, and every such program satisfies the existing
  controlled-program predicate. No interface or public premise is changed.\<close>

inductive hash_only_ro
  :: "nat \<Rightarrow> ('a, 'f protocol_channel) state_monad \<Rightarrow> bool"
where
  Pure: "hash_only_ro 0 (return x)"
| Ask: "(\<And>y. hash_only_ro q (k y)) \<Longrightarrow>
    hash_only_ro (Suc q) (hash x \<bind> k)"
| Bound: "hash_only_ro q m \<Longrightarrow> q \<le> r \<Longrightarrow> hash_only_ro r m"

lemma hash_only_ro_bind:
  fixes m :: "('a, 'f protocol_channel) state_monad"
    and k :: "'a \<Rightarrow> ('b, 'f protocol_channel) state_monad"
  assumes m: "hash_only_ro q m"
    and k: "\<And>x. hash_only_ro r (k x)"
  shows "hash_only_ro (q+r) (m \<bind> k)"
  using m k
proof (induction arbitrary: r k rule: hash_only_ro.induct)
  case (Pure x)
  then show ?case by simp
next
  case (Ask q f x)
  show ?case
    using Ask.IH[OF Ask.prems]
    by (simp add: sm_bind_assoc hash_only_ro.Ask)
next
  case (Bound q m b)
  show ?case
    by (rule hash_only_ro.Bound[OF Bound.IH[OF Bound.prems]])
      (use Bound.hyps(2) in simp)
qed

lemma hash_only_ro_controlled:
  assumes "hash_only_ro q m"
  shows "controlled_ro_program q m"
  using assms by (induction rule: hash_only_ro.induct)
    (auto intro: controlled_ro_program.Weaken)

declare hash_only_ro.Pure[intro] hash_only_ro.Ask[intro]

lemma hash_only_ro_create:
  "hash_only_ro (2 * length xs - 1) (protocol_merkle.create xs)"
proof (induction xs rule: protocol_merkle.create.induct)
  case 1
  show ?case by auto
next
  case (2 x)
  show ?case by auto
next
  case (3 x y zs)
  let ?xs = "x # y # zs"
  let ?i = "length ?xs div 2"
  have lpos: "0 < length (take ?i ?xs)" and rpos: "0 < length (drop ?i ?xs)" by auto
  have budget:
    "(2 * length (take ?i ?xs) - 1) +
      ((2 * length (drop ?i ?xs) - 1) + 1) = 2 * length ?xs - 1"
    using lpos rpos by simp
  have control:
    "hash_only_ro ((2 * length (take ?i ?xs) - 1) +
      ((2 * length (drop ?i ?xs) - 1) + 1))
      (protocol_merkle.create (take ?i ?xs) \<bind> (\<lambda>l.
       protocol_merkle.create (drop ?i ?xs) \<bind> (\<lambda>r.
       hash (MerkleNode (value l) (value r)) \<bind> (\<lambda>h.
       return (Node l h r)))))"
    by (intro hash_only_ro_bind 3)
      (auto simp: numeral_2_eq_2)
  show ?case using control budget by (simp add: Let_def)
qed

lemma hash_only_ro_protocol_create:
  "hash_only_ro (2 * length xs - 1) (protocol_create xs)"
  unfolding protocol_create_def using hash_only_ro_create[of "map MerkleLeaf xs"] by simp


lemma hash_only_ro_map:
  assumes "hash_only_ro q m"
  shows "hash_only_ro q (m \<bind> (\<lambda>x. return (f x)))"
proof -
  have "hash_only_ro (q+0) (m \<bind> (\<lambda>x. return (f x)))"
    by (rule hash_only_ro_bind[OF assms]) (rule hash_only_ro.Pure)
  then show ?thesis by simp
qed

lemma hash_only_ro_shadow_alpha:
  "hash_only_ro 2 (shadow_alpha i cursor)"
  unfolding shadow_alpha_def numeral_2_eq_2
  by (intro hash_only_ro.Ask hash_only_ro.Pure)


end

end
