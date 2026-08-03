(*  Title:      Stark/Controlled_RO.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Controlled_RO
  imports
    Soundness_Oracle
begin

context soundness
begin

text \<open>
  Controlled random-oracle programs provide a capability-safe interface for
  attacker stages.  The constructors expose ordinary probabilistic
  computation and oracle queries, but no operation that can directly modify
  the oracle map or protocol-local channel fields.
\<close>

inductive controlled_ro_program
  :: "nat \<Rightarrow>
      ('r, 'f protocol_channel) state_monad \<Rightarrow> bool"
where
  Return[intro]:
    "controlled_ro_program 0 (return x)"
| Fail[intro]:
    "controlled_ro_program 0 throw"
| Sample[intro]:
    "controlled_ro_program 0 (lift (\<lambda>_. d))"
| Query[intro]:
    "(\<forall>y. controlled_ro_program q (k y)) \<Longrightarrow>
      controlled_ro_program (Suc q)
        ((hash x :: ('f, 'f protocol_channel) state_monad)
          \<bind> k)"
| Bind[intro]:
    "controlled_ro_program q m \<Longrightarrow>
      (\<forall>x. controlled_ro_program r (k x)) \<Longrightarrow>
      controlled_ro_program (q + r) (m \<bind> k)"
| Weaken:
    "controlled_ro_program q m \<Longrightarrow> q \<le> r \<Longrightarrow>
      controlled_ro_program r m"

lemma hash_map_preserving_throw:
  "hash_map_preserving
    (throw :: ('r, 'f protocol_channel) state_monad)"
  unfolding hash_map_preserving_def
  by (simp add: throw_no_outcome)

lemma hash_map_preserving_return:
  "hash_map_preserving
    (return x :: ('r, 'f protocol_channel) state_monad)"
  unfolding hash_map_preserving_def by simp

lemma hash_map_preserving_state_independent_sample:
  "hash_map_preserving
    (lift (\<lambda>_. d) ::
      ('r, 'f protocol_channel) state_monad)"
  unfolding hash_map_preserving_def lift.rep_eq lift_dist_def
  by (auto simp: set_dist_dist_map)

definition protocol_fields_preserving
  :: "('r, 'f protocol_channel) state_monad \<Rightarrow> bool"
  where
    "protocol_fields_preserving m \<longleftrightarrow>
      (\<forall>s x t.
        Some (x, t) \<in> set_dist (execute m s) \<longrightarrow>
        PState t = PState s \<and>
        PTranscript t = PTranscript s \<and>
        PTraceFriCounter t = PTraceFriCounter s \<and>
        PCompositionFriCounter t = PCompositionFriCounter s \<and>
        PAlphaCounter t = PAlphaCounter s \<and>
        PQueryCounter t = PQueryCounter s)"

lemma controlled_ro_program_preserves_protocol_fields:
  assumes "controlled_ro_program q m"
  shows "protocol_fields_preserving m"
  using assms
proof (induction rule: controlled_ro_program.induct)
  case (Return x)
  then show ?case
    unfolding protocol_fields_preserving_def by simp
next
  case Fail
  then show ?case
    unfolding protocol_fields_preserving_def
    by (simp add: throw_no_outcome)
next
  case (Sample d)
  then show ?case
    unfolding protocol_fields_preserving_def lift.rep_eq lift_dist_def
    by (auto simp: set_dist_dist_map)
next
  case (Query q k x)
  show ?case
    unfolding protocol_fields_preserving_def
  proof (intro allI impI)
    fix s result t
    assume outcome:
      "Some (result, t) \<in>
        set_dist
          (execute
            ((hash x :: ('f, 'f protocol_channel) state_monad) \<bind> k) s)"
    then obtain h u where
      hash_out:
        "Some (h, u) \<in>
          set_dist
            (execute (hash x :: ('f, 'f protocol_channel) state_monad) s)"
      and rest: "Some (result, t) \<in> set_dist (execute (k h) u)"
      by (auto elim!: set_dist_bindE)
    have fields_u:
      "PState u = PState s \<and>
       PTranscript u = PTranscript s \<and>
       PTraceFriCounter u = PTraceFriCounter s \<and>
       PCompositionFriCounter u = PCompositionFriCounter s \<and>
       PAlphaCounter u = PAlphaCounter s \<and>
       PQueryCounter u = PQueryCounter s"
      using hash_channel_preserves[OF hash_out] by simp
    have preserving_k: "protocol_fields_preserving (k h)"
      using Query.IH by blast
    have fields_t:
      "PState t = PState u \<and>
       PTranscript t = PTranscript u \<and>
       PTraceFriCounter t = PTraceFriCounter u \<and>
       PCompositionFriCounter t = PCompositionFriCounter u \<and>
       PAlphaCounter t = PAlphaCounter u \<and>
       PQueryCounter t = PQueryCounter u"
      using preserving_k rest
      unfolding protocol_fields_preserving_def by blast
    show
      "PState t = PState s \<and>
       PTranscript t = PTranscript s \<and>
       PTraceFriCounter t = PTraceFriCounter s \<and>
       PCompositionFriCounter t = PCompositionFriCounter s \<and>
       PAlphaCounter t = PAlphaCounter s \<and>
       PQueryCounter t = PQueryCounter s"
      using fields_u fields_t by simp
  qed
next
  case (Bind q m r k)
  show ?case
    unfolding protocol_fields_preserving_def
  proof (intro allI impI)
    fix s result t
    assume outcome:
      "Some (result, t) \<in> set_dist (execute (m \<bind> k) s)"
    then obtain x u where
      first: "Some (x, u) \<in> set_dist (execute m s)"
      and rest: "Some (result, t) \<in> set_dist (execute (k x) u)"
      by (auto elim!: set_dist_bindE)
    have fields_u:
      "PState u = PState s \<and>
       PTranscript u = PTranscript s \<and>
       PTraceFriCounter u = PTraceFriCounter s \<and>
       PCompositionFriCounter u = PCompositionFriCounter s \<and>
       PAlphaCounter u = PAlphaCounter s \<and>
       PQueryCounter u = PQueryCounter s"
      using Bind.IH(1) first
      unfolding protocol_fields_preserving_def by blast
    have preserving_k: "protocol_fields_preserving (k x)"
      using Bind.IH(2) by blast
    have fields_t:
      "PState t = PState u \<and>
       PTranscript t = PTranscript u \<and>
       PTraceFriCounter t = PTraceFriCounter u \<and>
       PCompositionFriCounter t = PCompositionFriCounter u \<and>
       PAlphaCounter t = PAlphaCounter u \<and>
       PQueryCounter t = PQueryCounter u"
      using preserving_k rest
      unfolding protocol_fields_preserving_def by blast
    show
      "PState t = PState s \<and>
       PTranscript t = PTranscript s \<and>
       PTraceFriCounter t = PTraceFriCounter s \<and>
       PCompositionFriCounter t = PCompositionFriCounter s \<and>
       PAlphaCounter t = PAlphaCounter s \<and>
       PQueryCounter t = PQueryCounter s"
      using fields_u fields_t by simp
  qed
next
  case (Weaken q m r)
  then show ?case by simp
qed

lemma hash_range_budget_throw:
  "hash_range_budget 0
    (throw :: ('r, 'f protocol_channel) state_monad)"
  unfolding hash_range_budget_def
  by (simp add: throw_no_outcome)

lemma hash_collision_budget_throw:
  "hash_collision_budget 0
    (throw :: ('r, 'f protocol_channel) state_monad)"
  unfolding hash_collision_budget_def wp_event_def wp_def
    throw.rep_eq dist_throw_def dist_delta_dist delta_map_def
    hash_collision_budget_value_def hash_new_collision_event_def
  by simp

lemma hash_target_program_throw:
  "hash_target_program B 0
    (throw :: ('r, 'f protocol_channel) state_monad)"
  by (rule hash_map_preserving_imp_hash_target_program_zero)
    (rule hash_map_preserving_throw)

lemma hash_range_budget_state_independent_sample:
  "hash_range_budget 0
    (lift (\<lambda>_. d) ::
      ('r, 'f protocol_channel) state_monad)"
  unfolding hash_range_budget_def lift.rep_eq lift_dist_def
  by (auto simp: set_dist_dist_map hash_map_output_values_def)

lemma hash_map_preserving_imp_hash_collision_budget_zero:
  fixes m :: "('r, 'f protocol_channel) state_monad"
  assumes preserving: "hash_map_preserving m"
  shows "hash_collision_budget 0 m"
  unfolding hash_collision_budget_def
proof (intro allI impI)
  fix s :: "'f protocol_channel"
  assume clean: "\<not> hash_map_output_collision s"
  have no_event:
    "\<And>out. out \<in> set_dist (execute m s) \<Longrightarrow>
      \<not> hash_new_collision_event s out"
  proof -
    fix out
    assume support: "out \<in> set_dist (execute m s)"
    show "\<not> hash_new_collision_event s out"
    proof (cases out)
      case None
      then show ?thesis
        unfolding hash_new_collision_event_def by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) simp
      have same: "HashMap t = HashMap s"
        using preserving support Some xt
        unfolding hash_map_preserving_def by blast
      show ?thesis
        using clean same Some xt
        unfolding hash_new_collision_event_def
          hash_map_new_output_collision_def hash_map_output_collision_def
        by simp
    qed
  qed
  have no_event_dom:
    "\<And>out. out \<in> dom (dist (execute m s)) \<Longrightarrow>
      \<not> hash_new_collision_event s out"
    using no_event unfolding set_dist_def by blast
  have "wp_event m (hash_new_collision_event s) s = 0"
    unfolding wp_event_def wp_def dist_expect_def
    by (intro sum.neutral) (simp add: no_event_dom)
  then show
    "wp_event m (hash_new_collision_event s) s \<le>
      hash_collision_budget_value
        (card (hash_map_output_values s)) 0"
    unfolding hash_collision_budget_value_def by simp
qed

lemma hash_collision_budget_state_independent_sample:
  "hash_collision_budget 0
    (lift (\<lambda>_. d) ::
      ('r, 'f protocol_channel) state_monad)"
  by (rule hash_map_preserving_imp_hash_collision_budget_zero)
    (rule hash_map_preserving_state_independent_sample)

lemma hash_target_program_state_independent_sample:
  "hash_target_program B 0
    (lift (\<lambda>_. d) ::
      ('r, 'f protocol_channel) state_monad)"
  by (rule hash_map_preserving_imp_hash_target_program_zero)
    (rule hash_map_preserving_state_independent_sample)

lemma controlled_ro_program_extension:
  assumes "controlled_ro_program q m"
  shows "hash_extension_preserving m"
  using assms
proof (induction rule: controlled_ro_program.induct)
  case (Return x)
  then show ?case by (rule hash_extension_preserving_return)
next
  case Fail
  then show ?case
    by (rule hash_map_preserving_imp_hash_extension_preserving)
      (rule hash_map_preserving_throw)
next
  case (Sample d)
  then show ?case
    by (rule hash_map_preserving_imp_hash_extension_preserving)
      (rule hash_map_preserving_state_independent_sample)
next
  case (Query q k x)
  have ext_k: "\<And>y. hash_extension_preserving (k y)"
    using Query.IH by blast
  show ?case
    by (rule hash_extension_preserving_bind)
      (rule hash_extension_preserving_hash, rule ext_k)
next
  case (Bind q m r k)
  have ext_k: "\<And>x. hash_extension_preserving (k x)"
    using Bind.IH(2) by blast
  show ?case
    by (rule hash_extension_preserving_bind[OF Bind.IH(1) ext_k])
next
  case (Weaken q m r)
  then show ?case by simp
qed

lemma controlled_ro_program_range:
  assumes "controlled_ro_program q m"
  shows "hash_range_budget q m"
  using assms
proof (induction rule: controlled_ro_program.induct)
  case (Return x)
  then show ?case by (rule hash_range_budget_return)
next
  case Fail
  then show ?case by (rule hash_range_budget_throw)
next
  case (Sample d)
  then show ?case by (rule hash_range_budget_state_independent_sample)
next
  case (Query q k x)
  have range_k: "\<And>y. hash_range_budget q (k y)"
    using Query.IH by blast
  have "hash_range_budget (1 + q)
      ((hash x :: ('f, 'f protocol_channel) state_monad)
        \<bind> k)"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash, rule range_k)
  then show ?case by simp
next
  case (Bind q m r k)
  have range_k: "\<And>x. hash_range_budget r (k x)"
    using Bind.IH(2) by blast
  show ?case
    by (rule hash_range_budget_bind[OF Bind.IH(1) range_k])
next
  case (Weaken q m r)
  show ?case
    by (rule hash_range_budget_mono[OF Weaken.hyps(2) Weaken.IH])
qed

lemma controlled_ro_program_collision:
  assumes "controlled_ro_program q m"
  shows "hash_collision_budget q m"
  using assms
proof (induction rule: controlled_ro_program.induct)
  case (Return x)
  then show ?case by (rule hash_collision_budget_return)
next
  case Fail
  then show ?case by (rule hash_collision_budget_throw)
next
  case (Sample d)
  then show ?case by (rule hash_collision_budget_state_independent_sample)
next
  case (Query q k x)
  have range_k: "\<And>y. hash_range_budget q (k y)"
    using Query(1) by (blast intro: controlled_ro_program_range)
  have collision_k: "\<And>y. hash_collision_budget q (k y)"
    using Query.IH by blast
  have "hash_collision_budget (1 + q)
      ((hash x :: ('f, 'f protocol_channel) state_monad)
        \<bind> k)"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_hash, rule hash_collision_budget_hash,
        rule range_k, rule collision_k)
  then show ?case by simp
next
  case (Bind q m r k)
  have range_m: "hash_range_budget q m"
    by (rule controlled_ro_program_range[OF Bind(1)])
  have range_k: "\<And>x. hash_range_budget r (k x)"
    using Bind(3) by (blast intro: controlled_ro_program_range)
  have collision_k: "\<And>x. hash_collision_budget r (k x)"
    using Bind.IH(2) by blast
  show ?case
    by (rule hash_collision_budget_bind)
      (rule range_m, rule Bind.IH(1), rule range_k, rule collision_k)
next
  case (Weaken q m r)
  show ?case
    by (rule hash_collision_budget_mono[OF Weaken.hyps(2) Weaken.IH])
qed

lemma controlled_ro_program_target:
  assumes "controlled_ro_program q m"
  shows "hash_target_program B q m"
  using assms
proof (induction rule: controlled_ro_program.induct)
  case (Return x)
  then show ?case by (rule hash_target_program_return)
next
  case Fail
  then show ?case by (rule hash_target_program_throw)
next
  case (Sample d)
  then show ?case by (rule hash_target_program_state_independent_sample)
next
  case (Query q k x)
  have target_k: "\<And>y. hash_target_program B q (k y)"
    using Query.IH by blast
  have "hash_target_program B (1 + q)
      ((hash x :: ('f, 'f protocol_channel) state_monad)
        \<bind> k)"
    by (rule hash_target_program_bind)
      (rule hash_target_program_hash, rule target_k)
  then show ?case by simp
next
  case (Bind q m r k)
  have target_k: "\<And>x. hash_target_program B r (k x)"
    using Bind.IH(2) by blast
  show ?case
    by (rule hash_target_program_bind[OF Bind.IH(1) target_k])
next
  case (Weaken q m r)
  show ?case
    by (rule hash_target_program_mono[OF Weaken.hyps(2) Weaken.IH])
qed

definition controlled_ro_admissible
  :: "nat \<Rightarrow>
      ('r, 'f protocol_channel) state_monad \<Rightarrow> bool"
  where
    "controlled_ro_admissible q m \<longleftrightarrow>
      hash_extension_preserving m \<and>
      hash_range_budget q m \<and>
      hash_collision_budget q m \<and>
      (\<forall>B. hash_target_program B q m)"

lemma controlled_ro_program_admissible:
  assumes "controlled_ro_program q m"
  shows "controlled_ro_admissible q m"
  unfolding controlled_ro_admissible_def
  using controlled_ro_program_extension[OF assms]
    controlled_ro_program_range[OF assms]
    controlled_ro_program_collision[OF assms]
    controlled_ro_program_target[OF assms]
  by blast

definition hash_relation_hit
  :: "('f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
      'f protocol_channel \<Rightarrow> 'f protocol_channel \<Rightarrow> bool"
  where
    "hash_relation_hit R initial final \<longleftrightarrow>
      (\<exists>x y.
        fmlookup (HashMap initial) x = None \<and>
        fmlookup (HashMap final) x = Some y \<and>
        R x y)"

definition hash_relation_hit_event
  :: "('f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
      'f protocol_channel \<Rightarrow>
      ('r \<times> 'f protocol_channel) option \<Rightarrow> bool"
  where
    "hash_relation_hit_event R initial out \<longleftrightarrow>
      (case out of
        None \<Rightarrow> False
      | Some (_, final) \<Rightarrow> hash_relation_hit R initial final)"

lemma hash_relation_hit_after_update:
  "hash_relation_hit R s
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>) \<longleftrightarrow>
    fmlookup (HashMap s) x = None \<and> R x y"
proof
  assume hit:
    "hash_relation_hit R s
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)"
  then obtain k z where fresh:
      "fmlookup (HashMap s) k = None"
    and lookup:
      "fmlookup (fmupd x y (HashMap s)) k = Some z"
    and rel: "R k z"
    by (auto simp: hash_relation_hit_def)
  have "k = x"
  proof (rule ccontr)
    assume "k \<noteq> x"
    then have "fmlookup (HashMap s) k = Some z"
      using lookup by simp
    then show False using fresh by simp
  qed
  then show "fmlookup (HashMap s) x = None \<and> R x y"
    using fresh lookup rel by simp
next
  assume "fmlookup (HashMap s) x = None \<and> R x y"
  then show
    "hash_relation_hit R s
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)"
    unfolding hash_relation_hit_def by auto
qed

lemma wp_hash_relation_hit:
  fixes x :: "'f protocol_hash_input"
    and s :: "'f protocol_channel"
  shows
    "wp_event (hash x) (hash_relation_hit_event R s) s =
      (if fmlookup (HashMap s) x = None
       then nnreal (card {y. R x y}) / nnreal size
       else 0)"
proof (cases "fmlookup (HashMap s) x")
  case None
  have indicator:
    "(\<lambda>y. if hash_relation_hit R s
        (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)
      then 1 else 0 :: prob) =
      (\<lambda>y. if y \<in> {y. R x y} then 1 else 0)"
    by (rule ext)
      (simp add: hash_relation_hit_after_update None)
  have "wp_event (hash x) (hash_relation_hit_event R s) s =
      dist_expect (hash_dist x s)
        (\<lambda>y. if y \<in> {y. R x y} then 1 else 0)"
    unfolding wp_event_def hash_relation_hit_event_def
    by (simp add: wp_hash indicator)
  also have "... = nnreal (card {y. R x y}) / nnreal size"
    by (rule dist_expect_hash_dist_fresh_indicator[OF None])
  finally show ?thesis using None by simp
next
  case (Some y)
  have no_hit:
    "\<not> hash_relation_hit R s
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)"
    by (simp add: hash_relation_hit_after_update Some)
  show ?thesis
    unfolding wp_event_def hash_relation_hit_event_def
    by (simp add: wp_hash Some hash_dist_def option_default_dist_def no_hit)
qed

definition hash_relation_budget_value :: "nat \<Rightarrow> nat \<Rightarrow> prob"
  where
    "hash_relation_budget_value b q =
      nnreal (q * b) / nnreal size"

definition hash_relation_budget
  :: "('f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow>
      ('r, 'f protocol_channel) state_monad \<Rightarrow> bool"
  where
    "hash_relation_budget R b q m \<longleftrightarrow>
      (\<forall>s.
        wp_event m (hash_relation_hit_event R s) s \<le>
          hash_relation_budget_value b q)"

definition hash_relation_program
  :: "('f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow>
      ('r, 'f protocol_channel) state_monad \<Rightarrow> bool"
  where
    "hash_relation_program R b q m \<longleftrightarrow>
      hash_extension_preserving m \<and> hash_relation_budget R b q m"

lemma hash_relation_budget_value_add:
  "hash_relation_budget_value b q + hash_relation_budget_value b r =
    hash_relation_budget_value b (q + r)"
  unfolding hash_relation_budget_value_def
  by (simp add: add_divide_nnreal algebra_simps)

lemma hash_relation_budget_value_mono:
  assumes "q \<le> r"
  shows "hash_relation_budget_value b q \<le> hash_relation_budget_value b r"
  unfolding hash_relation_budget_value_def
  apply (subst nn2real_le_iff[symmetric])
  using assms by (simp add: divide_right_mono mult_right_mono)

lemma hash_relation_budget_value_mono_left:
  assumes "b \<le> c"
  shows "hash_relation_budget_value b q \<le> hash_relation_budget_value c q"
  unfolding hash_relation_budget_value_def
  apply (subst nn2real_le_iff[symmetric])
  using assms by (simp add: divide_right_mono mult_left_mono)

lemma hash_relation_hit_event_step_bound:
  fixes m :: "('r, 'f protocol_channel) state_monad"
  assumes ext_st: "s \<le> t"
    and ext_m: "hash_extension_preserving m"
  shows
    "wp_event m (hash_relation_hit_event R s) t \<le>
      (if hash_relation_hit R s t then 1
       else wp_event m (hash_relation_hit_event R t) t)"
proof (cases "hash_relation_hit R s t")
  case True
  then show ?thesis
    using wp_event_le_1[of m "hash_relation_hit_event R s" t] by simp
next
  case False
  have mono:
    "wp_event m (hash_relation_hit_event R s) t \<le>
      wp_event m (hash_relation_hit_event R t) t"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute m t)"
      and hit_s: "hash_relation_hit_event R s out"
    show "hash_relation_hit_event R t out"
    proof (cases out)
      case None
      then show ?thesis
        using hit_s unfolding hash_relation_hit_event_def by simp
    next
      case (Some xu)
      then obtain x u where xu: "xu = (x, u)"
        by (cases xu) simp
      have out: "Some (x, u) \<in> set_dist (execute m t)"
        using support Some xu by simp
      have ext_tu: "t \<le> u"
        using ext_m out unfolding hash_extension_preserving_def by blast
      from hit_s obtain k y where fresh_s:
          "fmlookup (HashMap s) k = None"
        and lookup_u: "fmlookup (HashMap u) k = Some y"
        and rel: "R k y"
        unfolding hash_relation_hit_event_def hash_relation_hit_def
        using Some xu by auto
      show ?thesis
      proof (cases "fmlookup (HashMap t) k")
        case None
        then show ?thesis
          using Some xu lookup_u rel
          unfolding hash_relation_hit_event_def hash_relation_hit_def
          by auto
      next
        case (Some z)
        have lookup_u_z: "fmlookup (HashMap u) k = Some z"
          by (rule hash_extension_lookup[OF Some ext_tu])
        have "z = y" using lookup_u lookup_u_z by simp
        then have "hash_relation_hit R s t"
          unfolding hash_relation_hit_def
          using fresh_s Some rel by blast
        then show ?thesis using False by contradiction
      qed
    qed
  qed
  then show ?thesis using False by simp
qed

lemma hash_relation_budget_bind:
  fixes m :: "('x, 'f protocol_channel) state_monad"
    and k :: "'x \<Rightarrow> ('y, 'f protocol_channel) state_monad"
  assumes m_ext: "hash_extension_preserving m"
    and m_budget: "hash_relation_budget R b q m"
    and k_ext: "\<And>x. hash_extension_preserving (k x)"
    and k_budget: "\<And>x. hash_relation_budget R b r (k x)"
  shows "hash_relation_budget R b (q + r) (m \<bind> k)"
  unfolding hash_relation_budget_def
proof (intro allI)
  fix s :: "'f protocol_channel"
  let ?E = "hash_relation_hit_event R s"
  let ?Tail =
    "\<lambda>out. case out of
      None \<Rightarrow> 0
    | Some (x, t) \<Rightarrow>
        if hash_relation_hit R s t then 0
        else wp_event (k x) (hash_relation_hit_event R t) t"
  let ?R = "\<lambda>out. (if ?E out then 1 else 0) + ?Tail out"
  have split:
    "wp_event (m \<bind> k) ?E s \<le> wp m ?R s"
  proof -
    have exact:
      "wp_event (m \<bind> k) ?E s =
        wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) s"
      unfolding wp_event_def hash_relation_hit_event_def
      by (simp add: wpsimps)
    have "wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) s
        \<le> wp m ?R s"
    proof (rule wp_mono_on_support)
      fix out
      assume support: "out \<in> set_dist (execute m s)"
      show "(case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) \<le> ?R out"
      proof (cases out)
        case None
        then show ?thesis
          unfolding hash_relation_hit_event_def by simp
      next
        case (Some xt)
        then obtain x t where xt: "xt = (x, t)"
          by (cases xt) simp
        have m_out: "Some (x, t) \<in> set_dist (execute m s)"
          using support Some xt by simp
        have ext_st: "s \<le> t"
          using m_ext m_out unfolding hash_extension_preserving_def by blast
        have step:
          "wp_event (k x) ?E t \<le>
            (if hash_relation_hit R s t then 1
             else wp_event (k x) (hash_relation_hit_event R t) t)"
          by (rule hash_relation_hit_event_step_bound
              [OF ext_st k_ext[of x]])
        show ?thesis
          using Some xt step
          unfolding hash_relation_hit_event_def
          by (cases "hash_relation_hit R s t") simp_all
      qed
    qed
    then show ?thesis unfolding exact .
  qed
  have head_bound:
    "wp_event m ?E s \<le> hash_relation_budget_value b q"
    using m_budget unfolding hash_relation_budget_def by blast
  have tail_bound:
    "wp m ?Tail s \<le> hash_relation_budget_value b r"
  proof (rule wp_le_const_on_support)
    fix out
    assume support: "out \<in> set_dist (execute m s)"
    show "?Tail out \<le> hash_relation_budget_value b r"
    proof (cases out)
      case None
      then show ?thesis
        unfolding hash_relation_budget_value_def by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) simp
      have tail:
        "wp_event (k x) (hash_relation_hit_event R t) t \<le>
          hash_relation_budget_value b r"
        using k_budget[of x] unfolding hash_relation_budget_def by blast
      show ?thesis using Some xt tail by simp
    qed
  qed
  have "wp_event (m \<bind> k) ?E s \<le> wp m ?R s"
    by (rule split)
  also have "... = wp_event m ?E s + wp m ?Tail s"
    unfolding wp_event_def wp_def dist_expect_def
    by (simp add: sum.distrib algebra_simps
        hash_relation_hit_event_def)
  also have "... \<le>
      hash_relation_budget_value b q + hash_relation_budget_value b r"
    by (intro add_mono head_bound tail_bound)
  also have "... = hash_relation_budget_value b (q + r)"
    by (rule hash_relation_budget_value_add)
  finally show
    "wp_event (m \<bind> k) (hash_relation_hit_event R s) s \<le>
      hash_relation_budget_value b (q + r)" .
qed

lemma hash_relation_budget_bind_on_outcomes:
  fixes m :: "('x, 'f protocol_channel) state_monad"
    and k :: "'x \<Rightarrow> ('y, 'f protocol_channel) state_monad"
  assumes m_ext: "hash_extension_preserving m"
    and m_budget: "hash_relation_budget R b q m"
    and k_ext:
      "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_extension_preserving (k x)"
    and k_budget:
      "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_relation_budget R b r (k x)"
  shows "hash_relation_budget R b (q + r) (m \<bind> k)"
  unfolding hash_relation_budget_def
proof (intro allI)
  fix s :: "'f protocol_channel"
  let ?E = "hash_relation_hit_event R s"
  let ?Tail =
    "\<lambda>out. case out of
      None \<Rightarrow> 0
    | Some (x, t) \<Rightarrow>
        if hash_relation_hit R s t then 0
        else wp_event (k x) (hash_relation_hit_event R t) t"
  let ?R = "\<lambda>out. (if ?E out then 1 else 0) + ?Tail out"
  have split:
    "wp_event (m \<bind> k) ?E s \<le> wp m ?R s"
  proof -
    have exact:
      "wp_event (m \<bind> k) ?E s =
        wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) s"
      unfolding wp_event_def hash_relation_hit_event_def
      by (simp add: wpsimps)
    have "wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) s
        \<le> wp m ?R s"
    proof (rule wp_mono_on_support)
      fix out
      assume support: "out \<in> set_dist (execute m s)"
      show "(case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) \<le> ?R out"
      proof (cases out)
        case None
        then show ?thesis
          unfolding hash_relation_hit_event_def by simp
      next
        case (Some xt)
        then obtain x t where xt: "xt = (x, t)"
          by (cases xt) simp
        have m_out: "Some (x, t) \<in> set_dist (execute m s)"
          using support Some xt by simp
        have ext_st: "s \<le> t"
          using m_ext m_out unfolding hash_extension_preserving_def by blast
        have step:
          "wp_event (k x) ?E t \<le>
            (if hash_relation_hit R s t then 1
             else wp_event (k x) (hash_relation_hit_event R t) t)"
          by (rule hash_relation_hit_event_step_bound
              [OF ext_st k_ext[OF m_out]])
        show ?thesis
          using Some xt step
          unfolding hash_relation_hit_event_def
          by (cases "hash_relation_hit R s t") simp_all
      qed
    qed
    then show ?thesis unfolding exact .
  qed
  have head_bound:
    "wp_event m ?E s \<le> hash_relation_budget_value b q"
    using m_budget unfolding hash_relation_budget_def by blast
  have tail_bound:
    "wp m ?Tail s \<le> hash_relation_budget_value b r"
  proof (rule wp_le_const_on_support)
    fix out
    assume support: "out \<in> set_dist (execute m s)"
    show "?Tail out \<le> hash_relation_budget_value b r"
    proof (cases out)
      case None
      then show ?thesis
        unfolding hash_relation_budget_value_def by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) simp
      have m_out: "Some (x, t) \<in> set_dist (execute m s)"
        using support Some xt by simp
      have tail:
        "wp_event (k x) (hash_relation_hit_event R t) t \<le>
          hash_relation_budget_value b r"
        using k_budget[OF m_out] unfolding hash_relation_budget_def
        by blast
      show ?thesis using Some xt tail by simp
    qed
  qed
  have "wp_event (m \<bind> k) ?E s \<le> wp m ?R s"
    by (rule split)
  also have "... = wp_event m ?E s + wp m ?Tail s"
    unfolding wp_event_def wp_def dist_expect_def
    by (simp add: sum.distrib algebra_simps
        hash_relation_hit_event_def)
  also have "... \<le>
      hash_relation_budget_value b q + hash_relation_budget_value b r"
    by (intro add_mono head_bound tail_bound)
  also have "... = hash_relation_budget_value b (q + r)"
    by (rule hash_relation_budget_value_add)
  finally show
    "wp_event (m \<bind> k) (hash_relation_hit_event R s) s \<le>
      hash_relation_budget_value b (q + r)" .
qed

lemma hash_relation_program_bind:
  assumes m: "hash_relation_program R b q m"
    and k: "\<And>x. hash_relation_program R b r (k x)"
  shows "hash_relation_program R b (q + r) (m \<bind> k)"
  unfolding hash_relation_program_def
proof
  show "hash_extension_preserving (m \<bind> k)"
    by (rule hash_extension_preserving_bind)
      (use m k in \<open>simp_all add: hash_relation_program_def\<close>)
  show "hash_relation_budget R b (q + r) (m \<bind> k)"
    by (rule hash_relation_budget_bind)
      (use m k in \<open>simp_all add: hash_relation_program_def\<close>)
qed

lemma hash_relation_program_bind_on_outcomes:
  fixes m :: "('x, 'f protocol_channel) state_monad"
    and k :: "'x \<Rightarrow> ('y, 'f protocol_channel) state_monad"
  assumes m: "hash_relation_program R b q m"
    and k:
      "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_relation_program R b r (k x)"
  shows "hash_relation_program R b (q + r) (m \<bind> k)"
  unfolding hash_relation_program_def
proof
  show "hash_extension_preserving (m \<bind> k)"
    by (rule hash_extension_preserving_bind_on_outcomes)
      (use m k in \<open>simp_all add: hash_relation_program_def\<close>)
  show "hash_relation_budget R b (q + r) (m \<bind> k)"
    by (rule hash_relation_budget_bind_on_outcomes)
      (use m k in \<open>simp_all add: hash_relation_program_def\<close>)
qed

lemma hash_relation_program_zero:
  assumes preserving: "hash_map_preserving m"
  shows "hash_relation_program R b 0 m"
  unfolding hash_relation_program_def hash_relation_budget_def
proof
  show "hash_extension_preserving m"
    by (rule hash_map_preserving_imp_hash_extension_preserving[OF preserving])
  show "\<forall>s.
      wp_event m (hash_relation_hit_event R s) s \<le>
        hash_relation_budget_value b 0"
  proof
    fix s
    have no_event_support:
      "\<And>out. out \<in> set_dist (execute m s) \<Longrightarrow>
        \<not> hash_relation_hit_event R s out"
    proof -
      fix out
      assume support: "out \<in> set_dist (execute m s)"
      show "\<not> hash_relation_hit_event R s out"
      proof (cases out)
        case None
        then show ?thesis
          unfolding hash_relation_hit_event_def by simp
      next
        case (Some xt)
        then obtain x t where xt: "xt = (x, t)"
          by (cases xt) simp
        have same: "HashMap t = HashMap s"
          using preserving support Some xt
          unfolding hash_map_preserving_def by blast
        show ?thesis
          using same Some xt
          unfolding hash_relation_hit_event_def hash_relation_hit_def
          by auto
      qed
    qed
    have no_event:
      "\<And>out. out \<in> dom (dist (execute m s)) \<Longrightarrow>
        \<not> hash_relation_hit_event R s out"
      using no_event_support unfolding set_dist_def by blast
    have "wp_event m (hash_relation_hit_event R s) s = 0"
      unfolding wp_event_def wp_def dist_expect_def
      by (intro sum.neutral) (simp add: no_event)
    then show
      "wp_event m (hash_relation_hit_event R s) s \<le>
        hash_relation_budget_value b 0"
      unfolding hash_relation_budget_value_def by simp
  qed
qed

lemma hash_relation_program_hash:
  assumes fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "hash_relation_program R b 1
      (hash x :: ('f, 'f protocol_channel) state_monad)"
  unfolding hash_relation_program_def hash_relation_budget_def
proof
  show "hash_extension_preserving
      (hash x :: ('f, 'f protocol_channel) state_monad)"
    by (rule hash_extension_preserving_hash)
  show "\<forall>s.
      wp_event (hash x) (hash_relation_hit_event R s) s \<le>
        hash_relation_budget_value b 1"
  proof
    fix s :: "'f protocol_channel"
    have
      "wp_event (hash x) (hash_relation_hit_event R s) s \<le>
        nnreal (card {y. R x y}) / nnreal size"
      unfolding wp_hash_relation_hit by simp
    also have "... \<le> nnreal b / nnreal size"
      by (rule nnreal_nat_divide_right_mono)
        (rule fibers)
    also have "... = hash_relation_budget_value b 1"
      unfolding hash_relation_budget_value_def by simp
    finally show
      "wp_event (hash x) (hash_relation_hit_event R s) s \<le>
        hash_relation_budget_value b 1" .
  qed
qed

lemma hash_relation_program_mono:
  assumes qr: "q \<le> r"
    and program: "hash_relation_program R b q m"
  shows "hash_relation_program R b r m"
  unfolding hash_relation_program_def hash_relation_budget_def
proof
  show "hash_extension_preserving m"
    using program unfolding hash_relation_program_def by simp
  show "\<forall>s.
      wp_event m (hash_relation_hit_event R s) s \<le>
        hash_relation_budget_value b r"
  proof
    fix s
    have
      "wp_event m (hash_relation_hit_event R s) s \<le>
        hash_relation_budget_value b q"
      using program
      unfolding hash_relation_program_def hash_relation_budget_def by blast
    also have "... \<le> hash_relation_budget_value b r"
      by (rule hash_relation_budget_value_mono[OF qr])
    finally show
      "wp_event m (hash_relation_hit_event R s) s \<le>
        hash_relation_budget_value b r" .
  qed
qed

lemma controlled_ro_program_relation:
  assumes controlled: "controlled_ro_program q m"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows "hash_relation_program R b q m"
  using controlled
proof (induction rule: controlled_ro_program.induct)
  case (Return x)
  show ?case
    by (rule hash_relation_program_zero)
      (rule hash_map_preserving_return)
next
  case Fail
  show ?case
    by (rule hash_relation_program_zero)
      (rule hash_map_preserving_throw)
next
  case (Sample d)
  show ?case
    by (rule hash_relation_program_zero)
      (rule hash_map_preserving_state_independent_sample)
next
  case (Query q k x)
  have tail: "\<And>y. hash_relation_program R b q (k y)"
    using Query.IH fibers by blast
  have "hash_relation_program R b (1 + q)
      ((hash x :: ('f, 'f protocol_channel) state_monad) \<bind> k)"
    by (rule hash_relation_program_bind)
      (rule hash_relation_program_hash[OF fibers], rule tail)
  then show ?case by simp
next
  case (Bind q m r k)
  have tail: "\<And>x. hash_relation_program R b r (k x)"
    using Bind.IH(2) by blast
  show ?case
    by (rule hash_relation_program_bind[OF Bind.IH(1) tail])
next
  case (Weaken q m r)
  show ?case
    by (rule hash_relation_program_mono[OF Weaken.hyps(2)
          Weaken.IH])
qed

theorem controlled_ro_program_relation_bound:
  assumes controlled: "controlled_ro_program q m"
    and fibers: "\<And>x. card {y. R x y} \<le> b"
  shows
    "wp_event m (hash_relation_hit_event R s) s \<le>
      nnreal (q * b) / nnreal size"
proof -
  have program: "hash_relation_program R b q m"
    by (rule controlled_ro_program_relation[OF controlled fibers])
  have budget: "hash_relation_budget R b q m"
    using program unfolding hash_relation_program_def by simp
  show ?thesis
    using budget unfolding hash_relation_budget_def
      hash_relation_budget_value_def by blast
qed

end

end
