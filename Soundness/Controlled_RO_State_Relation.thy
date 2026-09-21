(*  Title:      Stark/Controlled_RO_State_Relation.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Controlled_RO_State_Relation
  imports Controlled_RO
begin

context soundness
begin

definition hash_state_relation_active
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
        'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
      ('f protocol_hash_input, 'f) fmap \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "hash_state_relation_active R M x y \<longleftrightarrow>
    fmlookup M x = Some y \<and> R M x y"

definition hash_state_relation_transition
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
        'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
      ('f protocol_hash_input, 'f) fmap \<Rightarrow>
      ('f protocol_hash_input, 'f) fmap \<Rightarrow> bool"
where
  "hash_state_relation_transition R initial final \<longleftrightarrow>
    (\<exists>x y.
      hash_state_relation_active R final x y \<and>
      \<not> hash_state_relation_active R initial x y)"

definition hash_state_relation_transition_event
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
        'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
      ('f protocol_hash_input, 'f) fmap \<Rightarrow>
      ('r \<times> 'f protocol_channel) option \<Rightarrow> bool"
where
  "hash_state_relation_transition_event R initial out \<longleftrightarrow>
    (case out of
      None \<Rightarrow> False
    | Some (_, final) \<Rightarrow>
        hash_state_relation_transition R initial (HashMap final))"

lemma hash_state_relation_transition_split:
  assumes "hash_state_relation_transition R M U"
  shows "hash_state_relation_transition R M T \<or>
    hash_state_relation_transition R T U"
  using assms
  unfolding hash_state_relation_transition_def
  by blast

lemma hash_state_relation_transition_refl[simp]:
  "\<not> hash_state_relation_transition R M M"
  unfolding hash_state_relation_transition_def by blast

lemma hash_state_relation_transition_after_known_update:
  assumes "fmlookup M x = Some y"
  shows "\<not> hash_state_relation_transition R M (fmupd x y M)"
proof -
  have map_eq: "fmupd x y M = M"
  proof (rule fmap_ext)
    fix k
    show "fmlookup (fmupd x y M) k = fmlookup M k"
      using assms by (cases "k = x") simp_all
  qed
  show ?thesis using map_eq by simp
qed

lemma wp_hash_state_relation_transition:
  fixes x :: "'f protocol_hash_input"
    and s :: "'f protocol_channel"
  shows
    "wp_event (hash x)
        (hash_state_relation_transition_event R (HashMap s)) s =
      (if fmlookup (HashMap s) x = None
       then nnreal
          (card {y.
            hash_state_relation_transition R (HashMap s)
              (fmupd x y (HashMap s))}) /
          nnreal size
       else 0)"
proof (cases "fmlookup (HashMap s) x")
  case None
  have indicator:
    "(\<lambda>y. if hash_state_relation_transition R (HashMap s)
        (fmupd x y (HashMap s))
      then 1 else 0 :: prob) =
      (\<lambda>y. if y \<in> {y.
        hash_state_relation_transition R (HashMap s)
          (fmupd x y (HashMap s))}
        then 1 else 0)"
    by (rule ext) simp
  have hash_map_update:
    "\<And>y. HashMap (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>) =
      fmupd x y (HashMap s)"
    by simp
  have "wp_event (hash x)
        (hash_state_relation_transition_event R (HashMap s)) s =
      dist_expect (hash_dist x s)
        (\<lambda>y. if y \<in> {y.
          hash_state_relation_transition R (HashMap s)
            (fmupd x y (HashMap s))}
          then 1 else 0)"
    unfolding wp_event_def hash_state_relation_transition_event_def
    by (simp only: wp_hash option.case prod.case hash_map_update indicator)
  also have "... =
      nnreal
        (card {y.
          hash_state_relation_transition R (HashMap s)
            (fmupd x y (HashMap s))}) /
        nnreal size"
    by (rule dist_expect_hash_dist_fresh_indicator[OF None])
  finally show ?thesis using None by simp
next
  case (Some y)
  have no_transition:
    "\<not> hash_state_relation_transition R (HashMap s)
      (fmupd x y (HashMap s))"
    by (rule hash_state_relation_transition_after_known_update[OF Some])
  show ?thesis
    unfolding wp_event_def hash_state_relation_transition_event_def
    by (simp add: wp_hash Some hash_dist_def option_default_dist_def no_transition)
qed

lemma hash_state_relation_transition_event_step_bound:
  fixes m :: "('r, 'f protocol_channel) state_monad"
  shows
    "wp_event m (hash_state_relation_transition_event R M) t \<le>
      (if hash_state_relation_transition R M (HashMap t) then 1
       else wp_event m
          (hash_state_relation_transition_event R (HashMap t)) t)"
proof (cases
    "hash_state_relation_transition R M (HashMap t)")
  case True
  then show ?thesis
    using wp_event_le_1[
      of m "hash_state_relation_transition_event R M" t]
    by simp
next
  case False
  have mono:
    "wp_event m (hash_state_relation_transition_event R M) t \<le>
      wp_event m
        (hash_state_relation_transition_event R (HashMap t)) t"
  proof (rule wp_event_mono_on_support)
    fix out
    assume support: "out \<in> set_dist (execute m t)"
      and transition_M:
        "hash_state_relation_transition_event R M out"
    show
      "hash_state_relation_transition_event R (HashMap t) out"
    proof (cases out)
      case None
      then show ?thesis
        using transition_M
        unfolding hash_state_relation_transition_event_def
        by simp
    next
      case (Some xu)
      then obtain x u where xu: "xu = (x, u)"
        by (cases xu) simp
      have transition_MU:
        "hash_state_relation_transition R M (HashMap u)"
        using transition_M Some xu
        unfolding hash_state_relation_transition_event_def
        by simp
      have split:
        "hash_state_relation_transition R M (HashMap t) \<or>
          hash_state_relation_transition R (HashMap t) (HashMap u)"
        by (rule hash_state_relation_transition_split[OF transition_MU])
      have transition_TU:
        "hash_state_relation_transition R (HashMap t) (HashMap u)"
        using split False by blast
      show ?thesis
        using Some xu transition_TU
        unfolding hash_state_relation_transition_event_def
        by simp
    qed
  qed
  then show ?thesis using False by simp
qed

definition hash_state_relation_budget
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
        'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow>
      ('r, 'f protocol_channel) state_monad \<Rightarrow> bool"
where
  "hash_state_relation_budget R b q m \<longleftrightarrow>
    (\<forall>s.
      wp_event m
          (hash_state_relation_transition_event R (HashMap s)) s \<le>
        hash_relation_budget_value b q)"

lemma hash_state_relation_budget_bind:
  fixes m :: "('x, 'f protocol_channel) state_monad"
    and k :: "'x \<Rightarrow> ('y, 'f protocol_channel) state_monad"
  assumes m_budget: "hash_state_relation_budget R b q m"
    and k_budget: "\<And>x. hash_state_relation_budget R b r (k x)"
  shows "hash_state_relation_budget R b (q + r) (m \<bind> k)"
  unfolding hash_state_relation_budget_def
proof (intro allI)
  fix s :: "'f protocol_channel"
  let ?E =
    "hash_state_relation_transition_event R (HashMap s)"
  let ?Tail =
    "\<lambda>out. case out of
      None \<Rightarrow> 0
    | Some (x, t) \<Rightarrow>
        if hash_state_relation_transition R (HashMap s) (HashMap t)
        then 0
        else wp_event (k x)
          (hash_state_relation_transition_event R (HashMap t)) t"
  let ?Bound =
    "\<lambda>out. (if ?E out then 1 else 0) + ?Tail out"
  have split:
    "wp_event (m \<bind> k) ?E s \<le> wp m ?Bound s"
  proof -
    have exact:
      "wp_event (m \<bind> k) ?E s =
        wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) s"
      unfolding wp_event_def
        hash_state_relation_transition_event_def
      by (simp add: wpsimps)
    have "wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) s
        \<le> wp m ?Bound s"
    proof (rule wp_mono_on_support)
      fix out
      assume support: "out \<in> set_dist (execute m s)"
      show "(case out of
            None \<Rightarrow> 0
          | Some (x, t) \<Rightarrow> wp_event (k x) ?E t) \<le>
        ?Bound out"
      proof (cases out)
        case None
        then show ?thesis
          unfolding hash_state_relation_transition_event_def
          by simp
      next
        case (Some xt)
        then obtain x t where xt: "xt = (x, t)"
          by (cases xt) simp
        have step:
          "wp_event (k x) ?E t \<le>
            (if hash_state_relation_transition R
                (HashMap s) (HashMap t)
             then 1
             else wp_event (k x)
                (hash_state_relation_transition_event R (HashMap t)) t)"
          by (rule hash_state_relation_transition_event_step_bound)
        show ?thesis
          using Some xt step
          unfolding hash_state_relation_transition_event_def
          by (cases
              "hash_state_relation_transition R
                (HashMap s) (HashMap t)")
            simp_all
      qed
    qed
    then show ?thesis unfolding exact .
  qed
  have head_bound:
    "wp_event m ?E s \<le> hash_relation_budget_value b q"
    using m_budget
    unfolding hash_state_relation_budget_def
    by blast
  have tail_bound:
    "wp m ?Tail s \<le> hash_relation_budget_value b r"
  proof (rule wp_le_const_on_support)
    fix out
    assume support: "out \<in> set_dist (execute m s)"
    show "?Tail out \<le> hash_relation_budget_value b r"
    proof (cases out)
      case None
      then show ?thesis
        unfolding hash_relation_budget_value_def
        by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) simp
      have tail:
        "wp_event (k x)
            (hash_state_relation_transition_event R (HashMap t)) t \<le>
          hash_relation_budget_value b r"
        using k_budget[of x]
        unfolding hash_state_relation_budget_def
        by blast
      show ?thesis using Some xt tail by simp
    qed
  qed
  have "wp_event (m \<bind> k) ?E s \<le> wp m ?Bound s"
    by (rule split)
  also have "... = wp_event m ?E s + wp m ?Tail s"
    unfolding wp_event_def wp_def dist_expect_def
    by (simp add: sum.distrib algebra_simps
        hash_state_relation_transition_event_def)
  also have "... \<le>
      hash_relation_budget_value b q +
        hash_relation_budget_value b r"
    by (intro add_mono head_bound tail_bound)
  also have "... = hash_relation_budget_value b (q + r)"
    by (rule hash_relation_budget_value_add)
  finally show
    "wp_event (m \<bind> k)
        (hash_state_relation_transition_event R (HashMap s)) s \<le>
      hash_relation_budget_value b (q + r)" .
qed

lemma hash_state_relation_budget_zero:
  assumes preserving: "hash_map_preserving m"
  shows "hash_state_relation_budget R b 0 m"
  unfolding hash_state_relation_budget_def
proof
  fix s
  have no_event_support:
    "\<And>out. out \<in> set_dist (execute m s) \<Longrightarrow>
      \<not> hash_state_relation_transition_event R (HashMap s) out"
  proof -
    fix out
    assume support: "out \<in> set_dist (execute m s)"
    show
      "\<not> hash_state_relation_transition_event R (HashMap s) out"
    proof (cases out)
      case None
      then show ?thesis
        unfolding hash_state_relation_transition_event_def
        by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) simp
      have same: "HashMap t = HashMap s"
        using preserving support Some xt
        unfolding hash_map_preserving_def
        by blast
      show ?thesis
        using same Some xt
        unfolding hash_state_relation_transition_event_def
        by simp
    qed
  qed
  have no_event:
    "\<And>out. out \<in> dom (dist (execute m s)) \<Longrightarrow>
      \<not> hash_state_relation_transition_event R (HashMap s) out"
    using no_event_support
    unfolding set_dist_def
    by blast
  have "wp_event m
      (hash_state_relation_transition_event R (HashMap s)) s = 0"
    unfolding wp_event_def wp_def dist_expect_def
    by (intro sum.neutral) (simp add: no_event)
  then show
    "wp_event m
        (hash_state_relation_transition_event R (HashMap s)) s \<le>
      hash_relation_budget_value b 0"
    unfolding hash_relation_budget_value_def
    by simp
qed

lemma hash_state_relation_budget_hash:
  assumes steps:
    "\<And>M x. card {y.
      hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  shows
    "hash_state_relation_budget R b 1
      (hash x :: ('f, 'f protocol_channel) state_monad)"
  unfolding hash_state_relation_budget_def
proof
  fix s :: "'f protocol_channel"
  let ?T =
    "{y. hash_state_relation_transition R (HashMap s)
      (fmupd x y (HashMap s))}"
  have exact:
    "wp_event (hash x)
        (hash_state_relation_transition_event R (HashMap s)) s =
      (if fmlookup (HashMap s) x = None
       then nnreal (card ?T) / nnreal size
       else 0)"
    by (rule wp_hash_state_relation_transition)
  have first:
    "wp_event (hash x)
        (hash_state_relation_transition_event R (HashMap s)) s \<le>
      nnreal (card ?T) / nnreal size"
    using exact by (cases "fmlookup (HashMap s) x") simp_all
  have card_le: "card ?T \<le> b"
    by (rule steps)
  have "wp_event (hash x)
        (hash_state_relation_transition_event R (HashMap s)) s \<le>
      nnreal (card ?T) / nnreal size"
    by (rule first)
  also have "... \<le> nnreal b / nnreal size"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... = hash_relation_budget_value b 1"
    unfolding hash_relation_budget_value_def by simp
  finally show
    "wp_event (hash x)
        (hash_state_relation_transition_event R (HashMap s)) s \<le>
      hash_relation_budget_value b 1" .
qed
lemma hash_state_relation_budget_mono:
  assumes qr: "q \<le> r"
    and budget: "hash_state_relation_budget R b q m"
  shows "hash_state_relation_budget R b r m"
  unfolding hash_state_relation_budget_def
proof
  fix s
  have
    "wp_event m
        (hash_state_relation_transition_event R (HashMap s)) s \<le>
      hash_relation_budget_value b q"
    using budget
    unfolding hash_state_relation_budget_def
    by blast
  also have "... \<le> hash_relation_budget_value b r"
    by (rule hash_relation_budget_value_mono[OF qr])
  finally show
    "wp_event m
        (hash_state_relation_transition_event R (HashMap s)) s \<le>
      hash_relation_budget_value b r" .
qed

lemma controlled_ro_program_state_relation:
  assumes controlled: "controlled_ro_program q m"
    and steps:
      "\<And>M x. card {y.
        hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  shows "hash_state_relation_budget R b q m"
  using controlled
proof (induction rule: controlled_ro_program.induct)
  case (Return x)
  show ?case
    by (rule hash_state_relation_budget_zero)
      (rule hash_map_preserving_return)
next
  case Fail
  show ?case
    by (rule hash_state_relation_budget_zero)
      (rule hash_map_preserving_throw)
next
  case (Sample d)
  show ?case
    by (rule hash_state_relation_budget_zero)
      (rule hash_map_preserving_state_independent_sample)
next
  case (Query q k x)
  have tail:
    "\<And>y. hash_state_relation_budget R b q (k y)"
    using Query.IH steps
    by blast
  have
    "hash_state_relation_budget R b (1 + q)
      ((hash x :: ('f, 'f protocol_channel) state_monad) \<bind> k)"
    by (rule hash_state_relation_budget_bind)
      (rule hash_state_relation_budget_hash[OF steps], rule tail)
  then show ?case by simp
next
  case (Bind q m r k)
  have tail:
    "\<And>x. hash_state_relation_budget R b r (k x)"
    using Bind.IH steps
    by blast
  show ?case
    by (rule hash_state_relation_budget_bind)
      (use Bind.IH steps in blast, rule tail)
next
  case (Weaken q m r)
  show ?case
    by (rule hash_state_relation_budget_mono[OF Weaken.hyps(2)])
      (use Weaken.IH steps in blast)
qed

lemma wp_controlled_ro_program_state_relation:
  assumes controlled: "controlled_ro_program q m"
    and steps:
      "\<And>M x. card {y.
        hash_state_relation_transition R M (fmupd x y M)} \<le> b"
  shows
    "wp_event m
        (hash_state_relation_transition_event R (HashMap s)) s \<le>
      nnreal (q * b) / nnreal size"
  using controlled_ro_program_state_relation[OF controlled steps]
  unfolding hash_state_relation_budget_def
    hash_relation_budget_value_def
  by blast


text \<open>
  For a map-dependent relation, a fresh map update can activate the relation in
  two different ways.  A direct activation uses the newly inserted key.  A
  drift activation changes whether an older key is related because the
  relation itself observes the enlarged map.  Keeping these cases separate is
  essential for adaptive protocol relations: the direct branch retains its
  exact output fiber, while transcript-state and Merkle-induced drift can be
  charged by their own target arguments.
\<close>

definition hash_state_relation_direct_activation
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
        'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
      ('f protocol_hash_input, 'f) fmap \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "hash_state_relation_direct_activation R M x y \<longleftrightarrow>
    hash_state_relation_active R (fmupd x y M) x y \<and>
    \<not> hash_state_relation_active R M x y"

definition hash_state_relation_drift_activation
  :: "(('f protocol_hash_input, 'f) fmap \<Rightarrow>
        'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow>
      ('f protocol_hash_input, 'f) fmap \<Rightarrow>
      'f protocol_hash_input \<Rightarrow> 'f \<Rightarrow> bool"
where
  "hash_state_relation_drift_activation R M x y \<longleftrightarrow>
    (\<exists>k z. k \<noteq> x \<and>
      hash_state_relation_active R (fmupd x y M) k z \<and>
      \<not> hash_state_relation_active R M k z)"

lemma hash_state_relation_transition_update_imp_direct_or_drift:
  assumes transition:
    "hash_state_relation_transition R M (fmupd x y M)"
  shows
    "hash_state_relation_direct_activation R M x y \<or>
     hash_state_relation_drift_activation R M x y"
proof -
  from transition obtain k z where
    active_new:
      "hash_state_relation_active R (fmupd x y M) k z"
    and inactive_old:
      "\<not> hash_state_relation_active R M k z"
    unfolding hash_state_relation_transition_def
    by blast
  show ?thesis
  proof (cases "k = x")
    case True
    have z_eq: "z = y"
      using active_new True
      unfolding hash_state_relation_active_def
      by simp
    show ?thesis
      unfolding hash_state_relation_direct_activation_def
      using active_new inactive_old True z_eq
      by simp
  next
    case False
    show ?thesis
      unfolding hash_state_relation_drift_activation_def
      by (intro disjI2 exI[of _ k] exI[of _ z])
        (use False active_new inactive_old in simp)
  qed
qed

lemma hash_state_relation_transition_update_fiber_card_bound:
  assumes direct:
      "card {y. hash_state_relation_direct_activation R M x y} \<le> b"
    and drift:
      "card {y. hash_state_relation_drift_activation R M x y} \<le> d"
  shows
    "card {y. hash_state_relation_transition R M (fmupd x y M)}
      \<le> b + d"
proof -
  have subset:
    "{y. hash_state_relation_transition R M (fmupd x y M)} \<subseteq>
      {y. hash_state_relation_direct_activation R M x y} \<union>
      {y. hash_state_relation_drift_activation R M x y}"
    using hash_state_relation_transition_update_imp_direct_or_drift
    by blast
  have finite_direct:
    "finite {y. hash_state_relation_direct_activation R M x y}"
    by simp
  have finite_drift:
    "finite {y. hash_state_relation_drift_activation R M x y}"
    by simp
  have "card {y. hash_state_relation_transition R M (fmupd x y M)}
      \<le> card
        ({y. hash_state_relation_direct_activation R M x y} \<union>
         {y. hash_state_relation_drift_activation R M x y})"
    by (rule card_mono) (use finite_direct finite_drift subset in auto)
  also have "... \<le>
      card {y. hash_state_relation_direct_activation R M x y} +
      card {y. hash_state_relation_drift_activation R M x y}"
    by (rule card_Un_le)
  also have "... \<le> b + d"
    by (rule add_mono[OF direct drift])
  finally show ?thesis .
qed

lemma wp_controlled_ro_program_state_relation_direct_drift:
  assumes controlled: "controlled_ro_program q m"
    and direct:
      "\<And>M x. card {y.
        hash_state_relation_direct_activation R M x y} \<le> b"
    and drift:
      "\<And>M x. card {y.
        hash_state_relation_drift_activation R M x y} \<le> d"
  shows
    "wp_event m
        (hash_state_relation_transition_event R (HashMap s)) s
      \<le> nnreal (q * (b + d)) / nnreal size"
  by (rule wp_controlled_ro_program_state_relation[OF controlled])
    (rule hash_state_relation_transition_update_fiber_card_bound[
      OF direct drift])


lemma wp_event_bind_output_state_dependent_relation_bound:
  fixes m :: "('x, 'f protocol_channel) state_monad"
    and k :: "'x \<Rightarrow> ('y, 'f protocol_channel) state_monad"
  assumes none: "\<not> E None"
    and event_imp:
      "\<And>x t out. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        out \<in> set_dist (execute (k x) t) \<Longrightarrow>
        E out \<Longrightarrow>
        hash_relation_hit_event (R x t) t out"
    and budget:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_relation_program (R x t) b n (k x)"
  shows "wp_event (m \<bind> k) E s \<le> hash_relation_budget_value b n"
proof (rule wp_event_bind_bound_by_cont)
  show "\<not> E None"
    by (rule none)
next
  fix x t
  assume head: "Some (x, t) \<in> set_dist (execute m s)"
  have "wp_event (k x) E t \<le>
      wp_event (k x) (hash_relation_hit_event (R x t) t) t"
    by (rule wp_event_mono_on_support)
      (use head event_imp in blast)
  also have "... \<le> hash_relation_budget_value b n"
    using budget[OF head]
    unfolding hash_relation_program_def hash_relation_budget_def
    by blast
  finally show "wp_event (k x) E t \<le> hash_relation_budget_value b n" .
qed

lemma hash_relation_program_of_projection:
  fixes m :: "('x, 'f protocol_channel) state_monad"
    and n :: "('y, 'f protocol_channel) state_monad"
    and project :: "'x \<Rightarrow> 'y"
  assumes projection:
      "m \<bind> (\<lambda>x. return (project x)) = n"
    and program: "hash_relation_program R b q n"
  shows "hash_relation_program R b q m"
proof -
  have extension_n: "hash_extension_preserving n"
    using program unfolding hash_relation_program_def by blast
  have extension_m: "hash_extension_preserving m"
    unfolding hash_extension_preserving_def
  proof (intro allI impI)
    fix s x t
    assume out: "Some (x, t) \<in> set_dist (execute m s)"
    have projected:
      "Some (project x, t) \<in>
        set_dist (execute (m \<bind> (\<lambda>x. return (project x))) s)"
      by (rule set_dist_bindI[OF out]) simp
    have projected_n:
      "Some (project x, t) \<in> set_dist (execute n s)"
      using projected unfolding projection .
    show "s \<le> t"
      using extension_n projected_n
      unfolding hash_extension_preserving_def
      by blast
  qed
  have budget_n: "hash_relation_budget R b q n"
    using program unfolding hash_relation_program_def by blast
  have budget_m: "hash_relation_budget R b q m"
    unfolding hash_relation_budget_def
  proof
    fix s
    let ?E = "hash_relation_hit_event R s"
    have event_map:
      "(\<lambda>out. case out of
        None \<Rightarrow> ?E None
      | Some (x, t) \<Rightarrow> ?E (Some (project x, t))) = ?E"
      unfolding hash_relation_hit_event_def
      by (rule ext) (auto split: option.splits prod.splits)
    have mapped:
      "wp_event (m \<bind> (\<lambda>x. return (project x))) ?E s =
        wp_event m ?E s"
      by (subst wp_event_bind_return_map)
        (simp only: event_map)
    have "wp_event n ?E s \<le> hash_relation_budget_value b q"
      using budget_n unfolding hash_relation_budget_def by blast
    then show "wp_event m ?E s \<le> hash_relation_budget_value b q"
      using mapped unfolding projection by simp
  qed
  show ?thesis
    unfolding hash_relation_program_def
    using extension_m budget_m
    by blast
qed

end
end
