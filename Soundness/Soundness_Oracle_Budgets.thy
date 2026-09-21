(*  Title:      Stark/Soundness_Oracle_Budgets.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Oracle_Budgets
  imports Soundness_Oracle_Target
begin

text \<open>Random-oracle range and collision budget calculus for protocol programs.\<close>

context soundness
begin

definition hash_collision_budget_value :: "nat \<Rightarrow> nat \<Rightarrow> prob"
  where
    "hash_collision_budget_value c n =
      nnreal (n * (c + n)) / nnreal size"

definition hash_range_budget
  :: "nat \<Rightarrow> ('r, ('f, 'a) protocol_channel_scheme) state_monad \<Rightarrow> bool"
  where
    "hash_range_budget n m \<longleftrightarrow>
      (\<forall>s x t.
        Some (x, t) \<in> set_dist (execute m s) \<longrightarrow>
        card (hash_map_output_values t) \<le>
          card (hash_map_output_values s) + n)"

definition hash_collision_budget
  :: "nat \<Rightarrow> ('r, ('f, 'a) protocol_channel_scheme) state_monad \<Rightarrow> bool"
  where
    "hash_collision_budget n m \<longleftrightarrow>
      (\<forall>s. \<not> hash_map_output_collision s \<longrightarrow>
        wp_event m (hash_new_collision_event s) s \<le>
          hash_collision_budget_value (card (hash_map_output_values s)) n)"

lemma hash_collision_budget_value_mono_left:
  assumes "c \<le> d"
  shows "hash_collision_budget_value c n \<le>
    hash_collision_budget_value d n"
  unfolding hash_collision_budget_value_def
  apply (subst nn2real_le_iff[symmetric])
  using assms by (simp add: divide_right_mono add_mono mult_left_mono)

lemma hash_collision_budget_value_mono_right:
  assumes "m \<le> n"
  shows "hash_collision_budget_value c m \<le>
    hash_collision_budget_value c n"
  unfolding hash_collision_budget_value_def
  apply (subst nn2real_le_iff[symmetric])
  using assms by (simp add: divide_right_mono add_mono mult_mono)

lemma hash_range_budget_mono:
  fixes p :: "('r, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes "m \<le> n"
    and budget: "hash_range_budget m p"
  shows "hash_range_budget n p"
  using assms unfolding hash_range_budget_def by force

lemma hash_collision_budget_mono:
  fixes p :: "('r, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes "m \<le> n"
    and budget: "hash_collision_budget m p"
  shows "hash_collision_budget n p"
  unfolding hash_collision_budget_def
proof (intro allI impI)
  fix s :: "('f, 'a) protocol_channel_scheme"
  assume clean: "\<not> hash_map_output_collision s"
  have "wp_event p (hash_new_collision_event s) s \<le>
    hash_collision_budget_value (card (hash_map_output_values s)) m"
    using budget clean unfolding hash_collision_budget_def by blast
  also have "... \<le>
    hash_collision_budget_value (card (hash_map_output_values s)) n"
    by (rule hash_collision_budget_value_mono_right[OF assms(1)])
  finally show "wp_event p (hash_new_collision_event s) s \<le>
    hash_collision_budget_value (card (hash_map_output_values s)) n" .
qed

lemma hash_collision_budget_value_bind_le:
  "hash_collision_budget_value c n +
      hash_collision_budget_value (c + n) n' \<le>
    hash_collision_budget_value c (n + n')"
  unfolding hash_collision_budget_value_def
  by (simp add: add_divide_nnreal algebra_simps)

lemma hash_range_budget_bind:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes m: "hash_range_budget n m"
    and k: "\<And>x. hash_range_budget n' (k x)"
  shows "hash_range_budget (n + n') (m \<bind> k)"
  unfolding hash_range_budget_def
proof (intro allI impI)
  fix s y t
  assume outcome: "Some (y, t) \<in> set_dist (execute (m \<bind> k) s)"
  from outcome obtain x s1 where
    m_out: "Some (x, s1) \<in> set_dist (execute m s)"
    and k_out: "Some (y, t) \<in> set_dist (execute (k x) s1)"
    by (auto elim!: set_dist_bindE)
  have m_range:
    "card (hash_map_output_values s1) \<le>
      card (hash_map_output_values s) + n"
    using m m_out unfolding hash_range_budget_def by blast
  have k_range:
    "card (hash_map_output_values t) \<le>
      card (hash_map_output_values s1) + n'"
    using k k_out unfolding hash_range_budget_def by blast
  show "card (hash_map_output_values t)
      \<le> card (hash_map_output_values s) + (n + n')"
    using m_range k_range by linarith
qed

lemma hash_range_budget_bind_on_outcomes:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes m: "hash_range_budget n m"
    and k:
      "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_range_budget n' (k x)"
  shows "hash_range_budget (n + n') (m \<bind> k)"
  unfolding hash_range_budget_def
proof (intro allI impI)
  fix s y t
  assume outcome: "Some (y, t) \<in> set_dist (execute (m \<bind> k) s)"
  from outcome obtain x s1 where
    m_out: "Some (x, s1) \<in> set_dist (execute m s)"
    and k_out: "Some (y, t) \<in> set_dist (execute (k x) s1)"
    by (auto elim!: set_dist_bindE)
  have m_range:
    "card (hash_map_output_values s1) \<le>
      card (hash_map_output_values s) + n"
    using m m_out unfolding hash_range_budget_def by blast
  have k_range:
    "card (hash_map_output_values t) \<le>
      card (hash_map_output_values s1) + n'"
    using k[OF m_out] k_out unfolding hash_range_budget_def by blast
  show "card (hash_map_output_values t)
      \<le> card (hash_map_output_values s) + (n + n')"
    using m_range k_range by linarith
qed

lemma hash_new_collision_event_step_bound:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and s t :: "('f, 'a) protocol_channel_scheme"
  assumes clean: "\<not> hash_map_output_collision s"
  shows
    "wp_event m (hash_new_collision_event s) t \<le>
      (if hash_map_new_output_collision s t then 1
       else wp_event m (hash_new_collision_event t) t)"
proof (cases "hash_map_new_output_collision s t")
  case True
  then show ?thesis
    using wp_event_le_1[of m "hash_new_collision_event s" t] by simp
next
  case False
  then have clean_t: "\<not> hash_map_output_collision t"
    using clean unfolding hash_map_new_output_collision_def by simp
  have same:
    "hash_new_collision_event s out = hash_new_collision_event t out"
    for out :: "('x \<times> ('f, 'a) protocol_channel_scheme) option"
    using clean clean_t
    unfolding hash_new_collision_event_def hash_map_new_output_collision_def
    by (cases out) auto
  have "wp_event m (hash_new_collision_event s) t =
      wp_event m (hash_new_collision_event t) t"
    unfolding wp_event_def by (simp add: same)
  show ?thesis
    using False \<open>wp_event m (hash_new_collision_event s) t =
      wp_event m (hash_new_collision_event t) t\<close> by simp
qed

lemma hash_collision_budget_bind:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes range_m: "hash_range_budget n m"
    and coll_m: "hash_collision_budget n m"
    and range_k: "\<And>x. hash_range_budget n' (k x)"
    and coll_k: "\<And>x. hash_collision_budget n' (k x)"
  shows "hash_collision_budget (n + n') (m \<bind> k)"
  unfolding hash_collision_budget_def
proof (intro allI impI)
  fix s :: "('f, 'a) protocol_channel_scheme"
  assume clean: "\<not> hash_map_output_collision s"
  let ?c = "card (hash_map_output_values s)"
  let ?B1 = "hash_collision_budget_value ?c n"
  let ?B2 = "hash_collision_budget_value (?c + n) n'"
  let ?Em = "hash_new_collision_event s"
  let ?S =
    "\<lambda>out. case out of
      None \<Rightarrow> 0
    | Some (x, s1) \<Rightarrow>
        if hash_map_new_output_collision s s1 then 0
        else wp_event (k x) (hash_new_collision_event s1) s1"
  let ?R =
    "\<lambda>out. (if ?Em out then 1 else 0) + ?S out"
  have split:
    "wp_event (m \<bind> k) (hash_new_collision_event s) s \<le> wp m ?R s"
  proof -
    have exact:
      "wp_event (m \<bind> k) (hash_new_collision_event s) s =
        wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, s1) \<Rightarrow>
              wp_event (k x) (hash_new_collision_event s) s1) s"
      unfolding wp_event_def hash_new_collision_event_def
      by (simp add: wpsimps)
    have "wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, s1) \<Rightarrow>
              wp_event (k x) (hash_new_collision_event s) s1) s
        \<le> wp m ?R s"
    proof (rule wp_mono_on_support)
      fix out
      assume "out \<in> set_dist (execute m s)"
      show "(case out of
            None \<Rightarrow> 0
          | Some (x, s1) \<Rightarrow>
              wp_event (k x) (hash_new_collision_event s) s1) \<le> ?R out"
      proof (cases out)
        case None
        then show ?thesis
          unfolding hash_new_collision_event_def by simp
      next
        case (Some xs)
        then obtain x s1 where xs: "xs = (x, s1)"
          by (cases xs) simp
        have step:
          "wp_event (k x) (hash_new_collision_event s) s1 \<le>
            (if hash_map_new_output_collision s s1 then 1
             else wp_event (k x) (hash_new_collision_event s1) s1)"
          by (rule hash_new_collision_event_step_bound[OF clean])
        have R_eq:
          "?R out =
            (if hash_map_new_output_collision s s1 then 1
             else wp_event (k x) (hash_new_collision_event s1) s1)"
          using Some xs unfolding hash_new_collision_event_def by simp
        have L_eq:
          "(case out of
            None \<Rightarrow> 0
          | Some (x, s1) \<Rightarrow>
              wp_event (k x) (hash_new_collision_event s) s1) =
            wp_event (k x) (hash_new_collision_event s) s1"
          using Some xs by simp
        show ?thesis
          using step unfolding L_eq R_eq .
      qed
    qed
    then show ?thesis
      unfolding exact .
  qed
  have m_bound:
    "wp_event m ?Em s \<le> ?B1"
    using coll_m clean unfolding hash_collision_budget_def by blast
  have S_bound: "wp m ?S s \<le> ?B2"
  proof (rule wp_le_const_on_support)
    fix out
    assume out_support: "out \<in> set_dist (execute m s)"
    show "?S out \<le> ?B2"
    proof (cases out)
      case None
      then show ?thesis by simp
    next
      case (Some xs)
      then obtain x s1 where xs: "xs = (x, s1)"
        by (cases xs) simp
      show ?thesis
      proof (cases "hash_map_new_output_collision s s1")
        case True
        then show ?thesis
          using Some xs by simp
      next
        case False
        then have clean_s1: "\<not> hash_map_output_collision s1"
          using clean unfolding hash_map_new_output_collision_def by simp
        have k_bound:
          "wp_event (k x) (hash_new_collision_event s1) s1 \<le>
            hash_collision_budget_value
              (card (hash_map_output_values s1)) n'"
          using coll_k[of x] clean_s1 unfolding hash_collision_budget_def
          by blast
        have m_out:
          "Some (x, s1) \<in> set_dist (execute m s)"
          using out_support Some xs by simp
        have range:
          "card (hash_map_output_values s1) \<le> ?c + n"
          using range_m m_out unfolding hash_range_budget_def by blast
        have "hash_collision_budget_value
              (card (hash_map_output_values s1)) n' \<le> ?B2"
          by (rule hash_collision_budget_value_mono_left[OF range])
        then show ?thesis
          using Some xs False k_bound by simp
      qed
    qed
  qed
  have "wp_event (m \<bind> k) (hash_new_collision_event s) s
      \<le> wp m ?R s"
    by (rule split)
  also have "... =
      wp_event m ?Em s + wp m ?S s"
    unfolding wp_event_def wp_def dist_expect_def
    by (simp add: sum.distrib algebra_simps hash_new_collision_event_def)
  also have "... \<le> ?B1 + ?B2"
    using m_bound S_bound by (intro add_mono)
  also have "... \<le> hash_collision_budget_value ?c (n + n')"
    by (rule hash_collision_budget_value_bind_le)
  finally show
    "wp_event (m \<bind> k) (hash_new_collision_event s) s
      \<le> hash_collision_budget_value ?c (n + n')" .
qed

lemma hash_collision_budget_bind_on_outcomes:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
    and k :: "'x \<Rightarrow> ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes range_m: "hash_range_budget n m"
    and coll_m: "hash_collision_budget n m"
    and range_k:
      "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_range_budget n' (k x)"
    and coll_k:
      "\<And>s x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        hash_collision_budget n' (k x)"
  shows "hash_collision_budget (n + n') (m \<bind> k)"
  unfolding hash_collision_budget_def
proof (intro allI impI)
  fix s :: "('f, 'a) protocol_channel_scheme"
  assume clean: "\<not> hash_map_output_collision s"
  let ?c = "card (hash_map_output_values s)"
  let ?B1 = "hash_collision_budget_value ?c n"
  let ?B2 = "hash_collision_budget_value (?c + n) n'"
  let ?Em = "hash_new_collision_event s"
  let ?S =
    "\<lambda>out. case out of
      None \<Rightarrow> 0
    | Some (x, s1) \<Rightarrow>
        if hash_map_new_output_collision s s1 then 0
        else wp_event (k x) (hash_new_collision_event s1) s1"
  let ?R =
    "\<lambda>out. (if ?Em out then 1 else 0) + ?S out"
  have split:
    "wp_event (m \<bind> k) (hash_new_collision_event s) s \<le> wp m ?R s"
  proof -
    have exact:
      "wp_event (m \<bind> k) (hash_new_collision_event s) s =
        wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, s1) \<Rightarrow>
              wp_event (k x) (hash_new_collision_event s) s1) s"
      unfolding wp_event_def hash_new_collision_event_def
      by (simp add: wpsimps)
    have "wp m
          (\<lambda>out. case out of
            None \<Rightarrow> 0
          | Some (x, s1) \<Rightarrow>
              wp_event (k x) (hash_new_collision_event s) s1) s
        \<le> wp m ?R s"
    proof (rule wp_mono_on_support)
      fix out
      assume "out \<in> set_dist (execute m s)"
      show "(case out of
            None \<Rightarrow> 0
          | Some (x, s1) \<Rightarrow>
              wp_event (k x) (hash_new_collision_event s) s1) \<le> ?R out"
      proof (cases out)
        case None
        then show ?thesis
          unfolding hash_new_collision_event_def by simp
      next
        case (Some xs)
        then obtain x s1 where xs: "xs = (x, s1)"
          by (cases xs) simp
        have step:
          "wp_event (k x) (hash_new_collision_event s) s1 \<le>
            (if hash_map_new_output_collision s s1 then 1
             else wp_event (k x) (hash_new_collision_event s1) s1)"
          by (rule hash_new_collision_event_step_bound[OF clean])
        have R_eq:
          "?R out =
            (if hash_map_new_output_collision s s1 then 1
             else wp_event (k x) (hash_new_collision_event s1) s1)"
          using Some xs unfolding hash_new_collision_event_def by simp
        have L_eq:
          "(case out of
            None \<Rightarrow> 0
          | Some (x, s1) \<Rightarrow>
              wp_event (k x) (hash_new_collision_event s) s1) =
            wp_event (k x) (hash_new_collision_event s) s1"
          using Some xs by simp
        show ?thesis
          using step unfolding L_eq R_eq .
      qed
    qed
    then show ?thesis
      unfolding exact .
  qed
  have m_bound:
    "wp_event m ?Em s \<le> ?B1"
    using coll_m clean unfolding hash_collision_budget_def by blast
  have S_bound: "wp m ?S s \<le> ?B2"
  proof (rule wp_le_const_on_support)
    fix out
    assume out_support: "out \<in> set_dist (execute m s)"
    show "?S out \<le> ?B2"
    proof (cases out)
      case None
      then show ?thesis by simp
    next
      case (Some xs)
      then obtain x s1 where xs: "xs = (x, s1)"
        by (cases xs) simp
      have m_out:
        "Some (x, s1) \<in> set_dist (execute m s)"
        using out_support Some xs by simp
      show ?thesis
      proof (cases "hash_map_new_output_collision s s1")
        case True
        then show ?thesis
          using Some xs by simp
      next
        case False
        then have clean_s1: "\<not> hash_map_output_collision s1"
          using clean unfolding hash_map_new_output_collision_def by simp
        have k_bound:
          "wp_event (k x) (hash_new_collision_event s1) s1 \<le>
            hash_collision_budget_value
              (card (hash_map_output_values s1)) n'"
          using coll_k[OF m_out] clean_s1
          unfolding hash_collision_budget_def by blast
        have range:
          "card (hash_map_output_values s1) \<le> ?c + n"
          using range_m m_out unfolding hash_range_budget_def by blast
        have "hash_collision_budget_value
              (card (hash_map_output_values s1)) n' \<le> ?B2"
          by (rule hash_collision_budget_value_mono_left[OF range])
        then show ?thesis
          using Some xs False k_bound by simp
      qed
    qed
  qed
  have "wp_event (m \<bind> k) (hash_new_collision_event s) s
      \<le> wp m ?R s"
    by (rule split)
  also have "... =
      wp_event m ?Em s + wp m ?S s"
    unfolding wp_event_def wp_def dist_expect_def
    by (simp add: sum.distrib algebra_simps hash_new_collision_event_def)
  also have "... \<le> ?B1 + ?B2"
    using m_bound S_bound by (intro add_mono)
  also have "... \<le> hash_collision_budget_value ?c (n + n')"
    by (rule hash_collision_budget_value_bind_le)
  finally show
    "wp_event (m \<bind> k) (hash_new_collision_event s) s
      \<le> hash_collision_budget_value ?c (n + n')" .
qed

lemma wp_hash_new_output_collision_bound:
  fixes x :: "'f protocol_hash_input"
    and s :: "('f, 'a) protocol_channel_scheme"
  assumes clean: "\<not> hash_map_output_collision s"
  shows
    "wp_event (hash x)
      (hash_new_collision_event s) s
      \<le> nnreal (card (hash_map_output_values s)) / nnreal size"
proof (cases "fmlookup (HashMap s) x")
  case None
  let ?P =
    "\<lambda>y. hash_map_new_output_collision s
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)"
  let ?Q = "\<lambda>y. y \<in> hash_map_output_values s"
  have mono:
    "dist_expect (hash_dist x s) (\<lambda>y. if ?P y then 1 else 0) \<le>
      dist_expect (hash_dist x s) (\<lambda>y. if ?Q y then 1 else 0)"
    unfolding dist_expect_def
  proof (intro sum_mono)
    fix y
    assume "y \<in> dom (dist (hash_dist x s))"
    show "the (dist (hash_dist x s) y) * (if ?P y then 1 else 0)
        \<le> the (dist (hash_dist x s) y) * (if ?Q y then 1 else 0)"
    proof (cases "?P y")
      case True
      then have "?Q y"
        using hash_map_output_collision_after_fresh_updateD
          [OF clean None]
        unfolding hash_map_new_output_collision_def by simp
      then show ?thesis
        using True by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  show ?thesis
  proof -
    have "wp_event (hash x)
        (hash_new_collision_event s) s =
        dist_expect (hash_dist x s) (\<lambda>y. if ?P y then 1 else 0)"
      unfolding wp_event_def hash_new_collision_event_def
      by (simp add: wp_hash)
    also have "... \<le>
        dist_expect (hash_dist x s) (\<lambda>y. if ?Q y then 1 else 0)"
      by (rule mono)
    also have "... =
        nnreal (card (hash_map_output_values s)) / nnreal size"
      by (rule dist_expect_hash_dist_fresh_output_values[OF None])
    finally show ?thesis .
  qed
next
  case (Some y)
  have no_new:
    "\<not> hash_map_new_output_collision s
      (s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>)"
    using no_hash_map_output_collision_after_known_update[OF clean Some]
    unfolding hash_map_new_output_collision_def by simp
  show ?thesis
    unfolding wp_event_def hash_new_collision_event_def
    by (simp add: wp_hash Some hash_dist_def option_default_dist_def no_new)
qed

lemma hash_range_budget_return:
  "hash_range_budget 0 (return x)"
  unfolding hash_range_budget_def by simp

lemma hash_collision_budget_return:
  "hash_collision_budget 0 (return x)"
  unfolding hash_collision_budget_def hash_new_collision_event_def
    hash_collision_budget_value_def hash_map_new_output_collision_def
  by (simp add: wp_event_def wpsimps)

lemma hash_range_budget_hash:
  fixes x :: "'f protocol_hash_input"
  shows
    "hash_range_budget 1
      (hash x :: ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
  unfolding hash_range_budget_def
proof (intro allI impI)
  fix s y t
  assume outcome:
    "Some (y, t) \<in>
      set_dist (execute
        (hash x :: ('f, ('f, 'a) protocol_channel_scheme) state_monad) s)"
  have t_eq: "t = s\<lparr>HashMap := fmupd x y (HashMap s)\<rparr>"
  proof -
    from outcome obtain a s1 where
      apply_step:
        "Some (a, s1) \<in> set_dist (execute (apply_hash x) s)"
      and rest:
        "Some (y, t) \<in>
          set_dist (execute
            (modify_HashMap x a \<bind> (\<lambda>_. return a)) s1)"
    proof -
      have "Some (y, t) \<in>
        set_dist (execute
          (apply_hash x \<bind>
            (\<lambda>a. modify_HashMap x a \<bind> (\<lambda>_. return a))) s)"
        using outcome unfolding hash_def .
      then show ?thesis
        by (rule set_dist_bindE) (rule that)
    qed
    have apply_img:
      "Some (a, s1) \<in> (\<lambda>a. Some (a, s)) ` set_dist (hash_dist x s)"
      using apply_step
      unfolding apply_hash_def lift.rep_eq lift_dist_def
      by (simp add: set_dist_dist_map)
    then have s1_eq: "s1 = s"
      by auto
    from rest obtain u s2 where
      mod:
        "Some (u, s2) \<in> set_dist (execute (modify_HashMap x a) s1)"
      and ret:
        "Some (y, t) \<in> set_dist (execute (return a) s2)"
      by (elim set_dist_bindE)
    have s2_eq: "s2 = s1\<lparr>HashMap := fmupd x a (HashMap s1)\<rparr>"
      using mod unfolding modify_HashMap_def modify_def
      by (auto elim!: set_dist_bindE)
    have y_eq: "y = a" and t_eq_s2: "t = s2"
      using ret by auto
    show ?thesis
      using s1_eq s2_eq y_eq t_eq_s2 by simp
  qed
  show "card (hash_map_output_values t)
      \<le> card (hash_map_output_values s) + 1"
    unfolding t_eq
    using card_hash_map_output_values_after_update_le[of x y s]
    by simp
qed

lemma hash_collision_budget_hash:
  fixes x :: "'f protocol_hash_input"
  shows
    "hash_collision_budget 1
      (hash x :: ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
  unfolding hash_collision_budget_def
proof (intro allI impI)
  fix s :: "('f, 'a) protocol_channel_scheme"
  assume clean: "\<not> hash_map_output_collision s"
  have one_step:
    "wp_event (hash x) (hash_new_collision_event s) s \<le>
      nnreal (card (hash_map_output_values s)) / nnreal size"
    by (rule wp_hash_new_output_collision_bound[OF clean])
  also have "... \<le>
      hash_collision_budget_value (card (hash_map_output_values s)) 1"
    unfolding hash_collision_budget_value_def
    apply (subst nn2real_le_iff[symmetric])
    by (simp add: divide_right_mono)
  finally show
    "wp_event (hash x) (hash_new_collision_event s) s \<le>
      hash_collision_budget_value (card (hash_map_output_values s)) 1" .
qed

lemma hash_range_budget_get:
  "hash_range_budget 0
    (get :: (('f, 'a) protocol_channel_scheme,
      ('f, 'a) protocol_channel_scheme) state_monad)"
  unfolding hash_range_budget_def by simp

lemma hash_collision_budget_get:
  "hash_collision_budget 0
    (get :: (('f, 'a) protocol_channel_scheme,
      ('f, 'a) protocol_channel_scheme) state_monad)"
  unfolding hash_collision_budget_def hash_new_collision_event_def
    hash_map_new_output_collision_def hash_collision_budget_value_def
  by (simp add: wp_event_def wpsimps)

lemma hash_range_budget_assert:
  "hash_range_budget 0
    (assert b :: (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
  unfolding hash_range_budget_def assert_def
  by (auto simp: throw_no_outcome)

lemma hash_collision_budget_assert:
  "hash_collision_budget 0
    (assert b :: (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
  unfolding hash_collision_budget_def hash_new_collision_event_def
    hash_map_new_output_collision_def hash_collision_budget_value_def
    assert_def
  by (simp add: wp_event_def wpsimps)

lemma hash_range_budget_send:
  "hash_range_budget 0 (send x)"
  unfolding hash_range_budget_def send_def protocol_send_def modify_def
  by (auto simp: hash_map_output_values_def elim!: set_dist_bindE)

lemma hash_collision_budget_send:
  "hash_collision_budget 0 (send x)"
  unfolding hash_collision_budget_def hash_new_collision_event_def
    hash_map_new_output_collision_def hash_collision_budget_value_def
    hash_map_output_collision_def
    send_def protocol_send_def
  by (simp add: wp_event_def wpsimps)

lemma hash_range_budget_read:
  "hash_range_budget 0 (read :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding hash_range_budget_def
proof (intro allI impI)
  fix s x t
  assume out: "Some (x, t) \<in>
    set_dist (execute (read :: ('f, 'f, 'a) protocol_c_monad) s)"
  obtain y ys where tr: "PTranscript s = y # ys"
  proof -
    have "PTranscript s \<noteq> []"
      using out unfolding read_def protocol_read_def assert_def
      by (cases "PTranscript s")
        (auto simp: throw_no_outcome elim!: set_dist_bindE)
    then show ?thesis
      by (cases "PTranscript s") (auto intro: that)
  qed
  have t_eq:
    "t = s\<lparr>PState := concat (PState s) y, PTranscript := ys\<rparr>"
    using read_nonempty_outcome[OF out tr] by simp
  show "card (hash_map_output_values t)
      \<le> card (hash_map_output_values s) + 0"
    unfolding t_eq hash_map_output_values_def by simp
qed

lemma hash_collision_budget_read:
  "hash_collision_budget 0
    (read :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding hash_collision_budget_def hash_new_collision_event_def
    hash_map_new_output_collision_def hash_collision_budget_value_def
    hash_map_output_collision_def
    read_def protocol_read_def assert_def
  by (simp add: wp_event_def wpsimps)

lemma hash_range_budget_modify_preserves_hash_map:
  assumes "\<And>s. HashMap (f s) = HashMap s"
  shows "hash_range_budget 0 (modify f)"
  using assms
  unfolding hash_range_budget_def modify_def hash_map_output_values_def
  by (auto elim!: set_dist_bindE)

lemma hash_collision_budget_modify_preserves_hash_map:
  assumes "\<And>s. HashMap (f s) = HashMap s"
  shows "hash_collision_budget 0 (modify f)"
  using assms
  unfolding hash_collision_budget_def hash_new_collision_event_def
    hash_map_new_output_collision_def hash_collision_budget_value_def
    hash_map_output_collision_def modify_def
  by (simp add: wp_event_def wpsimps)

lemma hash_map_preserving_get:
  "hash_map_preserving
    (get :: (('f, 'a) protocol_channel_scheme,
      ('f, 'a) protocol_channel_scheme) state_monad)"
  unfolding hash_map_preserving_def by simp

lemma hash_map_preserving_assert:
  "hash_map_preserving
    (assert b :: (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
  unfolding hash_map_preserving_def assert_def
  by (auto simp: throw_no_outcome elim!: set_dist_bindE)

lemma hash_map_preserving_send:
  "hash_map_preserving (send x)"
  unfolding hash_map_preserving_def send_def protocol_send_def modify_def
  by (auto elim!: set_dist_bindE)

lemma hash_map_preserving_read:
  "hash_map_preserving (read :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding hash_map_preserving_def
proof (intro allI impI)
  fix s x t
  assume out:
    "Some (x, t) \<in>
      set_dist (execute (read :: ('f, 'f, 'a) protocol_c_monad) s)"
  obtain y ys where tr: "PTranscript s = y # ys"
  proof -
    have "PTranscript s \<noteq> []"
      using out unfolding read_def protocol_read_def assert_def
      by (cases "PTranscript s")
        (auto simp: throw_no_outcome elim!: set_dist_bindE)
    then show ?thesis
      by (cases "PTranscript s") (auto intro: that)
  qed
  have t_eq:
    "t = s\<lparr>PState := concat (PState s) y, PTranscript := ys\<rparr>"
    using read_nonempty_outcome[OF out tr] by simp
  show "HashMap t = HashMap s"
    unfolding t_eq by simp
qed

lemma hash_map_preserving_modify:
  assumes "\<And>s. HashMap (f s) = HashMap s"
  shows "hash_map_preserving (modify f)"
  using assms unfolding hash_map_preserving_def modify_def
  by (auto elim!: set_dist_bindE)

lemma hash_target_program_get:
  "hash_target_program B 0
    (get :: (('f, 'a) protocol_channel_scheme,
      ('f, 'a) protocol_channel_scheme) state_monad)"
  by (rule hash_map_preserving_imp_hash_target_program_zero)
    (rule hash_map_preserving_get)

lemma hash_target_program_assert:
  "hash_target_program B 0
    (assert b :: (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
  by (rule hash_map_preserving_imp_hash_target_program_zero)
    (rule hash_map_preserving_assert)

lemma hash_target_program_send:
  "hash_target_program B 0 (send x)"
  by (rule hash_map_preserving_imp_hash_target_program_zero)
    (rule hash_map_preserving_send)

lemma hash_target_program_read:
  "hash_target_program B 0 (read :: ('f, 'f, 'a) protocol_c_monad)"
  by (rule hash_map_preserving_imp_hash_target_program_zero)
    (rule hash_map_preserving_read)

lemma hash_target_program_ntimes_read_bind:
  fixes k :: "'f list \<Rightarrow>
    ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes k:
    "\<And>xs. length xs = n \<Longrightarrow> hash_target_program B b (k xs)"
  shows
    "hash_target_program B b
      ((ntimes read n ::
        ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind> k)"
proof -
  have reads:
    "hash_target_program B (n * 0)
      (ntimes read n ::
        ('f list, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_target_program_ntimes[OF hash_target_program_read])
  have "hash_target_program B (n * 0 + b)
      ((ntimes read n ::
        ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind> k)"
  proof (rule hash_target_program_bind_on_outcomes[OF reads])
    fix s xs t
    assume out:
      "Some (xs, t) \<in>
        set_dist (execute
          (ntimes read n ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) s)"
    show "hash_target_program B b (k xs)"
      by (rule k) (use ntimes_read_any_outcome[OF out] in simp)
  qed
  then show ?thesis by simp
qed

lemma hash_target_program_modify:
  assumes "\<And>s. HashMap (f s) = HashMap s"
  shows "hash_target_program B 0 (modify f)"
  by (rule hash_map_preserving_imp_hash_target_program_zero)
    (rule hash_map_preserving_modify[OF assms])

lemma hash_range_budget_protocol_absorb_message:
  "hash_range_budget 1 (protocol_absorb_message x)"
proof -
  have get_step:
    "hash_range_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_get)
  have hash_then_modify:
    "hash_range_budget (1 + 0)
      (hash (TranscriptAbsorb (PState s) x) \<bind>
        (\<lambda>h. modify
          (\<lambda>s. s\<lparr>PState := h,
            PTranscript := x # PTranscript s\<rparr>)) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash,
       rule hash_range_budget_modify_preserves_hash_map, simp)
  have "hash_range_budget (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          hash (TranscriptAbsorb (PState s) x) \<bind>
            (\<lambda>h. modify
              (\<lambda>s. s\<lparr>PState := h,
                PTranscript := x # PTranscript s\<rparr>))))"
    by (rule hash_range_budget_bind[OF get_step hash_then_modify])
  then show ?thesis
    unfolding protocol_absorb_message_def
    by simp
qed

lemma hash_collision_budget_protocol_absorb_message:
  "hash_collision_budget 1 (protocol_absorb_message x)"
proof -
  have get_range:
    "hash_range_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_get)
  have get_coll:
    "hash_collision_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_collision_budget_get)
  have hash_then_modify_range:
    "hash_range_budget (1 + 0)
      (hash (TranscriptAbsorb (PState s) x) \<bind>
        (\<lambda>h. modify
          (\<lambda>s. s\<lparr>PState := h,
            PTranscript := x # PTranscript s\<rparr>)) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash,
       rule hash_range_budget_modify_preserves_hash_map, simp)
  have hash_then_modify_coll:
    "hash_collision_budget (1 + 0)
      (hash (TranscriptAbsorb (PState s) x) \<bind>
        (\<lambda>h. modify
          (\<lambda>s. s\<lparr>PState := h,
            PTranscript := x # PTranscript s\<rparr>)) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_hash, rule hash_collision_budget_hash,
       rule hash_range_budget_modify_preserves_hash_map, simp,
       rule hash_collision_budget_modify_preserves_hash_map, simp)
  have "hash_collision_budget (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          hash (TranscriptAbsorb (PState s) x) \<bind>
            (\<lambda>h. modify
              (\<lambda>s. s\<lparr>PState := h,
                PTranscript := x # PTranscript s\<rparr>))))"
    by (rule hash_collision_budget_bind[OF get_range get_coll
          hash_then_modify_range hash_then_modify_coll])
  then show ?thesis
    unfolding protocol_absorb_message_def
    by simp
qed

lemma hash_target_program_protocol_absorb_message:
  "hash_target_program B 1 (protocol_absorb_message x)"
proof -
  have hash_then_modify:
    "hash_target_program B (1 + 0)
      (hash (TranscriptAbsorb (PState s) x) \<bind>
        (\<lambda>h. modify
          (\<lambda>s. s\<lparr>PState := h,
            PTranscript := x # PTranscript s\<rparr>)) ::
        (unit, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_target_program_bind)
      (rule hash_target_program_hash,
       rule hash_target_program_modify, simp)
  have "hash_target_program B (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          hash (TranscriptAbsorb (PState s) x) \<bind>
            (\<lambda>h. modify
              (\<lambda>s. s\<lparr>PState := h,
                PTranscript := x # PTranscript s\<rparr>))))"
    by (rule hash_target_program_bind[OF hash_target_program_get
          hash_then_modify])
  then show ?thesis
    unfolding protocol_absorb_message_def
    by simp
qed

lemma hash_range_budget_protocol_absorb_read:
  "hash_range_budget 1
    (protocol_absorb_read :: ('f, 'f, 'a) protocol_c_monad)"
proof -
  have get_step:
    "hash_range_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_get)
  have modify_then_return:
    "hash_range_budget (0 + 0)
      (modify
        (\<lambda>t. t\<lparr>PState := h,
          PTranscript := tl (PTranscript t)\<rparr>) \<bind>
        (\<lambda>_. return (hd (PTranscript s))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme" and h :: 'f
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_modify_preserves_hash_map, simp,
       rule hash_range_budget_return)
  have hash_then_tail:
    "hash_range_budget (1 + (0 + 0))
      (hash (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
        (\<lambda>h. modify
          (\<lambda>t. t\<lparr>PState := h,
            PTranscript := tl (PTranscript t)\<rparr>) \<bind>
          (\<lambda>_. return (hd (PTranscript s)))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash, rule modify_then_return)
  have assert_then_tail:
    "hash_range_budget (0 + (1 + (0 + 0)))
      (assert (PTranscript s \<noteq> []) \<bind>
        (\<lambda>_. hash
          (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
          (\<lambda>h. modify
            (\<lambda>t. t\<lparr>PState := h,
              PTranscript := tl (PTranscript t)\<rparr>) \<bind>
            (\<lambda>_. return (hd (PTranscript s))))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_assert, rule hash_then_tail)
  have "hash_range_budget (0 + (0 + (1 + (0 + 0))))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          assert (PTranscript s \<noteq> []) \<bind>
            (\<lambda>_. hash
              (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
              (\<lambda>h. modify
                (\<lambda>t. t\<lparr>PState := h,
                  PTranscript := tl (PTranscript t)\<rparr>) \<bind>
                (\<lambda>_. return (hd (PTranscript s)))))))"
    by (rule hash_range_budget_bind[OF get_step assert_then_tail])
  then show ?thesis
    unfolding protocol_absorb_read_def
    by simp
qed

lemma hash_collision_budget_protocol_absorb_read:
  "hash_collision_budget 1
    (protocol_absorb_read :: ('f, 'f, 'a) protocol_c_monad)"
proof -
  have get_range:
    "hash_range_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_get)
  have get_coll:
    "hash_collision_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_collision_budget_get)
  have modify_then_return_range:
    "hash_range_budget (0 + 0)
      (modify
        (\<lambda>t. t\<lparr>PState := h,
          PTranscript := tl (PTranscript t)\<rparr>) \<bind>
        (\<lambda>_. return (hd (PTranscript s))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme" and h :: 'f
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_modify_preserves_hash_map, simp,
       rule hash_range_budget_return)
  have modify_then_return_coll:
    "hash_collision_budget (0 + 0)
      (modify
        (\<lambda>t. t\<lparr>PState := h,
          PTranscript := tl (PTranscript t)\<rparr>) \<bind>
        (\<lambda>_. return (hd (PTranscript s))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme" and h :: 'f
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_modify_preserves_hash_map, simp,
       rule hash_collision_budget_modify_preserves_hash_map, simp,
       rule hash_range_budget_return,
       rule hash_collision_budget_return)
  have hash_then_tail_range:
    "hash_range_budget (1 + (0 + 0))
      (hash (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
        (\<lambda>h. modify
          (\<lambda>t. t\<lparr>PState := h,
            PTranscript := tl (PTranscript t)\<rparr>) \<bind>
          (\<lambda>_. return (hd (PTranscript s)))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash, rule modify_then_return_range)
  have hash_then_tail_coll:
    "hash_collision_budget (1 + (0 + 0))
      (hash (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
        (\<lambda>h. modify
          (\<lambda>t. t\<lparr>PState := h,
            PTranscript := tl (PTranscript t)\<rparr>) \<bind>
          (\<lambda>_. return (hd (PTranscript s)))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_hash, rule hash_collision_budget_hash,
       rule modify_then_return_range,
       rule modify_then_return_coll)
  have assert_then_tail_range:
    "hash_range_budget (0 + (1 + (0 + 0)))
      (assert (PTranscript s \<noteq> []) \<bind>
        (\<lambda>_. hash
          (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
          (\<lambda>h. modify
            (\<lambda>t. t\<lparr>PState := h,
              PTranscript := tl (PTranscript t)\<rparr>) \<bind>
            (\<lambda>_. return (hd (PTranscript s))))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_assert, rule hash_then_tail_range)
  have assert_then_tail_coll:
    "hash_collision_budget (0 + (1 + (0 + 0)))
      (assert (PTranscript s \<noteq> []) \<bind>
        (\<lambda>_. hash
          (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
          (\<lambda>h. modify
            (\<lambda>t. t\<lparr>PState := h,
              PTranscript := tl (PTranscript t)\<rparr>) \<bind>
            (\<lambda>_. return (hd (PTranscript s))))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_assert,
       rule hash_collision_budget_assert,
       rule hash_then_tail_range,
       rule hash_then_tail_coll)
  have "hash_collision_budget (0 + (0 + (1 + (0 + 0))))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          assert (PTranscript s \<noteq> []) \<bind>
            (\<lambda>_. hash
              (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
              (\<lambda>h. modify
                (\<lambda>t. t\<lparr>PState := h,
                  PTranscript := tl (PTranscript t)\<rparr>) \<bind>
                (\<lambda>_. return (hd (PTranscript s)))))))"
    by (rule hash_collision_budget_bind[OF get_range get_coll
          assert_then_tail_range assert_then_tail_coll])
  then show ?thesis
    unfolding protocol_absorb_read_def
    by simp
qed

lemma hash_target_program_protocol_absorb_read:
  "hash_target_program B 1
    (protocol_absorb_read :: ('f, 'f, 'a) protocol_c_monad)"
proof -
  have modify_then_return:
    "hash_target_program B (0 + 0)
      (modify
        (\<lambda>t. t\<lparr>PState := h,
          PTranscript := tl (PTranscript t)\<rparr>) \<bind>
        (\<lambda>_. return (hd (PTranscript s))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme" and h :: 'f
    by (rule hash_target_program_bind)
      (rule hash_target_program_modify, simp,
       rule hash_target_program_return)
  have hash_then_tail:
    "hash_target_program B (1 + (0 + 0))
      (hash (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
        (\<lambda>h. modify
          (\<lambda>t. t\<lparr>PState := h,
            PTranscript := tl (PTranscript t)\<rparr>) \<bind>
          (\<lambda>_. return (hd (PTranscript s)))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_target_program_bind)
      (rule hash_target_program_hash,
       rule modify_then_return)
  have assert_then_tail:
    "hash_target_program B (0 + (1 + (0 + 0)))
      (assert (PTranscript s \<noteq> []) \<bind>
        (\<lambda>_. hash
          (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
          (\<lambda>h. modify
            (\<lambda>t. t\<lparr>PState := h,
              PTranscript := tl (PTranscript t)\<rparr>) \<bind>
            (\<lambda>_. return (hd (PTranscript s))))) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_target_program_bind)
      (rule hash_target_program_assert, rule hash_then_tail)
  have "hash_target_program B (0 + (0 + (1 + (0 + 0))))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          assert (PTranscript s \<noteq> []) \<bind>
            (\<lambda>_. hash
              (TranscriptAbsorb (PState s) (hd (PTranscript s))) \<bind>
              (\<lambda>h. modify
                (\<lambda>t. t\<lparr>PState := h,
                  PTranscript := tl (PTranscript t)\<rparr>) \<bind>
                (\<lambda>_. return (hd (PTranscript s)))))))"
    by (rule hash_target_program_bind[OF hash_target_program_get
          assert_then_tail])
  then show ?thesis
    unfolding protocol_absorb_read_def
    by simp
qed
lemma hash_target_program_receive_random_field_element:
  "hash_target_program B 1
    (receive_random_field_element :: ('f, 'f, 'a) protocol_c_monad)"
proof -
  have tail:
    "hash_target_program B (1 + 0)
      (hash (FiatShamirChallenge (PState s)) \<bind> return ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_target_program_bind)
      (rule hash_target_program_hash, rule hash_target_program_return)
  have "hash_target_program B (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          hash (FiatShamirChallenge (PState s)) \<bind> return))"
    by (rule hash_target_program_bind[OF hash_target_program_get tail])
  then show ?thesis
    unfolding receive_random_field_element_def
      protocol_receive_random_field_element_def
      protocol_receive_tagged_random_field_element_def
    by simp
qed

lemma hash_target_program_receive_tagged_random_field_element:
  "hash_target_program B 1
    (receive_tagged_random_field_element tag ::
      ('f, 'f, 'a) protocol_c_monad)"
proof -
  have tail:
    "hash_target_program B (1 + 0)
      (hash (tag (PState s)) \<bind> return ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_target_program_bind)
      (rule hash_target_program_hash, rule hash_target_program_return)
  have "hash_target_program B (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          hash (tag (PState s)) \<bind> return))"
    by (rule hash_target_program_bind[OF hash_target_program_get tail])
  then show ?thesis
    unfolding receive_tagged_random_field_element_def
      protocol_receive_tagged_random_field_element_def
    by simp
qed

lemma hash_target_program_receive_counted_tagged_random_field_element:
  assumes bump: "\<And>s. HashMap (bump s) = HashMap s"
  shows "hash_target_program B 1
    (protocol_receive_counted_tagged_random_field_element counter bump tag ::
      ('f, 'f, 'a) protocol_c_monad)"
proof -
  have modify_return:
    "hash_target_program B (0 + 0)
      (modify bump \<bind> (\<lambda>_. return r) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for r :: 'f
    by (rule hash_target_program_bind)
      (rule hash_target_program_modify[OF bump],
        rule hash_target_program_return)
  have hash_tail:
    "hash_target_program B (1 + (0 + 0))
      (hash (tag (counter s) (PState s)) \<bind>
        (\<lambda>r. modify bump \<bind> (\<lambda>_. return r)) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_target_program_bind)
      (rule hash_target_program_hash, rule modify_return)
  have "hash_target_program B (0 + (1 + (0 + 0)))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          hash (tag (counter s) (PState s)) \<bind>
            (\<lambda>r. modify bump \<bind> (\<lambda>_. return r))))"
    by (rule hash_target_program_bind[OF hash_target_program_get hash_tail])
  then show ?thesis
    unfolding protocol_receive_counted_tagged_random_field_element_def
    by simp
qed

lemma hash_target_program_receive_alpha_challenge:
  "hash_target_program B 1
    (receive_alpha_challenge :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding receive_alpha_challenge_def
  by (rule hash_target_program_receive_counted_tagged_random_field_element)
    simp

lemma hash_target_program_receive_query_index_challenge:
  "hash_target_program B 1
    (receive_query_index_challenge :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding receive_query_index_challenge_def
  by (rule hash_target_program_receive_counted_tagged_random_field_element)
    simp

lemma hash_target_program_receive_trace_fri_challenge:
  "hash_target_program B 1
    (receive_trace_fri_challenge :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding receive_trace_fri_challenge_def
  by (rule hash_target_program_receive_counted_tagged_random_field_element)
    simp

lemma hash_target_program_receive_composition_fri_challenge:
  "hash_target_program B 1
    (receive_composition_fri_challenge :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding receive_composition_fri_challenge_def
  by (rule hash_target_program_receive_counted_tagged_random_field_element)
    simp

lemma hash_range_budget_receive_random_field_element:
  "hash_range_budget 1
    (receive_random_field_element :: ('f, 'f, 'a) protocol_c_monad)"
proof -
  have get_step:
    "hash_range_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_get)
  have hash_then_return:
    "hash_range_budget (1 + 0)
      (hash (FiatShamirChallenge (PState s)) \<bind> return ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash, rule hash_range_budget_return)
  have "hash_range_budget (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          hash (FiatShamirChallenge (PState s)) \<bind> return))"
    by (rule hash_range_budget_bind[OF get_step hash_then_return])
  then show ?thesis
    unfolding receive_random_field_element_def
      protocol_receive_random_field_element_def
      protocol_receive_tagged_random_field_element_def
    by simp
qed

lemma hash_range_budget_receive_tagged_random_field_element:
  "hash_range_budget 1
    (receive_tagged_random_field_element tag :: ('f, 'f, 'a) protocol_c_monad)"
proof -
  have get_step:
    "hash_range_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_get)
  have hash_then_return:
    "hash_range_budget (1 + 0)
      (hash (tag (PState s)) \<bind> return ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash, rule hash_range_budget_return)
  have "hash_range_budget (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          hash (tag (PState s)) \<bind> return))"
    by (rule hash_range_budget_bind[OF get_step hash_then_return])
  then show ?thesis
    unfolding receive_tagged_random_field_element_def
      protocol_receive_tagged_random_field_element_def
    by simp
qed

lemma hash_range_budget_receive_counted_tagged_random_field_element:
  assumes bump: "\<And>s. HashMap (bump s) = HashMap s"
  shows "hash_range_budget 1
    (protocol_receive_counted_tagged_random_field_element counter bump tag ::
      ('f, 'f, 'a) protocol_c_monad)"
proof -
  have get_step:
    "hash_range_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_get)
  have modify_return:
    "hash_range_budget (0 + 0)
      (modify bump \<bind> (\<lambda>_. return r) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for r :: 'f
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_modify_preserves_hash_map[OF bump],
        rule hash_range_budget_return)
  have hash_then_tail:
    "hash_range_budget (1 + (0 + 0))
      (hash (tag (counter s) (PState s)) \<bind>
        (\<lambda>r. modify bump \<bind> (\<lambda>_. return r)) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash, rule modify_return)
  have "hash_range_budget (0 + (1 + (0 + 0)))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          hash (tag (counter s) (PState s)) \<bind>
            (\<lambda>r. modify bump \<bind> (\<lambda>_. return r))))"
    by (rule hash_range_budget_bind[OF get_step hash_then_tail])
  then show ?thesis
    unfolding protocol_receive_counted_tagged_random_field_element_def
    by simp
qed

lemma hash_range_budget_receive_alpha_challenge:
  "hash_range_budget 1
    (receive_alpha_challenge :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding receive_alpha_challenge_def
  by (rule hash_range_budget_receive_counted_tagged_random_field_element) simp

lemma hash_range_budget_receive_query_index_challenge:
  "hash_range_budget 1
    (receive_query_index_challenge :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding receive_query_index_challenge_def
  by (rule hash_range_budget_receive_counted_tagged_random_field_element) simp

lemma hash_range_budget_receive_trace_fri_challenge:
  "hash_range_budget 1
    (receive_trace_fri_challenge :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding receive_trace_fri_challenge_def
  by (rule hash_range_budget_receive_counted_tagged_random_field_element) simp

lemma hash_range_budget_receive_composition_fri_challenge:
  "hash_range_budget 1
    (receive_composition_fri_challenge :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding receive_composition_fri_challenge_def
  by (rule hash_range_budget_receive_counted_tagged_random_field_element) simp

lemma hash_collision_budget_receive_random_field_element:
  "hash_collision_budget 1
    (receive_random_field_element :: ('f, 'f, 'a) protocol_c_monad)"
proof -
  have get_range:
    "hash_range_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_get)
  have get_coll:
    "hash_collision_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_collision_budget_get)
  have hash_then_return_range:
    "hash_range_budget (1 + 0)
      (hash (FiatShamirChallenge (PState s)) \<bind> return ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash, rule hash_range_budget_return)
  have hash_then_return_coll:
    "hash_collision_budget (1 + 0)
      (hash (FiatShamirChallenge (PState s)) \<bind> return ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_hash, rule hash_collision_budget_hash,
        rule hash_range_budget_return, rule hash_collision_budget_return)
  have "hash_collision_budget (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          hash (FiatShamirChallenge (PState s)) \<bind> return))"
    by (rule hash_collision_budget_bind
        [OF get_range get_coll hash_then_return_range
          hash_then_return_coll])
  then show ?thesis
    unfolding receive_random_field_element_def
      protocol_receive_random_field_element_def
      protocol_receive_tagged_random_field_element_def
    by simp
qed

lemma hash_collision_budget_receive_tagged_random_field_element:
  "hash_collision_budget 1
    (receive_tagged_random_field_element tag :: ('f, 'f, 'a) protocol_c_monad)"
proof -
  have get_range:
    "hash_range_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_get)
  have get_coll:
    "hash_collision_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_collision_budget_get)
  have hash_then_return_range:
    "hash_range_budget (1 + 0)
      (hash (tag (PState s)) \<bind> return ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash, rule hash_range_budget_return)
  have hash_then_return_coll:
    "hash_collision_budget (1 + 0)
      (hash (tag (PState s)) \<bind> return ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_hash, rule hash_collision_budget_hash,
        rule hash_range_budget_return, rule hash_collision_budget_return)
  have "hash_collision_budget (0 + (1 + 0))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          hash (tag (PState s)) \<bind> return))"
    by (rule hash_collision_budget_bind
        [OF get_range get_coll hash_then_return_range
          hash_then_return_coll])
  then show ?thesis
    unfolding receive_tagged_random_field_element_def
      protocol_receive_tagged_random_field_element_def
    by simp
qed

lemma hash_collision_budget_receive_counted_tagged_random_field_element:
  assumes bump: "\<And>s. HashMap (bump s) = HashMap s"
  shows "hash_collision_budget 1
    (protocol_receive_counted_tagged_random_field_element counter bump tag ::
      ('f, 'f, 'a) protocol_c_monad)"
proof -
  have get_range:
    "hash_range_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_get)
  have get_coll:
    "hash_collision_budget 0
      (get :: (('f, 'a) protocol_channel_scheme,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_collision_budget_get)
  have modify_return_range:
    "hash_range_budget (0 + 0)
      (modify bump \<bind> (\<lambda>_. return r) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for r :: 'f
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_modify_preserves_hash_map[OF bump],
        rule hash_range_budget_return)
  have modify_return_coll:
    "hash_collision_budget (0 + 0)
      (modify bump \<bind> (\<lambda>_. return r) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for r :: 'f
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_modify_preserves_hash_map[OF bump],
        rule hash_collision_budget_modify_preserves_hash_map[OF bump],
        rule hash_range_budget_return, rule hash_collision_budget_return)
  have hash_then_tail_range:
    "hash_range_budget (1 + (0 + 0))
      (hash (tag (counter s) (PState s)) \<bind>
        (\<lambda>r. modify bump \<bind> (\<lambda>_. return r)) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_hash, rule modify_return_range)
  have hash_then_tail_coll:
    "hash_collision_budget (1 + (0 + 0))
      (hash (tag (counter s) (PState s)) \<bind>
        (\<lambda>r. modify bump \<bind> (\<lambda>_. return r)) ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    for s :: "('f, 'a) protocol_channel_scheme"
    by (rule hash_collision_budget_bind)
      (rule hash_range_budget_hash, rule hash_collision_budget_hash,
        rule modify_return_range, rule modify_return_coll)
  have "hash_collision_budget (0 + (1 + (0 + 0)))
      (get \<bind>
        (\<lambda>s :: ('f, 'a) protocol_channel_scheme.
          hash (tag (counter s) (PState s)) \<bind>
            (\<lambda>r. modify bump \<bind> (\<lambda>_. return r))))"
    by (rule hash_collision_budget_bind
        [OF get_range get_coll hash_then_tail_range hash_then_tail_coll])
  then show ?thesis
    unfolding protocol_receive_counted_tagged_random_field_element_def
    by simp
qed

lemma hash_collision_budget_receive_alpha_challenge:
  "hash_collision_budget 1
    (receive_alpha_challenge :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding receive_alpha_challenge_def
  by (rule hash_collision_budget_receive_counted_tagged_random_field_element) simp

lemma hash_collision_budget_receive_query_index_challenge:
  "hash_collision_budget 1
    (receive_query_index_challenge :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding receive_query_index_challenge_def
  by (rule hash_collision_budget_receive_counted_tagged_random_field_element) simp

lemma hash_collision_budget_receive_trace_fri_challenge:
  "hash_collision_budget 1
    (receive_trace_fri_challenge :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding receive_trace_fri_challenge_def
  by (rule hash_collision_budget_receive_counted_tagged_random_field_element) simp

lemma hash_collision_budget_receive_composition_fri_challenge:
  "hash_collision_budget 1
    (receive_composition_fri_challenge :: ('f, 'f, 'a) protocol_c_monad)"
  unfolding receive_composition_fri_challenge_def
  by (rule hash_collision_budget_receive_counted_tagged_random_field_element) simp

lemma hash_range_budget_ntimes:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes m: "hash_range_budget n m"
  shows "hash_range_budget (k * n) (ntimes m k)"
  using m
proof (induction k)
  case 0
  then show ?case
    by (simp add: hash_range_budget_return)
next
  case (Suc k)
  have tail: "hash_range_budget (k * n) (ntimes m k)"
    using Suc.IH Suc.prems by simp
  have cont:
    "hash_range_budget (k * n + 0)
      (ntimes m k \<bind> (\<lambda>xs. return (x # xs)))" for x
    by (rule hash_range_budget_bind[OF tail hash_range_budget_return])
  have "hash_range_budget (n + (k * n + 0))
      (m \<bind> (\<lambda>x. ntimes m k \<bind> (\<lambda>xs. return (x # xs))))"
    by (rule hash_range_budget_bind[OF Suc.prems cont])
  then show ?case
    by simp
qed

lemma hash_collision_budget_ntimes:
  fixes m :: "('x, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes range_m: "hash_range_budget n m"
    and coll_m: "hash_collision_budget n m"
  shows "hash_collision_budget (k * n) (ntimes m k)"
  using range_m coll_m
proof (induction k)
  case 0
  then show ?case
    by (simp add: hash_collision_budget_return)
next
  case (Suc k)
  have tail_range: "hash_range_budget (k * n) (ntimes m k)"
    by (rule hash_range_budget_ntimes[OF Suc.prems(1)])
  have tail_coll: "hash_collision_budget (k * n) (ntimes m k)"
    using Suc.IH Suc.prems by simp
  have cont_range:
    "hash_range_budget (k * n + 0)
      (ntimes m k \<bind> (\<lambda>xs. return (x # xs)))" for x
    by (rule hash_range_budget_bind[OF tail_range hash_range_budget_return])
  have cont_coll:
    "hash_collision_budget (k * n + 0)
      (ntimes m k \<bind> (\<lambda>xs. return (x # xs)))" for x
    by (rule hash_collision_budget_bind
        [OF tail_range tail_coll hash_range_budget_return
          hash_collision_budget_return])
  have "hash_collision_budget (n + (k * n + 0))
      (m \<bind> (\<lambda>x. ntimes m k \<bind> (\<lambda>xs. return (x # xs))))"
    by (rule hash_collision_budget_bind
        [OF Suc.prems(1) Suc.prems(2) cont_range cont_coll])
  then show ?case
    by simp
qed

lemma hash_range_budget_ntimes_read_bind:
  fixes k :: "'f list \<Rightarrow>
    ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes k: "\<And>xs. length xs = n \<Longrightarrow> hash_range_budget b (k xs)"
  shows
    "hash_range_budget b
      ((ntimes read n :: ('f list, ('f, 'a) protocol_channel_scheme) state_monad)
        \<bind> k)"
proof -
  have read_range:
    "hash_range_budget (n * 0)
      (ntimes read n :: ('f list, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_ntimes[OF hash_range_budget_read])
  have "hash_range_budget (n * 0 + b)
      ((ntimes read n :: ('f list, ('f, 'a) protocol_channel_scheme) state_monad)
        \<bind> k)"
  proof (rule hash_range_budget_bind_on_outcomes[OF read_range])
    fix s xs t
    assume out:
      "Some (xs, t) \<in>
        set_dist (execute
          (ntimes read n ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) s)"
    show "hash_range_budget b (k xs)"
      by (rule k) (use ntimes_read_any_outcome[OF out] in simp)
  qed
  then show ?thesis by simp
qed

lemma hash_collision_budget_ntimes_read_bind:
  fixes k :: "'f list \<Rightarrow>
    ('y, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes range_k: "\<And>xs. length xs = n \<Longrightarrow> hash_range_budget b (k xs)"
    and coll_k: "\<And>xs. length xs = n \<Longrightarrow> hash_collision_budget b (k xs)"
  shows
    "hash_collision_budget b
      ((ntimes read n :: ('f list, ('f, 'a) protocol_channel_scheme) state_monad)
        \<bind> k)"
proof -
  have read_range:
    "hash_range_budget (n * 0)
      (ntimes read n :: ('f list, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_ntimes[OF hash_range_budget_read])
  have read_coll:
    "hash_collision_budget (n * 0)
      (ntimes read n :: ('f list, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_collision_budget_ntimes
        [OF hash_range_budget_read hash_collision_budget_read])
  have "hash_collision_budget (n * 0 + b)
      ((ntimes read n :: ('f list, ('f, 'a) protocol_channel_scheme) state_monad)
        \<bind> k)"
  proof (rule hash_collision_budget_bind_on_outcomes
      [OF read_range read_coll])
    fix s xs t
    assume out:
      "Some (xs, t) \<in>
        set_dist (execute
          (ntimes read n ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) s)"
    have len: "length xs = n"
      using ntimes_read_any_outcome[OF out] by simp
    show "hash_range_budget b (k xs)"
      by (rule range_k[OF len])
    show "hash_collision_budget b (k xs)"
      by (rule coll_k[OF len])
  qed
  then show ?thesis by simp
qed

lemma hash_range_budget_mmap:
  fixes ms :: "('x, ('f, 'a) protocol_channel_scheme) state_monad list"
  assumes ms: "\<And>m. m \<in> set ms \<Longrightarrow> hash_range_budget n m"
  shows "hash_range_budget (length ms * n) (mmap ms)"
  using ms
proof (induction ms)
  case Nil
  then show ?case
    by (simp add: hash_range_budget_return)
next
  case (Cons m ms)
  have head: "hash_range_budget n m"
    using Cons.prems by simp
  have tail: "hash_range_budget (length ms * n) (mmap ms)"
    using Cons.IH Cons.prems by simp
  have cont:
    "hash_range_budget (length ms * n + 0)
      (mmap ms \<bind> (\<lambda>xs. return (x # xs)))" for x
    by (rule hash_range_budget_bind[OF tail hash_range_budget_return])
  have "hash_range_budget (n + (length ms * n + 0))
      (m \<bind> (\<lambda>x. mmap ms \<bind> (\<lambda>xs. return (x # xs))))"
    by (rule hash_range_budget_bind[OF head cont])
  then show ?case
    by simp
qed

lemma hash_collision_budget_mmap:
  fixes ms :: "('x, ('f, 'a) protocol_channel_scheme) state_monad list"
  assumes range_ms: "\<And>m. m \<in> set ms \<Longrightarrow> hash_range_budget n m"
    and coll_ms: "\<And>m. m \<in> set ms \<Longrightarrow> hash_collision_budget n m"
  shows "hash_collision_budget (length ms * n) (mmap ms)"
  using range_ms coll_ms
proof (induction ms)
  case Nil
  then show ?case
    by (simp add: hash_collision_budget_return)
next
  case (Cons m ms)
  have head_range: "hash_range_budget n m"
    using Cons.prems by simp
  have head_coll: "hash_collision_budget n m"
    using Cons.prems by simp
  have tail_range: "hash_range_budget (length ms * n) (mmap ms)"
    by (rule hash_range_budget_mmap) (use Cons.prems in auto)
  have tail_coll: "hash_collision_budget (length ms * n) (mmap ms)"
    using Cons.IH Cons.prems by simp
  have cont_range:
    "hash_range_budget (length ms * n + 0)
      (mmap ms \<bind> (\<lambda>xs. return (x # xs)))" for x
    by (rule hash_range_budget_bind[OF tail_range hash_range_budget_return])
  have cont_coll:
    "hash_collision_budget (length ms * n + 0)
      (mmap ms \<bind> (\<lambda>xs. return (x # xs)))" for x
    by (rule hash_collision_budget_bind
        [OF tail_range tail_coll hash_range_budget_return
          hash_collision_budget_return])
  have "hash_collision_budget (n + (length ms * n + 0))
      (m \<bind> (\<lambda>x. mmap ms \<bind> (\<lambda>xs. return (x # xs))))"
    by (rule hash_collision_budget_bind
        [OF head_range head_coll cont_range cont_coll])
  then show ?case
    by simp
qed

lemma hash_range_budget_mfold:
  fixes steps :: "('x \<Rightarrow> ('x, ('f, 'a) protocol_channel_scheme) state_monad) list"
  assumes steps: "\<And>step x. step \<in> set steps \<Longrightarrow>
    hash_range_budget n (step x)"
  shows "hash_range_budget (length steps * n) (mfold x steps)"
  using steps
proof (induction steps arbitrary: x)
  case Nil
  then show ?case
    by (simp add: hash_range_budget_return)
next
  case (Cons step steps)
  have head: "hash_range_budget n (step x)"
    using Cons.prems by simp
  have tail: "\<And>y. hash_range_budget (length steps * n) (mfold y steps)"
    using Cons.IH Cons.prems by simp
  have "hash_range_budget (n + length steps * n)
      (step x \<bind> (\<lambda>y. mfold y steps))"
    by (rule hash_range_budget_bind[OF head tail])
  then show ?case
    by simp
qed

lemma hash_collision_budget_mfold:
  fixes steps :: "('x \<Rightarrow> ('x, ('f, 'a) protocol_channel_scheme) state_monad) list"
  assumes range_steps: "\<And>step x. step \<in> set steps \<Longrightarrow>
    hash_range_budget n (step x)"
    and coll_steps: "\<And>step x. step \<in> set steps \<Longrightarrow>
      hash_collision_budget n (step x)"
  shows "hash_collision_budget (length steps * n) (mfold x steps)"
  using range_steps coll_steps
proof (induction steps arbitrary: x)
  case Nil
  then show ?case
    by (simp add: hash_collision_budget_return)
next
  case (Cons step steps)
  have head_range: "hash_range_budget n (step x)"
    using Cons.prems by simp
  have head_coll: "hash_collision_budget n (step x)"
    using Cons.prems by simp
  have tail_range:
    "\<And>y. hash_range_budget (length steps * n) (mfold y steps)"
    by (rule hash_range_budget_mfold) (use Cons.prems in auto)
  have tail_coll:
    "\<And>y. hash_collision_budget (length steps * n) (mfold y steps)"
    using Cons.IH Cons.prems by simp
  have "hash_collision_budget (n + length steps * n)
      (step x \<bind> (\<lambda>y. mfold y steps))"
    by (rule hash_collision_budget_bind
        [OF head_range head_coll tail_range tail_coll])
  then show ?case
    by simp
qed

lemma hash_range_budget_mfold_invariant:
  fixes steps :: "('x \<Rightarrow> ('x, ('f, 'a) protocol_channel_scheme) state_monad) list"
  assumes init: "I x"
    and step_budget:
      "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        hash_range_budget n (step y)"
    and step_inv:
      "\<And>step y z s t. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        Some (z, t) \<in> set_dist (execute (step y) s) \<Longrightarrow> I z"
  shows "hash_range_budget (length steps * n) (mfold x steps)"
  using init step_budget step_inv
proof (induction steps arbitrary: x)
  case Nil
  then show ?case
    by (simp add: hash_range_budget_return)
next
  case (Cons step steps)
  have Ix: "I x"
    using Cons.prems by simp
  have head: "hash_range_budget n (step x)"
    by (rule Cons.prems(2)) (use Ix in auto)
  have tail:
    "hash_range_budget (length steps * n) (mfold y steps)"
    if out: "Some (y, t) \<in> set_dist (execute (step x) s)"
    for s y t
  proof (rule Cons.IH)
    show "I y"
    proof -
      have mem: "step \<in> set (step # steps)"
        by simp
      have inv: "\<And>z s t.
        Some (z, t) \<in> set_dist (execute (step x) s) \<Longrightarrow> I z"
        by (rule Cons.prems(3)[OF mem Ix])
      show ?thesis
        by (rule inv[OF out])
    qed
    show "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
      hash_range_budget n (step y)"
      by (rule Cons.prems(2)) simp_all
    show "\<And>step y z s t.
      step \<in> set steps \<Longrightarrow>
      I y \<Longrightarrow> Some (z, t) \<in> set_dist (execute (step y) s) \<Longrightarrow> I z"
      by (rule Cons.prems(3)) simp_all
  qed
  have "hash_range_budget (n + length steps * n)
      (step x \<bind> (\<lambda>y. mfold y steps))"
    by (rule hash_range_budget_bind_on_outcomes[OF head]) (rule tail)
  then show ?case
    by simp
qed

lemma hash_collision_budget_mfold_invariant:
  fixes steps :: "('x \<Rightarrow> ('x, ('f, 'a) protocol_channel_scheme) state_monad) list"
  assumes init: "I x"
    and range_step:
      "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        hash_range_budget n (step y)"
    and coll_step:
      "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        hash_collision_budget n (step y)"
    and step_inv:
      "\<And>step y z s t. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        Some (z, t) \<in> set_dist (execute (step y) s) \<Longrightarrow> I z"
  shows "hash_collision_budget (length steps * n) (mfold x steps)"
  using init range_step coll_step step_inv
proof (induction steps arbitrary: x)
  case Nil
  then show ?case
    by (simp add: hash_collision_budget_return)
next
  case (Cons step steps)
  have Ix: "I x"
    using Cons.prems by simp
  have head_range: "hash_range_budget n (step x)"
    by (rule Cons.prems(2)) (use Ix in auto)
  have head_coll: "hash_collision_budget n (step x)"
    by (rule Cons.prems(3)) (use Ix in auto)
  have tail_range:
    "hash_range_budget (length steps * n) (mfold y steps)"
    if out: "Some (y, t) \<in> set_dist (execute (step x) s)"
    for s y t
  proof (rule hash_range_budget_mfold_invariant)
    show "I y"
    proof -
      have mem: "step \<in> set (step # steps)"
        by simp
      have inv: "\<And>z s t.
        Some (z, t) \<in> set_dist (execute (step x) s) \<Longrightarrow> I z"
        by (rule Cons.prems(4)[OF mem Ix])
      show ?thesis
        by (rule inv[OF out])
    qed
    show "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
      hash_range_budget n (step y)"
      by (rule Cons.prems(2)) simp_all
    show "\<And>step y z s t.
      step \<in> set steps \<Longrightarrow>
      I y \<Longrightarrow> Some (z, t) \<in> set_dist (execute (step y) s) \<Longrightarrow> I z"
      by (rule Cons.prems(4)) simp_all
  qed
  have tail_coll:
    "hash_collision_budget (length steps * n) (mfold y steps)"
    if out: "Some (y, t) \<in> set_dist (execute (step x) s)"
    for s y t
  proof (rule Cons.IH)
    show "I y"
    proof -
      have mem: "step \<in> set (step # steps)"
        by simp
      have inv: "\<And>z s t.
        Some (z, t) \<in> set_dist (execute (step x) s) \<Longrightarrow> I z"
        by (rule Cons.prems(4)[OF mem Ix])
      show ?thesis
        by (rule inv[OF out])
    qed
    show "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
      hash_range_budget n (step y)"
      by (rule Cons.prems(2)) simp_all
    show "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
      hash_collision_budget n (step y)"
      by (rule Cons.prems(3)) simp_all
    show "\<And>step y z s t.
      step \<in> set steps \<Longrightarrow>
      I y \<Longrightarrow> Some (z, t) \<in> set_dist (execute (step y) s) \<Longrightarrow> I z"
      by (rule Cons.prems(4)) simp_all
  qed
  have "hash_collision_budget (n + length steps * n)
      (step x \<bind> (\<lambda>y. mfold y steps))"
    by (rule hash_collision_budget_bind_on_outcomes
        [OF head_range head_coll tail_range tail_coll])
	  then show ?case
	    by simp
qed

lemma hash_range_budget_fri_state_mfold_invariant:
  fixes st :: "nat \<times> 'f \<times> nat \<times> nat"
    and steps ::
      "(nat \<times> 'f \<times> nat \<times> nat \<Rightarrow>
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad) list"
    and I :: "nat \<times> 'f \<times> nat \<times> nat \<Rightarrow> bool"
  assumes init: "I st"
    and step_budget:
      "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        hash_range_budget n (step y)"
    and step_inv:
      "\<And>step y z s t. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        Some (z, t) \<in> set_dist (execute (step y) s) \<Longrightarrow> I z"
  shows "hash_range_budget (length steps * n) (mfold st steps)"
  using assms by (rule hash_range_budget_mfold_invariant)

lemma hash_collision_budget_fri_state_mfold_invariant:
  fixes st :: "nat \<times> 'f \<times> nat \<times> nat"
    and steps ::
      "(nat \<times> 'f \<times> nat \<times> nat \<Rightarrow>
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad) list"
    and I :: "nat \<times> 'f \<times> nat \<times> nat \<Rightarrow> bool"
  assumes init: "I st"
    and range_step:
      "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        hash_range_budget n (step y)"
    and coll_step:
      "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        hash_collision_budget n (step y)"
    and step_inv:
      "\<And>step y z s t. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        Some (z, t) \<in> set_dist (execute (step y) s) \<Longrightarrow> I z"
  shows "hash_collision_budget (length steps * n) (mfold st steps)"
  using assms by (rule hash_collision_budget_mfold_invariant)

(*
lemma hash_range_budget_fri_state_mfold_invariant:
  fixes steps ::
    "(nat \<times> 'f \<times> nat \<times> nat \<Rightarrow>
      (nat \<times> 'f \<times> nat \<times> nat,
        ('f, 'a) protocol_channel_scheme) state_monad) list"
    and I :: "nat \<times> 'f \<times> nat \<times> nat \<Rightarrow> bool"
  assumes init: "I x"
    and step_budget:
      "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        hash_range_budget n (step y)"
    and step_inv:
      "\<And>step y z s t. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        Some (z, t) \<in> set_dist (execute (step y) s) \<Longrightarrow> I z"
  shows "hash_range_budget (length steps * n) (mfold x steps)"
  using assms by (rule hash_range_budget_mfold_invariant)

lemma hash_collision_budget_fri_state_mfold_invariant:
  fixes steps ::
    "(nat \<times> 'f \<times> nat \<times> nat \<Rightarrow>
      (nat \<times> 'f \<times> nat \<times> nat,
        ('f, 'a) protocol_channel_scheme) state_monad) list"
    and I :: "nat \<times> 'f \<times> nat \<times> nat \<Rightarrow> bool"
  assumes init: "I x"
    and range_step:
      "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        hash_range_budget n (step y)"
    and coll_step:
      "\<And>step y. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        hash_collision_budget n (step y)"
    and step_inv:
      "\<And>step y z s t. step \<in> set steps \<Longrightarrow> I y \<Longrightarrow>
        Some (z, t) \<in> set_dist (execute (step y) s) \<Longrightarrow> I z"
  shows "hash_collision_budget (length steps * n) (mfold x steps)"
  using assms by (rule hash_collision_budget_mfold_invariant)
*)

lemma hash_target_program_receive_fri_commits:
  "hash_target_program B 1 receive_fri_commits"
proof -
  have tail:
    "hash_target_program B (1 + 0)
      (receive_random_field_element \<bind> (\<lambda>b. return (b, r)))"
    for r
    by (rule hash_target_program_bind)
      (rule hash_target_program_receive_random_field_element,
        rule hash_target_program_return)
  have "hash_target_program B (0 + (1 + 0))
      (read \<bind>
        (\<lambda>r. receive_random_field_element \<bind>
          (\<lambda>b. return (b, r))))"
    by (rule hash_target_program_bind[OF hash_target_program_read tail])
  then show ?thesis
    unfolding receive_fri_commits_def by simp
qed

lemma hash_target_program_receive_fri_commits_with:
  assumes challenge: "hash_target_program B 1 receive_challenge"
  shows "hash_target_program B 1
    (receive_fri_commits_with receive_challenge)"
proof -
  have tail:
    "hash_target_program B (1 + 0)
      (receive_challenge \<bind> (\<lambda>b. return (b, r)))"
    for r
    by (rule hash_target_program_bind[OF challenge hash_target_program_return])
  have "hash_target_program B (0 + (1 + 0))
      (read \<bind>
        (\<lambda>r. receive_challenge \<bind>
          (\<lambda>b. return (b, r))))"
    by (rule hash_target_program_bind[OF hash_target_program_read tail])
  then show ?thesis
    unfolding receive_fri_commits_with_def by simp
qed

lemma hash_target_program_receive_trace_fri_commits:
  "hash_target_program B 1 receive_trace_fri_commits"
  unfolding receive_trace_fri_commits_def
  by (rule hash_target_program_receive_fri_commits_with)
    (rule hash_target_program_receive_trace_fri_challenge)

lemma hash_target_program_receive_composition_fri_commits:
  "hash_target_program B 1 receive_composition_fri_commits"
  unfolding receive_composition_fri_commits_def
  by (rule hash_target_program_receive_fri_commits_with)
    (rule hash_target_program_receive_composition_fri_challenge)

lemma hash_range_budget_receive_fri_commits:
  "hash_range_budget 1 receive_fri_commits"
proof -
  have read_then_random:
    "hash_range_budget (0 + (1 + 0))
      (read \<bind>
        (\<lambda>r. receive_random_field_element \<bind>
          (\<lambda>b. return (b, r))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_read,
        rule hash_range_budget_bind
          [OF hash_range_budget_receive_random_field_element
            hash_range_budget_return])
  then show ?thesis
    unfolding receive_fri_commits_def by simp
qed

lemma hash_collision_budget_receive_fri_commits:
  "hash_collision_budget 1 receive_fri_commits"
proof -
  have random_then_return_range:
    "hash_range_budget (1 + 0)
      (receive_random_field_element \<bind> (\<lambda>b. return (b, r)))" for r
    by (rule hash_range_budget_bind
        [OF hash_range_budget_receive_random_field_element
          hash_range_budget_return])
  have random_then_return_coll:
    "hash_collision_budget (1 + 0)
      (receive_random_field_element \<bind> (\<lambda>b. return (b, r)))" for r
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_receive_random_field_element
          hash_collision_budget_receive_random_field_element
          hash_range_budget_return hash_collision_budget_return])
  have "hash_collision_budget (0 + (1 + 0))
      (read \<bind>
        (\<lambda>r. receive_random_field_element \<bind>
          (\<lambda>b. return (b, r))))"
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_read hash_collision_budget_read
          random_then_return_range random_then_return_coll])
  then show ?thesis
    unfolding receive_fri_commits_def by simp
qed

lemma hash_range_budget_receive_fri_commits_with:
  assumes challenge: "hash_range_budget 1 receive_challenge"
  shows "hash_range_budget 1 (receive_fri_commits_with receive_challenge)"
proof -
  have read_then_challenge:
    "hash_range_budget (0 + (1 + 0))
      (read \<bind>
        (\<lambda>r. receive_challenge \<bind>
          (\<lambda>b. return (b, r))))"
    by (rule hash_range_budget_bind)
      (rule hash_range_budget_read,
        rule hash_range_budget_bind [OF challenge hash_range_budget_return])
  then show ?thesis
    unfolding receive_fri_commits_with_def by simp
qed

lemma hash_collision_budget_receive_fri_commits_with:
  assumes challenge_range: "hash_range_budget 1 receive_challenge"
    and challenge_collision: "hash_collision_budget 1 receive_challenge"
  shows "hash_collision_budget 1 (receive_fri_commits_with receive_challenge)"
proof -
  have challenge_then_return_range:
    "hash_range_budget (1 + 0)
      (receive_challenge \<bind> (\<lambda>b. return (b, r)))" for r
    by (rule hash_range_budget_bind
        [OF challenge_range hash_range_budget_return])
  have challenge_then_return_coll:
    "hash_collision_budget (1 + 0)
      (receive_challenge \<bind> (\<lambda>b. return (b, r)))" for r
    by (rule hash_collision_budget_bind
        [OF challenge_range challenge_collision
          hash_range_budget_return hash_collision_budget_return])
  have "hash_collision_budget (0 + (1 + 0))
      (read \<bind>
        (\<lambda>r. receive_challenge \<bind>
          (\<lambda>b. return (b, r))))"
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_read hash_collision_budget_read
          challenge_then_return_range challenge_then_return_coll])
  then show ?thesis
    unfolding receive_fri_commits_with_def by simp
qed

lemma hash_range_budget_receive_trace_fri_commits:
  "hash_range_budget 1 receive_trace_fri_commits"
  unfolding receive_trace_fri_commits_def
  by (rule hash_range_budget_receive_fri_commits_with)
    (rule hash_range_budget_receive_trace_fri_challenge)

lemma hash_collision_budget_receive_trace_fri_commits:
  "hash_collision_budget 1 receive_trace_fri_commits"
  unfolding receive_trace_fri_commits_def
  by (rule hash_collision_budget_receive_fri_commits_with)
    (rule hash_range_budget_receive_trace_fri_challenge,
      rule hash_collision_budget_receive_trace_fri_challenge)

lemma hash_range_budget_receive_composition_fri_commits:
  "hash_range_budget 1 receive_composition_fri_commits"
  unfolding receive_composition_fri_commits_def
  by (rule hash_range_budget_receive_fri_commits_with)
    (rule hash_range_budget_receive_composition_fri_challenge)

lemma hash_collision_budget_receive_composition_fri_commits:
  "hash_collision_budget 1 receive_composition_fri_commits"
  unfolding receive_composition_fri_commits_def
  by (rule hash_collision_budget_receive_fri_commits_with)
    (rule hash_range_budget_receive_composition_fri_challenge,
      rule hash_collision_budget_receive_composition_fri_challenge)

lemma hash_target_program_protocol_check_authentication_path_raw:
  fixes leaf :: "'f protocol_hash_input"
  shows "hash_target_program B (Suc (length path))
    (protocol_merkle.check_authentication_path len i leaf path ::
      ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
proof (induction path arbitrary: len i)
  case Nil
  have "hash_target_program B 1
      (hash leaf :: ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_target_program_hash)
  then show ?case
    by (simp add: protocol_merkle.check_authentication_path.simps)
next
  case (Cons a path)
  show ?case
  proof (cases "i < len div 2")
    case True
    have rec:
      "hash_target_program B (Suc (length path))
        (protocol_merkle.check_authentication_path (len div 2) i leaf path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      using Cons.IH[of "len div 2" i] by simp
    have bound:
      "hash_target_program B (Suc (length path) + 1)
        ((protocol_merkle.check_authentication_path (len div 2) i leaf path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>x. hash (MerkleNode x a)))"
      by (rule hash_target_program_bind[OF rec hash_target_program_hash])
    show ?thesis
      using True bound
      by (simp add: protocol_merkle.check_authentication_path.simps)
  next
    case False
    have rec:
      "hash_target_program B (Suc (length path))
        (protocol_merkle.check_authentication_path
          (len div 2) (i - len div 2) leaf path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      using Cons.IH[of "len div 2" "i - len div 2"] by simp
    have bound:
      "hash_target_program B (Suc (length path) + 1)
        ((protocol_merkle.check_authentication_path
          (len div 2) (i - len div 2) leaf path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>x. hash (MerkleNode a x)))"
      by (rule hash_target_program_bind[OF rec hash_target_program_hash])
    show ?thesis
      using False bound
      by (simp add: protocol_merkle.check_authentication_path.simps)
  qed
qed

lemma hash_target_program_check_authentication_path:
  "hash_target_program B (Suc (length path))
    (check_authentication_path len i v path)"
  unfolding check_authentication_path_def protocol_check_authentication_path_def
  by (rule hash_target_program_protocol_check_authentication_path_raw)

lemma hash_target_program_check_authentication_path_assert_return:
  fixes path :: "'f list"
    and v root :: "'f"
    and r :: "'r"
  shows
    "hash_target_program B (Suc (length path))
      ((check_authentication_path len i v path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = root) \<bind> (\<lambda>_. return r)))"
proof -
  have tail:
    "hash_target_program B (0 + 0)
      (assert (ap = root) \<bind> (\<lambda>_. return r) ::
        ('r, ('f, 'a) protocol_channel_scheme) state_monad)"
    for ap
    by (rule hash_target_program_bind)
      (rule hash_target_program_assert, rule hash_target_program_return)
  have "hash_target_program B (Suc (length path) + (0 + 0))
      ((check_authentication_path len i v path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = root) \<bind> (\<lambda>_. return r)))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_check_authentication_path, rule tail)
  then show ?thesis by simp
qed

lemma hash_target_program_check_authentication_path_assert_bind:
  fixes path :: "'f list"
    and v root :: "'f"
    and k :: "unit \<Rightarrow>
      ('r, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes k: "\<And>u. hash_target_program B n (k u)"
  shows
    "hash_target_program B (Suc (length path) + n)
      ((check_authentication_path len i v path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = root) \<bind> k))"
proof -
  have tail:
    "hash_target_program B (0 + n)
      (assert (ap = root) \<bind> k ::
        ('r, ('f, 'a) protocol_channel_scheme) state_monad)"
    for ap
    by (rule hash_target_program_bind[OF hash_target_program_assert k])
  have "hash_target_program B (Suc (length path) + (0 + n))
      ((check_authentication_path len i v path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = root) \<bind> k))"
    by (rule hash_target_program_bind)
      (rule hash_target_program_check_authentication_path, rule tail)
  then show ?thesis by simp
qed

lemma hash_target_program_fri_layer_opening_finish:
  assumes xp_path_len: "length xp_path = floor_log len"
    and xn_path_len: "length xn_path = floor_log len"
  shows
    "hash_target_program B
      (Suc (floor_log len) + Suc (floor_log len))
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
proof -
  let ?H = "Suc (floor_log len)"
  let ?sidx = "(i + len div 2) mod len"
  let ?out =
    "(i mod (len div 2),
      (xp + xn) div 2 +
        b * ((xp - xn) div (2 * ((h ^ i) * shift) ^ pw)),
      len div 2, pw + pw)"
  have second:
    "hash_target_program B ?H
      ((check_authentication_path len ?sidx xn xn_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out)))"
    by (subst xn_path_len[symmetric])
      (rule hash_target_program_check_authentication_path_assert_return)
  have first0:
    "hash_target_program B (Suc (length xp_path) + ?H)
      ((check_authentication_path len i xp xp_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind>
          (\<lambda>_.
            (check_authentication_path len ?sidx xn xn_path ::
              ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out)))))"
    by (rule hash_target_program_check_authentication_path_assert_bind)
      (use second in simp)
  have first:
    "hash_target_program B (?H + ?H)
      ((check_authentication_path len i xp xp_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind>
          (\<lambda>_.
            (check_authentication_path len ?sidx xn xn_path ::
              ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out)))))"
    using first0 xp_path_len by simp
  have raw:
    "hash_target_program B (0 + (?H + ?H))
      ((assert (xp = x) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>_.
          (check_authentication_path len i xp xp_path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = f) \<bind>
            (\<lambda>_.
              (check_authentication_path len ?sidx xn xn_path ::
                ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    by (rule hash_target_program_bind[OF hash_target_program_assert first])
  show ?thesis
    using raw unfolding fri_layer_opening_finish_def
    by (simp add: Let_def)
qed

lemma hash_target_program_fri_layer_opening_step:
  "hash_target_program B
    (Suc (floor_log len) + Suc (floor_log len))
    (fri_layer_opening_step (b, f) (i, x, len, pw))"
proof -
  let ?N = "Suc (floor_log len) + Suc (floor_log len)"
  have after_xn_path:
    "hash_target_program B ?N
      ((ntimes read (floor_log len) ::
          ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>xn_path.
          fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path))"
    if xp_path_len: "length xp_path = floor_log len"
    for xp xp_path xn
  proof (rule hash_target_program_ntimes_read_bind)
    fix xn_path :: "'f list"
    assume xn_path_len: "length xn_path = floor_log len"
    show "hash_target_program B ?N
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
      by (rule hash_target_program_fri_layer_opening_finish
          [OF xp_path_len xn_path_len])
  qed
  have after_xn:
    "hash_target_program B ?N
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
    if xp_path_len: "length xp_path = floor_log len"
    for xp xp_path
  proof -
    have "hash_target_program B (0 + ?N)
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
      by (rule hash_target_program_bind
          [OF hash_target_program_read after_xn_path[OF xp_path_len]])
    then show ?thesis by simp
  qed
  have after_xp_path:
    "hash_target_program B ?N
      ((ntimes read (floor_log len) ::
          ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>xp_path.
          read \<bind>
          (\<lambda>xn.
            (ntimes read (floor_log len) ::
              ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>xn_path.
              fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path))))"
    for xp
  proof (rule hash_target_program_ntimes_read_bind)
    fix xp_path :: "'f list"
    assume xp_path_len: "length xp_path = floor_log len"
    show "hash_target_program B ?N
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
      by (rule after_xn[OF xp_path_len])
  qed
  have "hash_target_program B (0 + ?N)
      (read \<bind>
        (\<lambda>xp.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xp_path.
            read \<bind>
            (\<lambda>xn.
              (ntimes read (floor_log len) ::
                ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>xn_path.
                fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))))"
    by (rule hash_target_program_bind
        [OF hash_target_program_read after_xp_path])
  then show ?thesis
    unfolding fri_layer_opening_step_unfold_finish by simp
qed

lemma hash_range_budget_protocol_check_authentication_path_raw:
  fixes leaf :: "'f protocol_hash_input"
  shows "hash_range_budget (Suc (length path))
    (protocol_merkle.check_authentication_path len i leaf path ::
      ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
proof (induction path arbitrary: len i)
  case Nil
  have hash_budget:
    "hash_range_budget 1
      (hash leaf :: ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_hash)
  then show ?case
    by (simp add: protocol_merkle.check_authentication_path.simps)
next
  case (Cons a path)
  show ?case
  proof (cases "i < len div 2")
    case True
    have rec:
      "hash_range_budget (Suc (length path))
        (protocol_merkle.check_authentication_path (len div 2) i leaf path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      using Cons.IH[of "len div 2" i] by simp
    have bound:
      "hash_range_budget (Suc (length path) + 1)
        ((protocol_merkle.check_authentication_path (len div 2) i leaf path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>x. hash (MerkleNode x a)))"
      by (rule hash_range_budget_bind[OF rec hash_range_budget_hash])
    show ?thesis
      using True bound
      by (simp add: protocol_merkle.check_authentication_path.simps)
  next
    case False
    have rec:
      "hash_range_budget (Suc (length path))
        (protocol_merkle.check_authentication_path
          (len div 2) (i - len div 2) leaf path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      using Cons.IH[of "len div 2" "i - len div 2"] by simp
    have bound:
      "hash_range_budget (Suc (length path) + 1)
        ((protocol_merkle.check_authentication_path
          (len div 2) (i - len div 2) leaf path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>x. hash (MerkleNode a x)))"
      by (rule hash_range_budget_bind[OF rec hash_range_budget_hash])
    show ?thesis
      using False bound
      by (simp add: protocol_merkle.check_authentication_path.simps)
  qed
qed

lemma hash_range_budget_check_authentication_path:
  "hash_range_budget (Suc (length path))
    (check_authentication_path len i v path)"
  unfolding check_authentication_path_def protocol_check_authentication_path_def
  by (rule hash_range_budget_protocol_check_authentication_path_raw)

lemma hash_collision_budget_protocol_check_authentication_path_raw:
  fixes leaf :: "'f protocol_hash_input"
  shows "hash_collision_budget (Suc (length path))
    (protocol_merkle.check_authentication_path len i leaf path ::
      ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
proof (induction path arbitrary: len i)
  case Nil
  have hash_budget:
    "hash_collision_budget 1
      (hash leaf :: ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_collision_budget_hash)
  then show ?case
    by (simp add: protocol_merkle.check_authentication_path.simps)
next
  case (Cons a path)
  show ?case
  proof (cases "i < len div 2")
    case True
    have rec_range:
      "hash_range_budget (Suc (length path))
        (protocol_merkle.check_authentication_path (len div 2) i leaf path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_protocol_check_authentication_path_raw)
    have rec_coll:
      "hash_collision_budget (Suc (length path))
        (protocol_merkle.check_authentication_path (len div 2) i leaf path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      using Cons.IH[of "len div 2" i] by simp
    have bound:
      "hash_collision_budget (Suc (length path) + 1)
        ((protocol_merkle.check_authentication_path (len div 2) i leaf path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>x. hash (MerkleNode x a)))"
      by (rule hash_collision_budget_bind
          [OF rec_range rec_coll hash_range_budget_hash
            hash_collision_budget_hash])
    show ?thesis
      using True bound
      by (simp add: protocol_merkle.check_authentication_path.simps)
  next
    case False
    have rec_range:
      "hash_range_budget (Suc (length path))
        (protocol_merkle.check_authentication_path
          (len div 2) (i - len div 2) leaf path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      by (rule hash_range_budget_protocol_check_authentication_path_raw)
    have rec_coll:
      "hash_collision_budget (Suc (length path))
        (protocol_merkle.check_authentication_path
          (len div 2) (i - len div 2) leaf path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
      using Cons.IH[of "len div 2" "i - len div 2"] by simp
    have bound:
      "hash_collision_budget (Suc (length path) + 1)
        ((protocol_merkle.check_authentication_path
          (len div 2) (i - len div 2) leaf path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>x. hash (MerkleNode a x)))"
      by (rule hash_collision_budget_bind
          [OF rec_range rec_coll hash_range_budget_hash
            hash_collision_budget_hash])
    show ?thesis
      using False bound
      by (simp add: protocol_merkle.check_authentication_path.simps)
  qed
qed

lemma hash_collision_budget_check_authentication_path:
  "hash_collision_budget (Suc (length path))
    (check_authentication_path len i v path)"
  unfolding check_authentication_path_def protocol_check_authentication_path_def
  by (rule hash_collision_budget_protocol_check_authentication_path_raw)

lemma hash_range_budget_check_authentication_path_assert_return:
  fixes path :: "'f list"
    and v root :: "'f"
    and r :: "'r"
  shows
  "hash_range_budget (Suc (length path))
    (((check_authentication_path len i v path ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
      (\<lambda>ap. assert (ap = root) \<bind> (\<lambda>_. return r))))"
proof -
  have check_budget:
    "hash_range_budget (Suc (length path))
      (check_authentication_path len i v path ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_check_authentication_path)
  have assert_return:
    "hash_range_budget (0 + 0)
      (assert (ap = root) \<bind> (\<lambda>_. return r) ::
        ('r, ('f, 'a) protocol_channel_scheme) state_monad)" for ap
    by (rule hash_range_budget_bind
        [OF hash_range_budget_assert hash_range_budget_return])
  have "hash_range_budget (Suc (length path) + (0 + 0))
      (((check_authentication_path len i v path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = root) \<bind> (\<lambda>_. return r))))"
    by (rule hash_range_budget_bind[OF check_budget assert_return])
  then show ?thesis by simp
qed

lemma hash_collision_budget_check_authentication_path_assert_return:
  fixes path :: "'f list"
    and v root :: "'f"
    and r :: "'r"
  shows
  "hash_collision_budget (Suc (length path))
    (((check_authentication_path len i v path ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
      (\<lambda>ap. assert (ap = root) \<bind> (\<lambda>_. return r))))"
proof -
  have check_range:
    "hash_range_budget (Suc (length path))
      (check_authentication_path len i v path ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_check_authentication_path)
  have check_coll:
    "hash_collision_budget (Suc (length path))
      (check_authentication_path len i v path ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_collision_budget_check_authentication_path)
  have assert_return_range:
    "hash_range_budget (0 + 0)
      (assert (ap = root) \<bind> (\<lambda>_. return r) ::
        ('r, ('f, 'a) protocol_channel_scheme) state_monad)" for ap
    by (rule hash_range_budget_bind
        [OF hash_range_budget_assert hash_range_budget_return])
  have assert_return_coll:
    "hash_collision_budget (0 + 0)
      (assert (ap = root) \<bind> (\<lambda>_. return r) ::
        ('r, ('f, 'a) protocol_channel_scheme) state_monad)" for ap
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_assert hash_collision_budget_assert
          hash_range_budget_return hash_collision_budget_return])
  have "hash_collision_budget (Suc (length path) + (0 + 0))
      (((check_authentication_path len i v path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = root) \<bind> (\<lambda>_. return r))))"
    by (rule hash_collision_budget_bind
        [OF check_range check_coll assert_return_range assert_return_coll])
  then show ?thesis by simp
qed

lemma hash_range_budget_check_authentication_path_assert_bind:
  fixes path :: "'f list"
    and v root :: "'f"
    and k :: "unit \<Rightarrow> ('r, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes k: "\<And>u. hash_range_budget n (k u)"
  shows
  "hash_range_budget (Suc (length path) + n)
    (((check_authentication_path len i v path ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
      (\<lambda>ap. assert (ap = root) \<bind> k)))"
proof -
  have check_budget:
    "hash_range_budget (Suc (length path))
      (check_authentication_path len i v path ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_check_authentication_path)
  have assert_cont:
    "hash_range_budget (0 + n)
      (assert (ap = root) \<bind> k ::
        ('r, ('f, 'a) protocol_channel_scheme) state_monad)" for ap
    by (rule hash_range_budget_bind[OF hash_range_budget_assert k])
  have "hash_range_budget (Suc (length path) + (0 + n))
    (((check_authentication_path len i v path ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
      (\<lambda>ap. assert (ap = root) \<bind> k)))"
    by (rule hash_range_budget_bind[OF check_budget assert_cont])
  then show ?thesis by simp
qed

lemma hash_collision_budget_check_authentication_path_assert_bind:
  fixes path :: "'f list"
    and v root :: "'f"
    and k :: "unit \<Rightarrow> ('r, ('f, 'a) protocol_channel_scheme) state_monad"
  assumes range_k: "\<And>u. hash_range_budget n (k u)"
    and coll_k: "\<And>u. hash_collision_budget n (k u)"
  shows
  "hash_collision_budget (Suc (length path) + n)
    (((check_authentication_path len i v path ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
      (\<lambda>ap. assert (ap = root) \<bind> k)))"
proof -
  have check_range:
    "hash_range_budget (Suc (length path))
      (check_authentication_path len i v path ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_check_authentication_path)
  have check_coll:
    "hash_collision_budget (Suc (length path))
      (check_authentication_path len i v path ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_collision_budget_check_authentication_path)
  have assert_range:
    "hash_range_budget (0 + n)
      (assert (ap = root) \<bind> k ::
        ('r, ('f, 'a) protocol_channel_scheme) state_monad)" for ap
    by (rule hash_range_budget_bind[OF hash_range_budget_assert range_k])
  have assert_coll:
    "hash_collision_budget (0 + n)
      (assert (ap = root) \<bind> k ::
        ('r, ('f, 'a) protocol_channel_scheme) state_monad)" for ap
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_assert hash_collision_budget_assert
          range_k coll_k])
  have "hash_collision_budget (Suc (length path) + (0 + n))
    (((check_authentication_path len i v path ::
        ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
      (\<lambda>ap. assert (ap = root) \<bind> k)))"
    by (rule hash_collision_budget_bind
        [OF check_range check_coll assert_range assert_coll])
  then show ?thesis by simp
qed

lemma hash_range_budget_fri_layer_opening_finish:
  assumes xp_path_len: "length xp_path = floor_log len"
    and xn_path_len: "length xn_path = floor_log len"
  shows
    "hash_range_budget (Suc (floor_log len) + Suc (floor_log len))
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
proof -
  let ?b = "Suc (floor_log len)"
  let ?sidx = "(i + len div 2) mod len"
  let ?out =
    "(i mod (len div 2),
      (xp + xn) div 2 +
        b * ((xp - xn) div (2 * ((h ^ i) * shift) ^ pw)),
      len div 2, pw + pw)"
  have second:
    "hash_range_budget ?b
      (((check_authentication_path len ?sidx xn xn_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))"
    by (subst xn_path_len[symmetric])
      (rule hash_range_budget_check_authentication_path_assert_return)
  have second_cont:
    "\<And>u. hash_range_budget ?b
      (((check_authentication_path len ?sidx xn xn_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))"
    using second by simp
  have first0:
    "hash_range_budget (Suc (length xp_path) + ?b)
      (((check_authentication_path len i xp xp_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind>
          (\<lambda>_.
            (check_authentication_path len ?sidx xn xn_path ::
              ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    by (rule hash_range_budget_check_authentication_path_assert_bind
        [OF second_cont])
  have first:
    "hash_range_budget (?b + ?b)
      (((check_authentication_path len i xp xp_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind>
          (\<lambda>_.
            (check_authentication_path len ?sidx xn xn_path ::
              ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    using first0 xp_path_len by simp
  have raw:
    "hash_range_budget (0 + (?b + ?b))
      ((assert (xp = x) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>_.
          (check_authentication_path len i xp xp_path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = f) \<bind>
            (\<lambda>_.
              (check_authentication_path len ?sidx xn xn_path ::
                ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    by (rule hash_range_budget_bind[OF hash_range_budget_assert first])
  have all:
    "hash_range_budget (?b + ?b)
      ((assert (xp = x) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>_.
          (check_authentication_path len i xp xp_path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = f) \<bind>
            (\<lambda>_.
              (check_authentication_path len ?sidx xn xn_path ::
                ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    using raw by simp
  from all show ?thesis
    unfolding fri_layer_opening_finish_def
    by (simp add: Let_def)
qed

lemma hash_collision_budget_fri_layer_opening_finish:
  assumes xp_path_len: "length xp_path = floor_log len"
    and xn_path_len: "length xn_path = floor_log len"
  shows
    "hash_collision_budget (Suc (floor_log len) + Suc (floor_log len))
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
proof -
  let ?b = "Suc (floor_log len)"
  let ?sidx = "(i + len div 2) mod len"
  let ?out =
    "(i mod (len div 2),
      (xp + xn) div 2 +
        b * ((xp - xn) div (2 * ((h ^ i) * shift) ^ pw)),
      len div 2, pw + pw)"
  have second_range:
    "hash_range_budget ?b
      (((check_authentication_path len ?sidx xn xn_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))"
    by (subst xn_path_len[symmetric])
      (rule hash_range_budget_check_authentication_path_assert_return)
  have second_coll:
    "hash_collision_budget ?b
      (((check_authentication_path len ?sidx xn xn_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))"
    by (subst xn_path_len[symmetric])
      (rule hash_collision_budget_check_authentication_path_assert_return)
  have second_cont_range:
    "\<And>u. hash_range_budget ?b
      (((check_authentication_path len ?sidx xn xn_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))"
    using second_range by simp
  have second_cont_coll:
    "\<And>u. hash_collision_budget ?b
      (((check_authentication_path len ?sidx xn xn_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))"
    using second_coll by simp
  have first_range0:
    "hash_range_budget (Suc (length xp_path) + ?b)
      (((check_authentication_path len i xp xp_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind>
          (\<lambda>_.
            (check_authentication_path len ?sidx xn xn_path ::
              ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    by (rule hash_range_budget_check_authentication_path_assert_bind
        [OF second_cont_range])
  have first_coll0:
    "hash_collision_budget (Suc (length xp_path) + ?b)
      (((check_authentication_path len i xp xp_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind>
          (\<lambda>_.
            (check_authentication_path len ?sidx xn xn_path ::
              ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    by (rule hash_collision_budget_check_authentication_path_assert_bind
        [OF second_cont_range second_cont_coll])
  have first_range:
    "hash_range_budget (?b + ?b)
      (((check_authentication_path len i xp xp_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind>
          (\<lambda>_.
            (check_authentication_path len ?sidx xn xn_path ::
              ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    using first_range0 xp_path_len by simp
  have first_coll:
    "hash_collision_budget (?b + ?b)
      (((check_authentication_path len i xp xp_path ::
          ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>ap. assert (ap = f) \<bind>
          (\<lambda>_.
            (check_authentication_path len ?sidx xn xn_path ::
              ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    using first_coll0 xp_path_len by simp
  have raw:
    "hash_collision_budget (0 + (?b + ?b))
      ((assert (xp = x) ::
          (unit, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>_.
          (check_authentication_path len i xp xp_path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = f) \<bind>
            (\<lambda>_.
              (check_authentication_path len ?sidx xn xn_path ::
                ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>ap. assert (ap = f) \<bind> (\<lambda>_. return ?out))))))"
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_assert hash_collision_budget_assert
          first_range first_coll])
  then show ?thesis
    unfolding fri_layer_opening_finish_def
    by (simp add: Let_def)
qed

lemma hash_range_budget_fri_layer_opening_step:
  "hash_range_budget (Suc (floor_log len) + Suc (floor_log len))
    (fri_layer_opening_step (b, f) (i, x, len, pw))"
proof -
  let ?B = "Suc (floor_log len) + Suc (floor_log len)"
  have after_xn_path:
    "hash_range_budget ?B
      ((ntimes read (floor_log len) ::
          ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>xn_path.
          fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path))"
    if xp_path_len: "length xp_path = floor_log len"
    for xp xp_path xn
  proof (rule hash_range_budget_ntimes_read_bind)
    fix xn_path :: "'f list"
    assume xn_path_len: "length xn_path = floor_log len"
    show "hash_range_budget ?B
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
      by (rule hash_range_budget_fri_layer_opening_finish
          [OF xp_path_len xn_path_len])
  qed
  have after_xn:
    "hash_range_budget ?B
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
    if xp_path_len: "length xp_path = floor_log len"
    for xp xp_path
  proof -
    have "hash_range_budget (0 + ?B)
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
      by (rule hash_range_budget_bind
          [OF hash_range_budget_read after_xn_path[OF xp_path_len]])
    then show ?thesis by simp
  qed
  have after_xp_path:
    "hash_range_budget ?B
      ((ntimes read (floor_log len) ::
          ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>xp_path.
          read \<bind>
          (\<lambda>xn.
            (ntimes read (floor_log len) ::
              ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>xn_path.
              fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path))))"
    for xp
  proof (rule hash_range_budget_ntimes_read_bind)
    fix xp_path :: "'f list"
    assume xp_path_len: "length xp_path = floor_log len"
    show "hash_range_budget ?B
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
      by (rule after_xn[OF xp_path_len])
  qed
  have "hash_range_budget (0 + ?B)
      (read \<bind>
        (\<lambda>xp.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xp_path.
            read \<bind>
            (\<lambda>xn.
              (ntimes read (floor_log len) ::
                ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>xn_path.
                fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))))"
    by (rule hash_range_budget_bind
        [OF hash_range_budget_read after_xp_path])
  then show ?thesis
    unfolding fri_layer_opening_step_unfold_finish by simp
qed

lemma hash_collision_budget_fri_layer_opening_step:
  "hash_collision_budget (Suc (floor_log len) + Suc (floor_log len))
    (fri_layer_opening_step (b, f) (i, x, len, pw))"
proof -
  let ?B = "Suc (floor_log len) + Suc (floor_log len)"
  have after_xn_path_range:
    "hash_range_budget ?B
      ((ntimes read (floor_log len) ::
          ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>xn_path.
          fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path))"
    if xp_path_len: "length xp_path = floor_log len"
    for xp xp_path xn
  proof (rule hash_range_budget_ntimes_read_bind)
    fix xn_path :: "'f list"
    assume xn_path_len: "length xn_path = floor_log len"
    show "hash_range_budget ?B
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
      by (rule hash_range_budget_fri_layer_opening_finish
          [OF xp_path_len xn_path_len])
  qed
  have after_xn_path_coll:
    "hash_collision_budget ?B
      ((ntimes read (floor_log len) ::
          ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>xn_path.
          fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path))"
    if xp_path_len: "length xp_path = floor_log len"
    for xp xp_path xn
  proof (rule hash_collision_budget_ntimes_read_bind)
    fix xn_path :: "'f list"
    assume xn_path_len: "length xn_path = floor_log len"
    show "hash_range_budget ?B
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
      by (rule hash_range_budget_fri_layer_opening_finish
          [OF xp_path_len xn_path_len])
    show "hash_collision_budget ?B
      (fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)"
      by (rule hash_collision_budget_fri_layer_opening_finish
          [OF xp_path_len xn_path_len])
  qed
  have after_xn_range:
    "hash_range_budget ?B
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
    if xp_path_len: "length xp_path = floor_log len"
    for xp xp_path
  proof -
    have "hash_range_budget (0 + ?B)
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
      by (rule hash_range_budget_bind
          [OF hash_range_budget_read after_xn_path_range[OF xp_path_len]])
    then show ?thesis by simp
  qed
  have after_xn_coll:
    "hash_collision_budget ?B
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
    if xp_path_len: "length xp_path = floor_log len"
    for xp xp_path
  proof -
    have "hash_collision_budget (0 + ?B)
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
      by (rule hash_collision_budget_bind
          [OF hash_range_budget_read hash_collision_budget_read
            after_xn_path_range[OF xp_path_len]
            after_xn_path_coll[OF xp_path_len]])
    then show ?thesis by simp
  qed
  have after_xp_path_range:
    "hash_range_budget ?B
      ((ntimes read (floor_log len) ::
          ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>xp_path.
          read \<bind>
          (\<lambda>xn.
            (ntimes read (floor_log len) ::
              ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>xn_path.
              fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path))))"
    for xp
  proof (rule hash_range_budget_ntimes_read_bind)
    fix xp_path :: "'f list"
    assume xp_path_len: "length xp_path = floor_log len"
    show "hash_range_budget ?B
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
      by (rule after_xn_range[OF xp_path_len])
  qed
  have after_xp_path_coll:
    "hash_collision_budget ?B
      ((ntimes read (floor_log len) ::
          ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>xp_path.
          read \<bind>
          (\<lambda>xn.
            (ntimes read (floor_log len) ::
              ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>xn_path.
              fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path))))"
    for xp
  proof (rule hash_collision_budget_ntimes_read_bind)
    fix xp_path :: "'f list"
    assume xp_path_len: "length xp_path = floor_log len"
    show "hash_range_budget ?B
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
      by (rule after_xn_range[OF xp_path_len])
    show "hash_collision_budget ?B
      (read \<bind>
        (\<lambda>xn.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xn_path.
            fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))"
      by (rule after_xn_coll[OF xp_path_len])
  qed
  have "hash_collision_budget (0 + ?B)
      (read \<bind>
        (\<lambda>xp.
          (ntimes read (floor_log len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>xp_path.
            read \<bind>
            (\<lambda>xn.
              (ntimes read (floor_log len) ::
                ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>xn_path.
                fri_layer_opening_finish b f i x len pw xp xp_path xn xn_path)))))"
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_read hash_collision_budget_read
          after_xp_path_range after_xp_path_coll])
  then show ?thesis
    unfolding fri_layer_opening_step_unfold_finish by simp
qed

lemma floor_log_div2_le_self:
  "floor_log (n div 2) \<le> floor_log n"
  by (rule floor_log_le_iff) simp

lemma receive_query_commits_eq_fri_layer_opening_steps:
  "receive_query_commits fl = map fri_layer_opening_step fl"
  unfolding receive_query_commits_def fri_layer_opening_step_def
  by (simp add: fun_eq_iff split_def)

lemma hash_target_program_fri_layer_opening_steps_mfold_state:
  fixes st :: "nat \<times> 'f \<times> nat \<times> nat"
  assumes init:
    "case st of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
  shows
    "hash_target_program B
      (length fl * (Suc L + Suc L))
      (mfold st (map fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
  using init
proof (induction fl arbitrary: st)
  case Nil
  then show ?case
    by (simp add: hash_target_program_return)
next
  case (Cons bf fl)
  obtain i x len pw where st_eq: "st = (i, x, len, pw)"
    by (cases st)
  obtain b f where bf_eq: "bf = (b, f)"
    by (cases bf)
  let ?N = "Suc L + Suc L"
  have head_exact:
    "hash_target_program B
      (Suc (floor_log len) + Suc (floor_log len))
      (fri_layer_opening_step (b, f) (i, x, len, pw))"
    by (rule hash_target_program_fri_layer_opening_step)
  have head_le:
    "Suc (floor_log len) + Suc (floor_log len) \<le> ?N"
    using Cons.prems unfolding st_eq by simp
  have head:
    "hash_target_program B ?N
      (fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
    unfolding bf_eq st_eq
    by (rule hash_target_program_mono[OF head_le head_exact])
  have tail:
    "hash_target_program B (length fl * ?N)
      (mfold z (map fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
    if out:
      "Some (z, t) \<in>
        set_dist (execute (fri_layer_opening_step bf st) s)"
    for z and s :: "('f, 'a) protocol_channel_scheme"
      and t :: "('f, 'a) protocol_channel_scheme"
  proof -
    from fri_layer_opening_step_outcome[OF out[unfolded bf_eq st_eq]]
    obtain xp xp_path xn xn_path x' where
      z_eq: "z = (i mod (len div 2), x', len div 2, pw + pw)"
      by blast
    have len_le: "floor_log len \<le> L"
      using Cons.prems unfolding st_eq by simp
    have next_len: "floor_log (len div 2) \<le> L"
      using floor_log_div2_le_self[of len] len_le by linarith
    have z_inv:
      "case z of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
      unfolding z_eq using next_len by simp
    show ?thesis
      by (rule Cons.IH[OF z_inv])
  qed
  have "hash_target_program B (?N + length fl * ?N)
      ((fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>z. mfold z (map fri_layer_opening_step fl)))"
    by (rule hash_target_program_bind_on_outcomes[OF head]) (rule tail)
  then show ?case
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma hash_target_program_receive_query_commits_mfold:
  assumes init: "floor_log len \<le> L"
  shows
    "hash_target_program B
      (length fl * (Suc L + Suc L))
      (mfold (i, x, len, pw) (receive_query_commits fl))"
  unfolding receive_query_commits_eq_fri_layer_opening_steps
proof -
  have st_inv:
    "case (i, x, len, pw) of
      (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
    using init by simp
  show "hash_target_program B (length fl * (Suc L + Suc L))
    (mfold (i, x, len, pw) (map fri_layer_opening_step fl) ::
      (nat \<times> 'f \<times> nat \<times> nat,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_target_program_fri_layer_opening_steps_mfold_state
        [OF st_inv])
qed

lemma hash_range_budget_fri_layer_opening_steps_mfold_state:
  fixes st :: "nat \<times> 'f \<times> nat \<times> nat"
  assumes init:
    "case st of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
  shows
    "hash_range_budget
      (length fl * (Suc L + Suc L))
      (mfold st (map fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
  using init
proof (induction fl arbitrary: st)
  case Nil
  then show ?case
    by (simp add: hash_range_budget_return)
next
  case (Cons bf fl)
  obtain i x len pw where st_eq: "st = (i, x, len, pw)"
    by (cases st)
  obtain b f where bf_eq: "bf = (b, f)"
    by (cases bf)
  let ?B = "Suc L + Suc L"
  have head_exact:
    "hash_range_budget (Suc (floor_log len) + Suc (floor_log len))
      (fri_layer_opening_step (b, f) (i, x, len, pw))"
    by (rule hash_range_budget_fri_layer_opening_step)
  have head_le:
    "Suc (floor_log len) + Suc (floor_log len) \<le> ?B"
    using Cons.prems unfolding st_eq by simp
  have head:
    "hash_range_budget ?B
      (fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
    unfolding bf_eq st_eq
    by (rule hash_range_budget_mono[OF head_le head_exact])
  have tail:
    "hash_range_budget (length fl * ?B)
      (mfold z (map fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
    if out:
      "Some (z, t) \<in>
        set_dist (execute (fri_layer_opening_step bf st) s)"
    for z and s :: "('f, 'a) protocol_channel_scheme"
      and t :: "('f, 'a) protocol_channel_scheme"
  proof -
    from fri_layer_opening_step_outcome[OF out[unfolded bf_eq st_eq]]
    obtain xp xp_path xn xn_path x' where
      z_eq: "z = (i mod (len div 2), x', len div 2, pw + pw)"
      by blast
    have len_le: "floor_log len \<le> L"
      using Cons.prems unfolding st_eq by simp
    have next_len: "floor_log (len div 2) \<le> L"
      using floor_log_div2_le_self[of len] len_le by linarith
    have z_inv:
      "case z of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
      unfolding z_eq using next_len by simp
    have ih_z:
      "hash_range_budget (length fl * ?B)
        (mfold z (map fri_layer_opening_step fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad)"
      using Cons.IH[OF z_inv] by assumption
    show ?thesis
      by (rule ih_z)
  qed
  have "hash_range_budget (?B + length fl * ?B)
      ((fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>z. mfold z (map fri_layer_opening_step fl)))"
    by (rule hash_range_budget_bind_on_outcomes[OF head]) (rule tail)
  then show ?case
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma hash_range_budget_receive_query_commits_mfold:
  assumes init: "floor_log len \<le> L"
  shows
    "hash_range_budget
      (length fl * (Suc L + Suc L))
      (mfold (i, x, len, pw) (receive_query_commits fl))"
  unfolding receive_query_commits_eq_fri_layer_opening_steps
proof -
  have st_inv:
    "case (i, x, len, pw) of
      (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
    using init by simp
  show "hash_range_budget (length fl * (Suc L + Suc L))
    (mfold (i, x, len, pw) (map fri_layer_opening_step fl) ::
      (nat \<times> 'f \<times> nat \<times> nat,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_range_budget_fri_layer_opening_steps_mfold_state
        [OF st_inv])
qed

lemma hash_collision_budget_fri_layer_opening_steps_mfold_state:
  fixes st :: "nat \<times> 'f \<times> nat \<times> nat"
  assumes init:
    "case st of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
  shows
    "hash_collision_budget
      (length fl * (Suc L + Suc L))
      (mfold st (map fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
  using init
proof (induction fl arbitrary: st)
  case Nil
  then show ?case
    by (simp add: hash_collision_budget_return)
next
  case (Cons bf fl)
  obtain i x len pw where st_eq: "st = (i, x, len, pw)"
    by (cases st)
  obtain b f where bf_eq: "bf = (b, f)"
    by (cases bf)
  let ?B = "Suc L + Suc L"
  have head_range_exact:
    "hash_range_budget (Suc (floor_log len) + Suc (floor_log len))
      (fri_layer_opening_step (b, f) (i, x, len, pw))"
    by (rule hash_range_budget_fri_layer_opening_step)
  have head_coll_exact:
    "hash_collision_budget (Suc (floor_log len) + Suc (floor_log len))
      (fri_layer_opening_step (b, f) (i, x, len, pw))"
    by (rule hash_collision_budget_fri_layer_opening_step)
  have head_le:
    "Suc (floor_log len) + Suc (floor_log len) \<le> ?B"
    using Cons.prems unfolding st_eq by simp
  have head_range:
    "hash_range_budget ?B
      (fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
    unfolding bf_eq st_eq
    by (rule hash_range_budget_mono[OF head_le head_range_exact])
  have head_coll:
    "hash_collision_budget ?B
      (fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
    unfolding bf_eq st_eq
    by (rule hash_collision_budget_mono[OF head_le head_coll_exact])
  have tail_range:
    "hash_range_budget (length fl * ?B)
      (mfold z (map fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
    if out:
      "Some (z, t) \<in>
        set_dist (execute (fri_layer_opening_step bf st) s)"
    for z and s :: "('f, 'a) protocol_channel_scheme"
      and t :: "('f, 'a) protocol_channel_scheme"
  proof -
    from fri_layer_opening_step_outcome[OF out[unfolded bf_eq st_eq]]
    obtain xp xp_path xn xn_path x' where
      z_eq: "z = (i mod (len div 2), x', len div 2, pw + pw)"
      by blast
    have len_le: "floor_log len \<le> L"
      using Cons.prems unfolding st_eq by simp
    have next_len: "floor_log (len div 2) \<le> L"
      using floor_log_div2_le_self[of len] len_le by linarith
    have z_inv:
      "case z of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
      unfolding z_eq using next_len by simp
    show ?thesis
      by (rule hash_range_budget_fri_layer_opening_steps_mfold_state
          [OF z_inv])
  qed
  have tail_coll:
    "hash_collision_budget (length fl * ?B)
      (mfold z (map fri_layer_opening_step fl) ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad)"
    if out:
      "Some (z, t) \<in>
        set_dist (execute (fri_layer_opening_step bf st) s)"
    for z and s :: "('f, 'a) protocol_channel_scheme"
      and t :: "('f, 'a) protocol_channel_scheme"
  proof -
    from fri_layer_opening_step_outcome[OF out[unfolded bf_eq st_eq]]
    obtain xp xp_path xn xn_path x' where
      z_eq: "z = (i mod (len div 2), x', len div 2, pw + pw)"
      by blast
    have len_le: "floor_log len \<le> L"
      using Cons.prems unfolding st_eq by simp
    have next_len: "floor_log (len div 2) \<le> L"
      using floor_log_div2_le_self[of len] len_le by linarith
    have z_inv:
      "case z of (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
      unfolding z_eq using next_len by simp
    have ih_z:
      "hash_collision_budget (length fl * ?B)
        (mfold z (map fri_layer_opening_step fl) ::
          (nat \<times> 'f \<times> nat \<times> nat,
            ('f, 'a) protocol_channel_scheme) state_monad)"
      using Cons.IH[OF z_inv] by assumption
    show ?thesis
      by (rule ih_z)
  qed
  have "hash_collision_budget (?B + length fl * ?B)
      ((fri_layer_opening_step bf st ::
        (nat \<times> 'f \<times> nat \<times> nat,
          ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>z. mfold z (map fri_layer_opening_step fl)))"
    by (rule hash_collision_budget_bind_on_outcomes
        [OF head_range head_coll tail_range tail_coll])
  then show ?case
    by (simp add: add.assoc add.commute add.left_commute)
qed

lemma hash_collision_budget_receive_query_commits_mfold:
  assumes init: "floor_log len \<le> L"
  shows
    "hash_collision_budget
      (length fl * (Suc L + Suc L))
      (mfold (i, x, len, pw) (receive_query_commits fl))"
  unfolding receive_query_commits_eq_fri_layer_opening_steps
proof -
  have st_inv:
    "case (i, x, len, pw) of
      (i, x, len, pw) \<Rightarrow> floor_log len \<le> L"
    using init by simp
  show "hash_collision_budget (length fl * (Suc L + Suc L))
    (mfold (i, x, len, pw) (map fri_layer_opening_step fl) ::
      (nat \<times> 'f \<times> nat \<times> nat,
        ('f, 'a) protocol_channel_scheme) state_monad)"
    by (rule hash_collision_budget_fri_layer_opening_steps_mfold_state
        [OF st_inv])
qed

lemma hash_target_program_query_decommitment_step:
  "hash_target_program B (Suc (floor_log (scale * clength)))
    (query_decommitment_step fr i)"
proof -
  let ?len = "scale * clength"
  have after_path:
    "hash_target_program B (Suc (floor_log ?len))
      ((ntimes read (floor_log ?len) ::
          ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>path.
          (check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))"
    for qh
  proof (rule hash_target_program_ntimes_read_bind)
    fix path :: "'f list"
    assume path_len: "length path = floor_log ?len"
    have "hash_target_program B (Suc (length path))
        ((check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (rule hash_target_program_check_authentication_path_assert_return)
    then show "hash_target_program B (Suc (floor_log ?len))
        ((check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (subst path_len[symmetric])
  qed
  have "hash_target_program B (0 + Suc (floor_log ?len))
      (read \<bind>
        (\<lambda>qh. (ntimes read (floor_log ?len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>path.
            (check_authentication_path ?len i qh path ::
              ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))))"
    by (rule hash_target_program_bind
        [OF hash_target_program_read after_path])
  then show ?thesis
    unfolding query_decommitment_step_def by (simp add: Let_def)
qed

lemma hash_target_program_check_decommit_on_query:
  "hash_target_program B
    (powers * Suc (floor_log (scale * clength)))
    (mmap (check_decommit_on_query fr idx))"
proof -
  let ?b = "Suc (floor_log (scale * clength))"
  let ?steps =
    "(map (query_decommitment_step fr) (powers_scaled idx) ::
      ('f, ('f, 'a) protocol_channel_scheme) state_monad list)"
  have step_budget:
    "\<And>(m :: ('f, ('f, 'a) protocol_channel_scheme) state_monad).
      m \<in> set ?steps \<Longrightarrow>
      hash_target_program B ?b m"
  proof -
    fix m :: "('f, ('f, 'a) protocol_channel_scheme) state_monad"
    assume "m \<in> set ?steps"
    then obtain i where "i \<in> set (powers_scaled idx)"
      and m_eq: "m = query_decommitment_step fr i"
      by auto
    show "hash_target_program B ?b m"
      unfolding m_eq by (rule hash_target_program_query_decommitment_step)
  qed
  have map_budget:
    "hash_target_program B (length ?steps * ?b) (mmap ?steps)"
    by (rule hash_target_program_mmap) (rule step_budget)
  then have "hash_target_program B
      (length (powers_scaled idx) * ?b) (mmap ?steps)"
    by simp
  then show ?thesis
    unfolding check_decommit_on_query_def query_decommitment_step_def
      powers_scaled_def
    by simp
qed

lemma hash_range_budget_query_decommitment_step:
  "hash_range_budget (Suc (floor_log (scale * clength)))
    (query_decommitment_step fr i)"
proof -
  let ?len = "scale * clength"
  have after_path:
    "hash_range_budget (Suc (floor_log ?len))
      ((ntimes read (floor_log ?len) ::
          ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>path.
          (check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))" for qh
  proof (rule hash_range_budget_ntimes_read_bind)
    fix path :: "'f list"
    assume path_len: "length path = floor_log ?len"
    have "hash_range_budget (Suc (length path))
        (((check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))"
      by (rule hash_range_budget_check_authentication_path_assert_return)
    note path_budget = this
    show "hash_range_budget (Suc (floor_log ?len))
        ((check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (subst path_len[symmetric]) (rule path_budget)
  qed
  have "hash_range_budget (0 + Suc (floor_log ?len))
      (read \<bind>
        (\<lambda>qh. (ntimes read (floor_log ?len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>path.
            (check_authentication_path ?len i qh path ::
              ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))))"
    by (rule hash_range_budget_bind[OF hash_range_budget_read after_path])
  then show ?thesis
    unfolding query_decommitment_step_def by (simp add: Let_def)
qed

lemma hash_collision_budget_query_decommitment_step:
  "hash_collision_budget (Suc (floor_log (scale * clength)))
    (query_decommitment_step fr i)"
proof -
  let ?len = "scale * clength"
  have after_path_range:
    "hash_range_budget (Suc (floor_log ?len))
      ((ntimes read (floor_log ?len) ::
          ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>path.
          (check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))" for qh
  proof (rule hash_range_budget_ntimes_read_bind)
    fix path :: "'f list"
    assume path_len: "length path = floor_log ?len"
    have "hash_range_budget (Suc (length path))
        (((check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))"
      by (rule hash_range_budget_check_authentication_path_assert_return)
    note path_budget = this
    show "hash_range_budget (Suc (floor_log ?len))
        ((check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (subst path_len[symmetric]) (rule path_budget)
  qed
  have after_path_coll:
    "hash_collision_budget (Suc (floor_log ?len))
      ((ntimes read (floor_log ?len) ::
          ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
        (\<lambda>path.
          (check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
            (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))" for qh
  proof (rule hash_collision_budget_ntimes_read_bind)
    fix path :: "'f list"
    assume path_len: "length path = floor_log ?len"
    have range_bind:
      "hash_range_budget (Suc (length path))
        (((check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))"
      by (rule hash_range_budget_check_authentication_path_assert_return)
    show "hash_range_budget (Suc (floor_log ?len))
        ((check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (subst path_len[symmetric]) (rule range_bind)
    have "hash_collision_budget (Suc (length path))
        (((check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh))))"
      by (rule hash_collision_budget_check_authentication_path_assert_return)
    note path_budget = this
    show "hash_collision_budget (Suc (floor_log ?len))
        ((check_authentication_path ?len i qh path ::
            ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))"
      by (subst path_len[symmetric]) (rule path_budget)
  qed
  have "hash_collision_budget (0 + Suc (floor_log ?len))
      (read \<bind>
        (\<lambda>qh. (ntimes read (floor_log ?len) ::
            ('f list, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
          (\<lambda>path.
            (check_authentication_path ?len i qh path ::
              ('f, ('f, 'a) protocol_channel_scheme) state_monad) \<bind>
              (\<lambda>ap. assert (ap = fr) \<bind> (\<lambda>_. return qh)))))"
    by (rule hash_collision_budget_bind
        [OF hash_range_budget_read hash_collision_budget_read
          after_path_range after_path_coll])
  then show ?thesis
    unfolding query_decommitment_step_def by (simp add: Let_def)
qed

lemma hash_range_budget_check_decommit_on_query:
  "hash_range_budget
    (powers * Suc (floor_log (scale * clength)))
    (mmap (check_decommit_on_query fr idx))"
proof -
  let ?b = "Suc (floor_log (scale * clength))"
  let ?steps =
    "(map (query_decommitment_step fr) (powers_scaled idx) ::
      ('f, ('f, 'a) protocol_channel_scheme) state_monad list)"
  have step_budget:
    "\<And>(m :: ('f, ('f, 'a) protocol_channel_scheme) state_monad).
      m \<in> set ?steps \<Longrightarrow>
      hash_range_budget ?b m"
  proof -
    fix m :: "('f, ('f, 'a) protocol_channel_scheme) state_monad"
    assume "m \<in> set ?steps"
    then obtain i where "i \<in> set (powers_scaled idx)"
      and m_eq: "m = query_decommitment_step fr i"
      by auto
    show "hash_range_budget ?b m"
      unfolding m_eq by (rule hash_range_budget_query_decommitment_step)
  qed
  have map_budget:
    "hash_range_budget
      (length ?steps * ?b) (mmap ?steps)"
    by (rule hash_range_budget_mmap) (rule step_budget)
  then have "hash_range_budget (length (powers_scaled idx) * ?b)
      (mmap ?steps)"
    by simp
  then show ?thesis
    unfolding check_decommit_on_query_def query_decommitment_step_def
      powers_scaled_def
    by simp
qed

lemma hash_collision_budget_check_decommit_on_query:
  "hash_collision_budget
    (powers * Suc (floor_log (scale * clength)))
    (mmap (check_decommit_on_query fr idx))"
proof -
  let ?b = "Suc (floor_log (scale * clength))"
  let ?steps =
    "(map (query_decommitment_step fr) (powers_scaled idx) ::
      ('f, ('f, 'a) protocol_channel_scheme) state_monad list)"
  have step_range:
    "\<And>(m :: ('f, ('f, 'a) protocol_channel_scheme) state_monad).
      m \<in> set ?steps \<Longrightarrow>
      hash_range_budget ?b m"
  proof -
    fix m :: "('f, ('f, 'a) protocol_channel_scheme) state_monad"
    assume "m \<in> set ?steps"
    then obtain i where "i \<in> set (powers_scaled idx)"
      and m_eq: "m = query_decommitment_step fr i"
      by auto
    show "hash_range_budget ?b m"
      unfolding m_eq by (rule hash_range_budget_query_decommitment_step)
  qed
  have step_coll:
    "\<And>(m :: ('f, ('f, 'a) protocol_channel_scheme) state_monad).
      m \<in> set ?steps \<Longrightarrow>
      hash_collision_budget ?b m"
  proof -
    fix m :: "('f, ('f, 'a) protocol_channel_scheme) state_monad"
    assume "m \<in> set ?steps"
    then obtain i where "i \<in> set (powers_scaled idx)"
      and m_eq: "m = query_decommitment_step fr i"
      by auto
    show "hash_collision_budget ?b m"
      unfolding m_eq by (rule hash_collision_budget_query_decommitment_step)
  qed
  have map_budget:
    "hash_collision_budget
      (length ?steps * ?b) (mmap ?steps)"
    apply (rule hash_collision_budget_mmap)
     apply (rule step_range, assumption)
    apply (rule step_coll, assumption)
    done
  then have "hash_collision_budget (length (powers_scaled idx) * ?b)
      (mmap ?steps)"
    by simp
  then show ?thesis
    unfolding check_decommit_on_query_def query_decommitment_step_def
      powers_scaled_def
    by simp
qed

end

end
