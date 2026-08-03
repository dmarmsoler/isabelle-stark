(*  Title:      Stark/Prob_Monad.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Prob_Monad
  imports
    Prob_Dist
begin

section \<open>Probabilistic State Monad\<close>

text \<open>
  This theory defines the finite probabilistic state monad used throughout the
  formalization.  It includes monadic combinators, failure, assertions, and a
  weakest-precondition calculus for probabilistic events.
\<close>

typedef ('a, 's) state_monad = "UNIV::('s \<Rightarrow> (('a \<times> 's) option) dist) set"
  morphisms execute create
  by simp

lemma execute_create: "execute (create f) = f" using create_inverse by simp

setup_lifting type_definition_state_monad

subsubsection \<open>Bind\<close>

definition map_bind :: "('s \<Rightarrow> ('a \<rightharpoonup> prob)) \<Rightarrow> ('a \<Rightarrow> ('b \<rightharpoonup> prob)) \<Rightarrow> ('s \<Rightarrow> ('b \<rightharpoonup> prob))"
where
  "map_bind m k s =
    (\<lambda>b.
      let p =
        (\<Sum>i\<in>dom (m s).
          (the (m s i))
          * (option_default (k i b)))
      in if p = 0 then None else Some p)"

lemma map_bind_nonzero_on_dom:
  assumes "x \<in> dom (map_bind m k s)"
  shows "the (map_bind m k s x) \<noteq> 0"
proof -
  show ?thesis
    using assms
    unfolding map_bind_def
    by (auto simp: Let_def split: if_splits)
qed

lemma option_default_map_bind:
  "option_default (map_bind m k s x) =
    (\<Sum>i\<in>dom (m s).
      the (m s i) * option_default (k i x))"
  unfolding map_bind_def by (simp add: Let_def)

lemma map_bind_eq_from_option_default:
  assumes
    "option_default (map_bind m k s x) =
      option_default (map_bind m' k' s' x)"
  shows "map_bind m k s x = map_bind m' k' s' x"
proof -
  show ?thesis
    using assms
    unfolding map_bind_def
    by (simp add: Let_def)
qed

lemma map_bind_cong:
  assumes m_eq: "m s = m' s"
  assumes k_eq: "\<And>i. i \<in> dom (m s) \<Longrightarrow> k i = k' i"
  shows "map_bind m k s = map_bind m' k' s"
proof
  fix x
  have dom_eq: "dom (m' s) = dom (m s)"
    using m_eq by simp
  show "map_bind m k s x = map_bind m' k' s x"
    unfolding map_bind_def Let_def
    using m_eq dom_eq k_eq
    by (intro if_cong refl arg_cong[where f=Some] sum.cong) auto
qed

lemma map_bind_cong_state:
  assumes m_eq: "m s = m' s'"
  assumes k_eq: "\<And>i. i \<in> dom (m s) \<Longrightarrow> k i = k' i"
  shows "map_bind m k s = map_bind m' k' s'"
proof
  fix x
  have dom_eq: "dom (m' s') = dom (m s)"
    using m_eq by simp
  show "map_bind m k s x = map_bind m' k' s' x"
    unfolding map_bind_def Let_def
    using m_eq dom_eq k_eq
    by (intro if_cong refl arg_cong[where f=Some] sum.cong) auto
qed

lemma dom_map_bind:
  "dom (map_bind m k s) =
    {x \<in> (\<Union>i\<in>dom (m s). dom (k i)).
      (\<Sum>i\<in>dom (m s).
        the (m s i) * option_default (k i x)) \<noteq> 0}"
proof -
  let ?M = "dom (m s)"
  let ?K = "\<lambda>i. k i"
  let ?D = "\<Union>i\<in>?M. dom (?K i)"
  let ?p = "\<lambda>x. \<Sum>i\<in>?M. the (m s i) * option_default (?K i x)"

  have outside_zero: "x \<notin> ?D \<Longrightarrow> ?p x = 0" for x
  proof -
    assume x: "x \<notin> ?D"
    have "\<And>i. i \<in> ?M \<Longrightarrow> option_default (?K i x) = 0"
      using x by (simp add: domIff)
    then show "?p x = 0"
      by simp
  qed

  show ?thesis
  proof
    show "dom (map_bind m k s) \<subseteq> {x \<in> ?D. ?p x \<noteq> 0}"
    proof
      fix x
      assume x_dom: "x \<in> dom (map_bind m k s)"

      have px_ne: "?p x \<noteq> 0"
        using x_dom
        unfolding map_bind_def
        by (fastforce simp: Let_def split: if_splits)

      moreover have "x \<in> ?D"
        using px_ne outside_zero by blast

      ultimately show "x \<in> {x \<in> ?D. ?p x \<noteq> 0}"
        by simp
    qed
  next
    show "{x \<in> ?D. ?p x \<noteq> 0} \<subseteq> dom (map_bind m k s)"
    proof
      fix x
      assume x: "x \<in> {x \<in> ?D. ?p x \<noteq> 0}"

      show "x \<in> dom (map_bind m k s)"
        using x
        unfolding map_bind_def
        apply (simp add: Let_def) by auto
    qed
  qed
qed

lemma sum_option_default_superset:
  assumes fin_D: "finite D"
  assumes dom_subset: "dom f \<subseteq> D"
  shows "(\<Sum>x\<in>D. option_default (f x)) = sum_map f"
proof -
  have "(\<Sum>x\<in>D. option_default (f x)) =
    (\<Sum>x\<in>D \<inter> dom f. option_default (f x))"
    using fin_D
    apply (intro sum.mono_neutral_right)
    apply auto
    by (metis not_None_eq option.case_eq_if)
  also have "... = (\<Sum>x\<in>dom f. option_default (f x))"
    using dom_subset by (simp add: inf.absorb2)
  also have "... = (\<Sum>x\<in>dom f. the (f x))"
    by (intro sum.cong) auto
  finally show ?thesis
    unfolding sum_map_def .
qed

lemma sum_option_default_mult_superset:
  assumes fin_D: "finite D"
  assumes dom_subset: "dom f \<subseteq> D"
  shows "(\<Sum>x\<in>D. option_default (f x) * g x) =
    (\<Sum>x\<in>dom f. the (f x) * g x)"
proof -
  have "(\<Sum>x\<in>D. option_default (f x) * g x) =
    (\<Sum>x\<in>dom f. option_default (f x) * g x)"
    using fin_D dom_subset
    by (intro sum.mono_neutral_right) (auto simp: dom_def)
  also have "... = (\<Sum>x\<in>dom f. the (f x) * g x)"
    by (intro sum.cong) auto
  finally show ?thesis .
qed

lemma the_map_bind_on_dom:
  assumes "x \<in> dom (map_bind m k s)"
  shows
    "the (map_bind m k s x) =
      (\<Sum>i\<in>dom (m s).
        the (m s i) * option_default (k i x))"
proof -
  show ?thesis
    using assms
    unfolding map_bind_def
    by (fastforce simp: Let_def split: if_splits)
qed

lemma finite_dom_bind:
  assumes fin_m: "finite (dom (m s))"
  assumes fin_k: "\<forall>i \<in> dom (m s). finite (dom (k i))"
  shows "finite (dom (map_bind m k s))"
proof -
  let ?D = "\<Union>i\<in>dom (m s). dom (k i)"

  have fin_D: "finite ?D"
    using fin_m fin_k by auto

  have "finite
    {x \<in> ?D.
      (\<Sum>i\<in>dom (m s).
        the (m s i) * option_default (k i x)) \<noteq> 0}"
    using fin_D fin_m by simp

  then show ?thesis
    by (simp add: dom_map_bind)
qed

lemma sum_map_bind_1:
  assumes fin_m: "finite (dom (m s))"
  assumes fin_k: "\<forall>i \<in> dom (m s). finite (dom (k i))"
  assumes sum_m: "sum_map (m s) = 1"
  assumes sum_k: "\<forall>i \<in> dom (m s). sum_map (k i) = 1"
  shows "sum_map (map_bind m k s) = 1"
proof -
  let ?M = "dom (m s)"
  let ?K = "\<lambda>i. k i"
  let ?D = "\<Union>i\<in>?M. dom (?K i)"
  let ?p = "\<lambda>x. \<Sum>i\<in>?M. the (m s i) * option_default (?K i x)"

  have fin_D: "finite ?D"
    using fin_m fin_k by auto

  have "sum_map (map_bind m k s) =
    (\<Sum>x\<in>dom (map_bind m k s). the (map_bind m k s x))"
    unfolding sum_map_def by simp

  also have "... = (\<Sum>x\<in>dom (map_bind m k s). ?p x)"
    by (intro sum.cong) (simp_all add: the_map_bind_on_dom)

  also have "... = (\<Sum>x\<in>{x \<in> ?D. ?p x \<noteq> 0}. ?p x)"
    by (simp add: dom_map_bind)

  also have "... = (\<Sum>x\<in>?D. ?p x)"
    using fin_D
    apply (intro sum.mono_neutral_cong_left) using assms(1) by auto

  also have "... = (\<Sum>i\<in>?M. \<Sum>x\<in>?D.
      the (m s i) * option_default (?K i x))"
    by (rule sum.swap)

  also have "... = (\<Sum>i\<in>?M.
      the (m s i) * (\<Sum>x\<in>?D. option_default (?K i x)))"
    by (simp add: sum_distrib_left)

  also have "... = (\<Sum>i\<in>?M. the (m s i) * sum_map (?K i))"
  proof (intro sum.cong refl)
    fix i
    assume i: "i \<in> ?M"
    have "dom (?K i) \<subseteq> ?D"
      using i by auto
    then show
      "the (m s i) * (\<Sum>x\<in>?D. option_default (?K i x)) =
       the (m s i) * sum_map (?K i)"
      using sum_option_default_superset[OF fin_D, of "?K i"]
      by simp
  qed

  also have "... = (\<Sum>i\<in>?M. the (m s i) * 1)"
    using sum_k by simp

  also have "... = sum_map (m s)"
    unfolding sum_map_def by simp

  also have "... = 1"
    using sum_m .

  finally show ?thesis .
qed

lemma map_bind_delta_left:
  fixes k :: "'a \<Rightarrow> 'b \<rightharpoonup> prob"
  assumes clean: "\<And>x. x \<in> dom (k a) \<Longrightarrow> the (k a x) \<noteq> 0"
  shows "map_bind (\<lambda>_. delta_map a) k s = k a"
proof
  fix x :: 'b
  show "map_bind (\<lambda>_. delta_map a) k s x = k a x"
  proof (cases "k a x")
    case None
    then show ?thesis
      unfolding map_bind_def delta_map_def
      by (simp add: Let_def)
  next
    case (Some p)
    then have "p \<noteq> 0"
      using clean[of x] by auto
    then show ?thesis
      unfolding map_bind_def delta_map_def
      using Some by (simp add: Let_def)
  qed
qed

lemma map_bind_delta_left_state:
  fixes k :: "'a \<Rightarrow> 'b \<rightharpoonup> prob"
  assumes clean: "\<And>x. x \<in> dom (k (f s)) \<Longrightarrow> the (k (f s) x) \<noteq> 0"
  shows "map_bind (\<lambda>t. delta_map (f t)) k s = k (f s)"
proof
  fix x :: 'b
  show "map_bind (\<lambda>t. delta_map (f t)) k s x = k (f s) x"
  proof (cases "k (f s) x")
    case None
    then show ?thesis
      unfolding map_bind_def delta_map_def
      by (simp add: Let_def)
  next
    case (Some p)
    then have "p \<noteq> 0"
      using clean[of x] by auto
    then show ?thesis
      unfolding map_bind_def delta_map_def
      using Some by (simp add: Let_def)
  qed
qed

lemma map_bind_delta_right:
  fixes m :: "'s \<Rightarrow> 'a \<rightharpoonup> prob"
  assumes fin: "finite (dom (m s))"
  assumes clean: "\<And>x. x \<in> dom (m s) \<Longrightarrow> the (m s x) \<noteq> 0"
  shows "map_bind m (\<lambda>a. delta_map a) s = m s"
proof
  fix x :: 'a
  have sum_delta:
    "(\<Sum>i\<in>dom (m s).
        the (m s i) *
          option_default (delta_map i x)) =
      (if x \<in> dom (m s) then the (m s x) else 0)"
  proof -
    have "(\<Sum>i\<in>dom (m s).
        the (m s i) *
          option_default (delta_map i x)) =
      (\<Sum>i\<in>dom (m s). if i = x then the (m s i) else 0)"
      by (intro sum.cong refl) (simp add: delta_map_def)
    also have "... = (if x \<in> dom (m s) then the (m s x) else 0)"
      using fin by (simp add: sum.delta)
    finally show ?thesis .
  qed
  show "map_bind m (\<lambda>a. delta_map a) s x = m s x"
  proof (cases "x \<in> dom (m s)")
    case True
    then have "m s x = Some (the (m s x))"
      by auto
    moreover have "the (m s x) \<noteq> 0"
      using True by (rule clean)
    ultimately show ?thesis
      unfolding map_bind_def
      using sum_delta True by (simp add: Let_def)
  next
    case False
    then have "m s x = None"
      by auto
    then show ?thesis
      unfolding map_bind_def
      using sum_delta False by (simp add: Let_def)
  qed
qed

lemma map_bind_assoc:
  fixes m :: "'s \<Rightarrow> 'a \<rightharpoonup> prob"
    and k :: "'a \<Rightarrow> 'b \<rightharpoonup> prob"
    and h :: "'b \<Rightarrow> 'c \<rightharpoonup> prob"
  assumes fin_m: "finite (dom (m s))"
  assumes fin_k: "\<And>i. i \<in> dom (m s) \<Longrightarrow> finite (dom (k i))"
  shows
    "map_bind (map_bind m k) h s =
      map_bind m (\<lambda>a. map_bind (\<lambda>_. k a) h ()) s"
proof
  fix x :: 'c

  let ?M = "dom (m s)"
  let ?K = "\<lambda>i. k i"
  let ?D = "\<Union>i\<in>?M. dom (?K i)"
  let ?H = "\<lambda>j. option_default (h j x)"
  let ?p = "\<lambda>j. \<Sum>i\<in>?M. the (m s i) * option_default (?K i j)"

  have fin_D: "finite ?D"
    using fin_m fin_k by auto

  have left_sum:
    "(\<Sum>j\<in>dom (map_bind m k s).
        the (map_bind m k s j) * ?H j) =
      (\<Sum>j\<in>?D. ?p j * ?H j)"
  proof -
    have "(\<Sum>j\<in>dom (map_bind m k s).
        the (map_bind m k s j) * ?H j) =
      (\<Sum>j\<in>{j \<in> ?D. ?p j \<noteq> 0}.
        the (map_bind m k s j) * ?H j)"
      by (simp add: dom_map_bind)
    also have "... =
      (\<Sum>j\<in>{j \<in> ?D. ?p j \<noteq> 0}. ?p j * ?H j)"
      by (intro sum.cong refl) (simp add: dom_map_bind the_map_bind_on_dom)
    also have "... = (\<Sum>j\<in>?D. ?p j * ?H j)"
      using fin_D
      by (intro sum.mono_neutral_left) auto
    finally show ?thesis .
  qed

  have swap_sum:
    "(\<Sum>j\<in>?D. ?p j * ?H j) =
      (\<Sum>i\<in>?M.
        the (m s i) *
          (\<Sum>j\<in>dom (?K i).
            the (?K i j) * ?H j))"
  proof -
    have "(\<Sum>j\<in>?D. ?p j * ?H j) =
      (\<Sum>j\<in>?D. \<Sum>i\<in>?M.
        the (m s i) * option_default (?K i j) * ?H j)"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... =
      (\<Sum>i\<in>?M. \<Sum>j\<in>?D.
        the (m s i) * option_default (?K i j) * ?H j)"
      by (rule sum.swap)
    also have "... =
      (\<Sum>i\<in>?M.
        the (m s i) *
          (\<Sum>j\<in>?D. option_default (?K i j) * ?H j))"
      by (simp add: sum_distrib_left algebra_simps)
    also have "... =
      (\<Sum>i\<in>?M.
        the (m s i) *
          (\<Sum>j\<in>dom (?K i). the (?K i j) * ?H j))"
    proof (intro sum.cong refl)
      fix i
      assume i: "i \<in> ?M"
      have "dom (?K i) \<subseteq> ?D"
        using i by auto
      then show
        "the (m s i) *
          (\<Sum>j\<in>?D. option_default (?K i j) * ?H j) =
        the (m s i) *
          (\<Sum>j\<in>dom (?K i). the (?K i j) * ?H j)"
        using sum_option_default_mult_superset[OF fin_D, of "?K i" ?H]
        by simp
    qed
    finally show ?thesis .
  qed

  have sums_eq:
    "(\<Sum>j\<in>dom (map_bind m k s).
        the (map_bind m k s j) * ?H j) =
      (\<Sum>i\<in>?M.
        the (m s i) *
          option_default (map_bind (\<lambda>_. k i) h () x))"
  proof -
    have "(\<Sum>j\<in>dom (map_bind m k s).
        the (map_bind m k s j) * ?H j) =
      (\<Sum>i\<in>?M.
        the (m s i) *
          (\<Sum>j\<in>dom (?K i). the (?K i j) * ?H j))"
      using left_sum swap_sum by simp
    also have "... =
      (\<Sum>i\<in>?M.
        the (m s i) *
          option_default (map_bind (\<lambda>_. k i) h () x))"
      by (intro sum.cong refl) (simp add: option_default_map_bind)
    finally show ?thesis .
  qed

  show
    "map_bind (map_bind m k) h s x =
      map_bind m (\<lambda>a. map_bind (\<lambda>_. k a) h ()) s x"
  proof (rule map_bind_eq_from_option_default)
    show
      "option_default (map_bind (map_bind m k) h s x) =
        option_default (map_bind m (\<lambda>a. map_bind (\<lambda>_. k a) h ()) s x)"
      using sums_eq
      by (simp add: option_default_map_bind)
  qed
qed

definition bind_cont_map ::
  "('a \<Rightarrow> 's \<Rightarrow> (('b \<times> 's) option \<rightharpoonup> prob)) \<Rightarrow>
    ('a \<times> 's) option \<Rightarrow> (('b \<times> 's) option \<rightharpoonup> prob)"
where
  "bind_cont_map k r =
    (case r of
      None \<Rightarrow> delta_map None
    | Some (a, s') \<Rightarrow> k a s')"

lemma bind_cont_map_return:
  "bind_cont_map (\<lambda>a s. delta_map (Some (a, s))) r = delta_map r"
  unfolding bind_cont_map_def
  by (cases r) auto

lemma finite_dom_bind_cont_mapI:
  assumes "\<And>a s. finite (dom (k a s))"
  shows "finite (dom (bind_cont_map k r))"
  using assms
  unfolding bind_cont_map_def
  by (cases r) (auto simp: delta_map_def split: prod.splits)

lemma sum_map_bind_cont_mapI:
  assumes "\<And>a s. sum_map (k a s) = 1"
  shows "sum_map (bind_cont_map k r) = 1"
  using assms
  unfolding bind_cont_map_def sum_map_def
  by (cases r) (auto simp: delta_map_def split: prod.splits)

lift_definition dist_bind ::
  "('s \<Rightarrow> (('a \<times> 's) option) dist) \<Rightarrow>
    ('a \<Rightarrow> ('s \<Rightarrow> (('b \<times> 's) option) dist)) \<Rightarrow>
    ('s \<Rightarrow> (('b \<times> 's) option) dist)"
is "\<lambda>m k. map_bind m (bind_cont_map k)"
proof -
  fix m :: "'s \<Rightarrow> (('a \<times> 's) option \<rightharpoonup> prob)"
    and k :: "'a \<Rightarrow> 's \<Rightarrow> (('b \<times> 's) option \<rightharpoonup> prob)"
    and s :: 's
  assume m:
    "\<And>s. finite (dom (m s)) \<and> sum_map (m s) = 1 \<and>
      (\<forall>x\<in>dom (m s). the (m s x) \<noteq> 0)"
  assume k:
    "\<And>a s. finite (dom (k a s)) \<and> sum_map (k a s) = 1 \<and>
      (\<forall>x\<in>dom (k a s). the (k a s x) \<noteq> 0)"
  show "finite (dom (map_bind m (bind_cont_map k) s)) \<and>
    sum_map (map_bind m (bind_cont_map k) s) = 1 \<and>
    (\<forall>x\<in>dom (map_bind m (bind_cont_map k) s).
      the (map_bind m (bind_cont_map k) s x) \<noteq> 0)"
  proof (intro conjI ballI)
    show "finite (dom (map_bind m (bind_cont_map k) s))"
      by (rule finite_dom_bind) (use m k in
        \<open>auto intro!: finite_dom_bind_cont_mapI simp: bind_cont_map_def delta_map_def split: option.splits prod.splits\<close>)
    show "sum_map (map_bind m (bind_cont_map k) s) = 1"
      by (rule sum_map_bind_1) (use m k in
        \<open>auto intro!: sum_map_bind_cont_mapI simp: bind_cont_map_def delta_map_def sum_map_def split: option.splits prod.splits\<close>)
    fix x
    assume "x \<in> dom (map_bind m (bind_cont_map k) s)"
    then show "the (map_bind m (bind_cont_map k) s x) \<noteq> 0"
      by (rule map_bind_nonzero_on_dom)
  qed
qed

lift_definition
  sm_bind :: "('a, 's) state_monad \<Rightarrow> ('a \<Rightarrow> ('b, 's) state_monad) \<Rightarrow> ('b, 's) state_monad"
  (infixl ">>=" 60)
  is dist_bind .

subsubsection \<open>Return\<close>

definition dist_return :: "'a \<Rightarrow> ('s \<Rightarrow> (('a \<times> 's) option) dist)"
  where "dist_return a = (\<lambda>s. delta_dist (Some (a, s)))"

lift_definition return :: "'a \<Rightarrow> ('a, 's) state_monad"
is dist_return .

definition dist_throw :: "'s \<Rightarrow> (('a \<times> 's) option) dist"
  where "dist_throw = (\<lambda>_. delta_dist None)"

lift_definition throw :: "('a, 's) state_monad"
is dist_throw .

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> sm_bind

subsubsection \<open>Monad laws\<close>

lemma dist_bind_return_left:
  "dist_bind (dist_return a) k = k a"
proof
  fix s
  show "dist_bind (dist_return a) k s = k a s"
    apply (rule dist_inject[THEN iffD1])
    unfolding dist_bind.rep_eq dist_return_def
    apply (simp add: o_def map_fun_def dist_delta_dist)
    apply (subst map_bind_delta_left_state[where f="\<lambda>t. Some (a, t)"])
    by (auto simp: bind_cont_map_def split: option.splits prod.splits)
qed

lemma sm_bind_return_left[simp]:
  "sm_bind (return a) k = k a"
  by transfer (rule dist_bind_return_left)

lemma dist_bind_return_right:
  "dist_bind m (\<lambda>a. dist_return a) = m"
proof
  fix s
  have cont:
    "bind_cont_map (\<lambda>x xa. delta_map (Some (x, xa))) = (\<lambda>r. delta_map r)"
    by (rule ext) (simp add: bind_cont_map_return)
  show "dist_bind m (\<lambda>a. dist_return a) s = m s"
    apply (rule dist_inject[THEN iffD1])
    unfolding dist_bind.rep_eq dist_return_def
    apply (simp add: o_def map_fun_def dist_delta_dist)
    apply (subst cont)
    by (simp add: map_bind_delta_right)
qed

lemma sm_bind_return_right[simp]:
  "sm_bind m return = m"
  by transfer (rule dist_bind_return_right)

lemma dist_bind_assoc:
  "dist_bind (dist_bind m k) h =
    dist_bind m (\<lambda>a. dist_bind (k a) h)"
proof
  fix s
  let ?M = "\<lambda>s. dist (m s)"
  let ?K = "bind_cont_map (\<lambda>a t. dist (k a t))"
  let ?H = "bind_cont_map (\<lambda>a t. dist (h a t))"
  let ?R = "bind_cont_map (\<lambda>a t. map_bind (\<lambda>u. dist (k a u)) ?H t)"
  have assoc:
    "map_bind (map_bind ?M ?K) ?H s =
      map_bind ?M (\<lambda>r. map_bind (\<lambda>_. ?K r) ?H ()) s"
    by (rule map_bind_assoc) (auto intro!: finite_dom_bind_cont_mapI)
  have cont:
    "map_bind (\<lambda>_. ?K r) ?H () = ?R r" for r
  proof (cases r)
    case None
    then show ?thesis
      apply (simp add: bind_cont_map_def)
      apply (subst map_bind_delta_left[where a=None])
       apply (auto simp: bind_cont_map_def delta_map_def split: option.splits prod.splits)
      done
  next
    case (Some as)
    obtain a t where r: "r = Some (a, t)"
      using Some by (cases as) simp
    show ?thesis
      unfolding r bind_cont_map_def
      apply (simp add: map_fun_def)
      by (rule map_bind_cong_state) simp_all
  qed
  show
    "dist_bind (dist_bind m k) h s =
      dist_bind m (\<lambda>a. dist_bind (k a) h) s"
    apply (rule dist_inject[THEN iffD1])
    unfolding dist_bind.rep_eq
    using assoc
    apply (simp add: o_def map_fun_def dist_bind.rep_eq)
    apply (rule map_bind_cong)
     apply simp
    using cont
    by simp
qed

lemma sm_bind_assoc:
  "sm_bind (sm_bind m k) h = sm_bind m (\<lambda>a. sm_bind (k a) h)"
  by transfer (rule dist_bind_assoc)

subsection \<open>Monad Operations\<close>

subsubsection \<open>Basic Operators\<close>

definition dist_get :: "'s \<Rightarrow> ((('s \<times> 's) option) dist)"
 where
  "dist_get = (\<lambda>s. delta_dist (Some (s,s)))"

lift_definition get :: "('s, 's) state_monad"
is dist_get .

definition dist_put :: "'s \<Rightarrow> 's \<Rightarrow> ((unit \<times> 's) option) dist" where
  "dist_put s = (\<lambda>_. delta_dist (Some ((),s)))"

lift_definition put :: "'s \<Rightarrow> (unit, 's) state_monad"
is dist_put .

definition lift_dist :: "('s \<Rightarrow> 'a dist) \<Rightarrow> 's \<Rightarrow> ((('a \<times> 's) option) dist)"
 where
  "lift_dist d = (\<lambda>s. dist_map (\<lambda>a. Some (a, s)) (d s))"

lift_definition lift :: "('s \<Rightarrow> 'a dist) \<Rightarrow> ('a, 's) state_monad"
is lift_dist .

definition modify :: "('s \<Rightarrow> 's) \<Rightarrow> (unit, 's) state_monad" where
"modify f = get \<bind> (\<lambda>s::'s. put (f s))"

definition assert :: "bool \<Rightarrow> (unit, 's) state_monad" where
 "assert b = (if b then return () else throw)"

primrec ntimes :: "('a, 's) state_monad \<Rightarrow> nat \<Rightarrow> ('a list, 's) state_monad"
  where
    "ntimes m 0 = return []"
  | "ntimes m (Suc n) =
      do {
        x \<leftarrow> m;
        xs \<leftarrow> ntimes m n;
        return (x # xs)
      }"

primrec mfold2 :: "('a \<Rightarrow> (unit,'s) state_monad) \<Rightarrow> 'a list \<Rightarrow> (unit, 's) state_monad"
  where
    "mfold2 m [] = return ()"
  | "mfold2 m (x # xs) =
      do {
        m x;
        mfold2 m xs
      }"

primrec mmap :: "('a,'s) state_monad list \<Rightarrow> ('a list, 's) state_monad"
  where
    "mmap [] = return []"
  | "mmap (m # ms) =
      do {
        x \<leftarrow> m;
        xs \<leftarrow> mmap ms;
        return (x # xs)
      }"

primrec mfold :: "'a \<Rightarrow> ('a \<Rightarrow> ('a,'s) state_monad) list \<Rightarrow> ('a, 's) state_monad"
  where
    "mfold a [] = return a"
  | "mfold a (m # ms) =
      do {
        x \<leftarrow> m a;
        mfold x ms
      }"

subsubsection \<open>Probabilistic Choice\<close>

definition die :: "nat \<Rightarrow> (nat, 's) state_monad"
  where "die n = create (\<lambda>s. dist_uniform (fset_of_list (map (\<lambda>x. Some (x,s)) [1..<Suc n])))"

definition coin :: "prob \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a, 's) state_monad"
  where "coin f x y = create (\<lambda>s. dist_of_fset {|(Some (x,s),f),(Some (y,s),1-f)|})"

subsection \<open>Weakest Precondition Calculus\<close>

definition dist_expect :: "'a dist \<Rightarrow> ('a \<Rightarrow> prob) \<Rightarrow> prob" where
  "dist_expect d Q = (\<Sum>x\<in>dom (dist d). the (dist d x) * Q x)"

lemma dist_expect_items:
  "dist_expect d Q = fsum (\<lambda>(x, p). p * Q x) (items d)"
  unfolding dist_expect_def fsum_items
  by simp

lemma dist_expect_return[simp]:
  "dist_expect (delta_dist x) Q = Q x"
  unfolding dist_expect_def
  by (simp add: dist_delta_dist delta_map_def)

lemma dist_expect_0[simp]:
  "dist_expect d (\<lambda>_. 0) = 0"
  unfolding dist_expect_def by simp

lemma dist_expect_indicator:
  "dist_expect d (\<lambda>x. if x = a then 1 else 0) =
    option_default (dist d a)"
proof -
  have "dist_expect d (\<lambda>x. if x = a then 1 else 0) =
      (\<Sum>x\<in>dom (dist d). if x = a then the (dist d x) else 0)"
    unfolding dist_expect_def
    by (intro sum.cong refl) simp
  also have "... = (if a \<in> dom (dist d) then the (dist d a) else 0)"
    by (simp add: sum.delta)
  also have "... = option_default (dist d a)"
    by (cases "dist d a") auto
  finally show ?thesis .
qed

lemma dist_expect_None:
  "dist_expect d (\<lambda>r. case r of None \<Rightarrow> 1 | Some _ \<Rightarrow> 0) =
    option_default (dist d None)"
proof -
  have eq: "(\<lambda>r. case r of None \<Rightarrow> 1 | Some _ \<Rightarrow> 0) =
    (\<lambda>r. if r = None then 1 else 0)"
    by (rule ext) (simp split: option.splits)
  have "dist_expect d (\<lambda>r. case r of None \<Rightarrow> 1 | Some _ \<Rightarrow> 0) =
    dist_expect d (\<lambda>r. if r = None then 1 else 0)"
    by (simp add: eq)
  also have "... = option_default (dist d None)"
    by (rule dist_expect_indicator)
  finally show ?thesis .
qed

lemma dist_expect_map:
  "dist_expect (dist_map f d) Q = dist_expect d (\<lambda>x. Q (f x))"
proof -
  let ?M = "dom (dist d)"
  have dom_map: "dom (dist (dist_map f d)) = f ` ?M"
    using set_dist_dist_map[of f d]
    unfolding set_dist_def by simp

  have "dist_expect (dist_map f d) Q =
    (\<Sum>x\<in>f ` ?M. the (dist (dist_map f d) x) * Q x)"
    unfolding dist_expect_def dom_map by simp
  also have "... =
    (\<Sum>x\<in>f ` ?M.
      (\<Sum>y\<in>{y \<in> ?M. f y = x}. the (dist d y)) * Q x)"
  proof (intro sum.cong refl)
    fix x
    assume x: "x \<in> f ` ?M"
    then have x_dom: "x \<in> dom (dist (dist_map f d))"
      using dom_map by simp
    have "the (dist (dist_map f d) x) =
      fsum snd (ffilter (\<lambda>i. f (fst i) = x) (items d))"
      using fsum_items_filter_dist_map_on_dom[OF x_dom]
      by simp
    also have "... = (\<Sum>y\<in>{y \<in> ?M. f y = x}. the (dist d y))"
      by (rule fsum_items_filter_dist_map)
    finally show
      "the (dist (dist_map f d) x) * Q x =
       (\<Sum>y\<in>{y \<in> ?M. f y = x}. the (dist d y)) * Q x"
      by simp
  qed
  also have "... =
    (\<Sum>x\<in>f ` ?M.
      (\<Sum>y\<in>{y \<in> ?M. f y = x}. the (dist d y) * Q (f y)))"
  proof (intro sum.cong refl)
    fix x
    show
      "(\<Sum>y\<in>{y \<in> ?M. f y = x}. the (dist d y)) * Q x =
       (\<Sum>y\<in>{y \<in> ?M. f y = x}. the (dist d y) * Q (f y))"
      by (subst sum_distrib_right) (intro sum.cong refl, auto)
  qed
  also have "... = (\<Sum>y\<in>?M. the (dist d y) * Q (f y))"
    by (rule sum.group) auto
  also have "... = dist_expect d (\<lambda>x. Q (f x))"
    unfolding dist_expect_def by simp
  finally show ?thesis .
qed

lemma fimage_fst_norm_fset_subset:
  assumes "fsum snd A \<noteq> 0"
  shows "fset (fimage fst (norm_fset A)) \<subseteq> fset (fimage fst A)"
proof
  fix x
  assume "x \<in> fset (fimage fst (norm_fset A))"
  then obtain p where xp: "(x, p) |\<in>| norm_fset A"
    by auto
  then show "x \<in> fset (fimage fst A)"
    using assms
    unfolding norm_fset_def squish_def
    by (force simp: Let_def split: prod.splits)
qed

lemma dom_dist_of_fset_subset:
  assumes "fsum snd A \<noteq> 0"
  shows "dom (dist (dist_of_fset A)) \<subseteq> fset (fimage fst A)"
proof -
  have dist_eq: "dist (dist_of_fset A) = map_of (norm_fset A)"
    using assms
    unfolding dist_of_fset.rep_eq map_of_fset_def
    by (simp add: Let_def)
  have "dom (dist (dist_of_fset A)) \<subseteq> fset (fimage fst (norm_fset A))"
    unfolding dist_eq
    by (rule dom_map_of_subset)
  also have "... \<subseteq> fset (fimage fst A)"
    by (rule fimage_fst_norm_fset_subset[OF assms])
  finally show ?thesis .
qed

lemma dom_dist_uniform_subset:
  assumes "xs \<noteq> {||}"
  shows "dom (dist (dist_uniform xs)) \<subseteq> fset xs"
proof -
  let ?A = "((\<lambda>x. (x, 1::prob)) |`| xs)"
  have total: "fsum snd ?A \<noteq> 0"
    using assms by (simp add: fsum_snd_uniform_ones)
  have "dom (dist (dist_uniform xs)) \<subseteq> fset (fimage fst ?A)"
    unfolding dist_uniform_def
    by (rule dom_dist_of_fset_subset[OF total])
  also have "... \<subseteq> fset xs"
    by auto
  finally show ?thesis .
qed

lemma fsum_snd_coin_nonzero:
  fixes p :: prob
  shows "fsum snd {|(a, p), (b, 1 - p)|} \<noteq> 0"
proof -
  have one_minus_zero: "(1::prob) - 0 = 1"
    by transfer simp
  have "p \<noteq> 0 \<or> 1 - p \<noteq> 0"
  proof (cases "p = 0")
    case True
    have "1 - p = 1"
      using True one_minus_zero by simp
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by simp
  qed
  then show ?thesis
  proof
    assume p: "p \<noteq> 0"
    have "(a, p) \<in> fset {|(a, p), (b, 1 - p)|}"
      by simp
    then show ?thesis
      using p
      unfolding fsum_fset_sum
      by (auto simp: sum_nonneg_eq_0_iff)
  next
    assume q: "1 - p \<noteq> 0"
    have "(b, 1 - p) \<in> fset {|(a, p), (b, 1 - p)|}"
      by simp
    then show ?thesis
      using q
      unfolding fsum_fset_sum
      by (auto simp: sum_nonneg_eq_0_iff)
  qed
qed

lemma dist_expect_bind:
  "dist_expect (dist_bind m k s) Q =
    dist_expect (m s)
      (\<lambda>r. case r of None \<Rightarrow> Q None | Some (x, s') \<Rightarrow> dist_expect (k x s') Q)"
proof -
  let ?dm = "dist \<circ> m"
  let ?dk = "map_fun id dist \<circ> k"
  let ?M = "dom (?dm s)"
  let ?K = "bind_cont_map ?dk"
  let ?D = "\<Union>i\<in>?M. dom (?K i)"
  let ?B = "map_bind ?dm ?K s"

  have fin_D: "finite ?D"
    by (auto simp: bind_cont_map_def delta_map_def split: option.splits prod.splits)

  have dom_B_subset: "dom ?B \<subseteq> ?D"
    by (auto simp: dom_map_bind)

  have "dist_expect (dist_bind m k s) Q =
    (\<Sum>x\<in>dom ?B. the (?B x) * Q x)"
    unfolding dist_expect_def dist_bind.rep_eq by simp
  also have "... = (\<Sum>x\<in>?D. option_default (?B x) * Q x)"
    using sum_option_default_mult_superset[OF fin_D dom_B_subset, of Q]
    by simp
  also have "... =
    (\<Sum>x\<in>?D.
      (\<Sum>i\<in>?M. the (dist (m s) i) * option_default (?K i x)) * Q x)"
    by (intro sum.cong refl) (simp add: option_default_map_bind)
  also have "... =
    (\<Sum>x\<in>?D. \<Sum>i\<in>?M.
      Q x * (the (dist (m s) i) * option_default (?K i x)))"
  proof (intro sum.cong refl)
    fix x
    assume "x \<in> ?D"
    have
      "(\<Sum>i\<in>?M. the (dist (m s) i) * option_default (?K i x)) * Q x =
        (\<Sum>i\<in>?M. (the (dist (m s) i) * option_default (?K i x)) * Q x)"
      by (simp add: sum_distrib_right)
    also have "... =
        (\<Sum>i\<in>?M. Q x * (the (dist (m s) i) * option_default (?K i x)))"
      by (intro sum.cong refl) (simp add: algebra_simps)
    finally show
      "(\<Sum>i\<in>?M. the (dist (m s) i) * option_default (?K i x)) * Q x =
        (\<Sum>i\<in>?M. Q x * (the (dist (m s) i) * option_default (?K i x)))" .
  qed
  also have "... =
    (\<Sum>i\<in>?M. \<Sum>x\<in>?D.
      Q x * (the (dist (m s) i) * option_default (?K i x)))"
    by (rule sum.swap)
  also have "... =
    (\<Sum>i\<in>?M.
      the (dist (m s) i) *
        (\<Sum>x\<in>?D. option_default (?K i x) * Q x))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "... =
    (\<Sum>i\<in>?M.
      the (dist (m s) i) *
        (\<Sum>x\<in>dom (?K i). the (?K i x) * Q x))"
  proof (intro sum.cong refl)
    fix i
    assume i: "i \<in> ?M"
    have "dom (?K i) \<subseteq> ?D"
      using i by auto
    then show
      "the (dist (m s) i) *
        (\<Sum>x\<in>?D. option_default (?K i x) * Q x) =
       the (dist (m s) i) *
        (\<Sum>x\<in>dom (?K i). the (?K i x) * Q x)"
      using sum_option_default_mult_superset[OF fin_D, of "?K i" Q]
      by simp
  qed
  also have "... =
    dist_expect (m s)
      (\<lambda>r. case r of None \<Rightarrow> Q None | Some (x, s') \<Rightarrow> dist_expect (k x s') Q)"
    unfolding dist_expect_def bind_cont_map_def
    apply (rule sum.cong)
     apply simp
    apply (rename_tac i)
    apply (case_tac i)
     apply (auto simp: case_prod_unfold dist_delta_dist delta_map_def split: prod.splits)
    done
  finally show ?thesis .
qed

definition wp :: "('a, 's) state_monad \<Rightarrow> (('a \<times> 's) option \<Rightarrow> prob) \<Rightarrow> 's \<Rightarrow> prob" where
  "wp m Q s =
    dist_expect (execute m s)
      (\<lambda>r. Q r)"

lemma wp_items:
  "wp m Q s =
    fsum (\<lambda>(r, p). p * Q r) (items (execute m s))"
  unfolding wp_def dist_expect_items
  by (simp add: case_prod_unfold)

definition wp_event :: "('a, 's) state_monad \<Rightarrow> (('a \<times> 's) option \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> prob" where
  "wp_event m P s = wp m (\<lambda>x. if P x then 1 else 0) s"

definition outcome_prob ::
  "('a, 's) state_monad \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> prob" where
  "outcome_prob m s x s' = option_default (dist (execute m s) (Some (x, s')))"

definition failure_prob :: "('a, 's) state_monad \<Rightarrow> 's \<Rightarrow> prob" where
  "failure_prob m s = option_default (dist (execute m s) None)"

definition success_prob :: "('a, 's) state_monad \<Rightarrow> 's \<Rightarrow> prob" where
  "success_prob m s = wp m (\<lambda>_. 1) s"

definition wp_error :: "('a, 's) state_monad \<Rightarrow> 's \<Rightarrow> prob" where
  "wp_error m s =
    wp m (\<lambda>r. case r of None \<Rightarrow> 1 | Some _ \<Rightarrow> 0) s"

definition wp_success :: "('a, 's) state_monad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> prob) \<Rightarrow> 's \<Rightarrow> prob" where
  "wp_success m Q s =
    wp m (\<lambda>r. case r of None \<Rightarrow> 0 | Some (x, s') \<Rightarrow> Q x s') s"

named_theorems wpsimps
named_theorems wp

lemma wp_return[wpsimps]:
  "wp (return x) Q s = Q (Some (x, s))"
  unfolding wp_def return.rep_eq dist_return_def
  by simp

lemma wp_bind[wpsimps]:
  "wp (m \<bind> k) Q s =
    wp m (\<lambda>r. case r of
      None \<Rightarrow> Q None
    | Some (x, s') \<Rightarrow> wp (k x) Q s') s"
  unfolding wp_def sm_bind.rep_eq
  apply (simp add: dist_expect_bind)
  apply (rule arg_cong[where f="\<lambda>F. dist_expect (execute m s) F"])
  by (rule ext) (auto split: option.splits prod.splits)

lemma wp_get[wpsimps]:
  "wp get Q s = Q (Some (s, s))"
  unfolding wp_def get.rep_eq dist_get_def by simp

lemma wp_put[wpsimps]:
  "wp (put s') Q s = Q (Some ((), s'))"
  unfolding wp_def put.rep_eq dist_put_def by simp

lemma wp_lift[wpsimps]:
  "wp (lift d) Q s = dist_expect (d s) (\<lambda>x. Q (Some (x, s)))"
  unfolding wp_def lift.rep_eq lift_dist_def
  by (simp add: dist_expect_map)

lemma wp_modify[wpsimps]:
  "wp (modify f) Q s = Q (Some ((), f s))"
  unfolding modify_def by (simp add: wpsimps)

lemma wp_throw[wpsimps]:
  "wp throw Q s = Q None"
  unfolding wp_def throw.rep_eq dist_throw_def by simp

lemma wp_create[wpsimps]:
  "wp (create f) Q s = dist_expect (f s) Q"
  unfolding wp_def execute_create by simp

lemma wp_die[wpsimps]:
  "wp (die n) Q s =
    dist_expect
      (dist_uniform (fset_of_list (map (\<lambda>x. Some (x, s)) [1..<Suc n]))) Q"
  unfolding die_def by (simp add: wpsimps)

lemma wp_coin[wpsimps]:
  "wp (coin p x y) Q s =
    dist_expect (dist_of_fset {|(Some (x, s), p), (Some (y, s), 1 - p)|}) Q"
  unfolding coin_def by (simp add: wpsimps)

lemma wp_returnI[wp]:
  assumes "P \<le> Q (Some (x, s))"
  shows "P \<le> wp (return x) Q s"
  using assms by (simp add:wpsimps)

lemma wp_bindI[wp]:
  assumes "P \<le> wp m (\<lambda>r. case r of
      None \<Rightarrow> Q None
    | Some (x, s') \<Rightarrow> wp (k x) Q s') s"
  shows "P \<le> wp (m \<bind> k) Q s"
  using assms by (simp add: wpsimps)

lemma wp_getI[wp]:
  assumes "P \<le> Q (Some (s, s))"
  shows "P \<le> wp get Q s"
  using assms by (simp add: wpsimps)

lemma wp_putI[wp]:
  assumes "P \<le> Q (Some ((), s'))"
  shows "P \<le> wp (put s') Q s"
  using assms by (simp add: wpsimps)

lemma wp_modifyI[wp]:
  assumes "P \<le> Q (Some ((), f s))"
  shows "P \<le> wp (modify f) Q s"
  using assms by (simp add: wpsimps)

lemma wp_liftI[wp]:
  assumes "P \<le> dist_expect (d s) (\<lambda>x. Q (Some (x, s)))"
  shows "P \<le> wp (lift d) Q s"
  using assms by (simp add: wpsimps)

lemma wp_throwI[wp]:
  assumes "P \<le> Q None"
  shows "P \<le> wp throw Q s"
  using assms by (simp add: wpsimps)

lemma wp_createI[wp]:
  assumes "P \<le> dist_expect (f s) Q"
  shows "P \<le> wp (create f) Q s"
  using assms by (simp add: wpsimps)

lemma wp_dieI[wp]:
  assumes "P \<le>
    dist_expect
      (dist_uniform (fset_of_list (map (\<lambda>x. Some (x, s)) [1..<Suc n]))) Q"
  shows "P \<le> wp (die n) Q s"
  using assms by (simp add: wpsimps)

lemma wp_coinI[wp]:
  assumes "P \<le> dist_expect (dist_of_fset {|(Some (x, s), p), (Some (y, s), 1 - p)|}) Q"
  shows "P \<le> wp (coin p x y) Q s"
  using assms by (simp add: wpsimps)

lemma wp_error_eq_failure_prob:
  "wp_error m s = failure_prob m s"
  unfolding wp_error_def wp_def failure_prob_def
  by (simp add: dist_expect_None)

lemma wp_error_return[wpsimps]:
  "wp_error (return x) s = 0"
  unfolding wp_error_def by (simp add: wpsimps)

lemma wp_error_bind[wpsimps]:
  "wp_error (m \<bind> k) s =
    wp m (\<lambda>r. case r of
      None \<Rightarrow> 1
    | Some (x, s') \<Rightarrow> wp_error (k x) s') s"
  unfolding wp_error_def
  apply (simp add: wpsimps)
  apply (rule arg_cong[where f="\<lambda>F. wp m F s"])
  by (rule ext) (auto split: option.splits prod.splits)

lemma wp_error_get[wpsimps]:
  "wp_error get s = 0"
  unfolding wp_error_def by (simp add: wpsimps)

lemma wp_error_put[wpsimps]:
  "wp_error (put s') s = 0"
  unfolding wp_error_def by (simp add: wpsimps)

lemma wp_error_modify[wpsimps]:
  "wp_error (modify f) s = 0"
  unfolding wp_error_def by (simp add: wpsimps)

lemma wp_error_lift[wpsimps]:
  "wp_error (lift d) s = 0"
  unfolding wp_error_def by (simp add: wpsimps)

lemma wp_error_throw[wpsimps]:
  "wp_error throw s = 1"
  unfolding wp_error_def by (simp add: wpsimps)

lemma wp_error_create[wpsimps]:
  "wp_error (create f) s = option_default (dist (f s) None)"
  by (simp add: wp_error_eq_failure_prob failure_prob_def execute_create)

lemma wp_error_coin[wpsimps]:
  "wp_error (coin p x y) s = 0"
proof -
  let ?A = "{|(Some (x, s), p), (Some (y, s), 1 - p)|}"
  have total: "fsum snd ?A \<noteq> 0"
    by (rule fsum_snd_coin_nonzero)
  have "None \<notin> dom (dist (dist_of_fset ?A))"
    using dom_dist_of_fset_subset[OF total]
    by auto
  then show ?thesis
    unfolding wp_error_def
    by (simp add: wpsimps dist_expect_None domIff)
qed

lemma wp_error_die_pos[wpsimps]:
  assumes "0 < n"
  shows "wp_error (die n) s = 0"
proof -
  let ?xs = "fset_of_list (map (\<lambda>x. Some (x, s)) [1..<Suc n])"
  have xs_nonempty: "?xs \<noteq> {||}"
    using assms by auto
  have none_xs: "None \<notin> fset ?xs"
    by (auto simp: fset_of_list.rep_eq)
  have supp: "dom (dist (dist_uniform ?xs)) \<subseteq> fset ?xs"
    by (rule dom_dist_uniform_subset[OF xs_nonempty])
  have "None \<notin> dom (dist (dist_uniform ?xs))"
    using supp none_xs by blast
  then show ?thesis
    unfolding wp_error_def
    by (simp add: wpsimps dist_expect_None domIff)
qed

lemma wp_success_return[wpsimps]:
  "wp_success (return x) Q s = Q x s"
  unfolding wp_success_def by (simp add: wpsimps)

lemma wp_success_bind[wpsimps]:
  "wp_success (m \<bind> k) Q s =
    wp_success m (\<lambda>x s'. wp_success (k x) Q s') s"
  unfolding wp_success_def
  apply (simp add: wpsimps)
  apply (rule arg_cong[where f="\<lambda>F. wp m F s"])
  by (rule ext) (auto split: option.splits prod.splits)

lemma wp_success_get[wpsimps]:
  "wp_success get Q s = Q s s"
  unfolding wp_success_def by (simp add: wpsimps)

lemma wp_success_put[wpsimps]:
  "wp_success (put s') Q s = Q () s'"
  unfolding wp_success_def by (simp add: wpsimps)

lemma wp_success_modify[wpsimps]:
  "wp_success (modify f) Q s = Q () (f s)"
  unfolding wp_success_def by (simp add: wpsimps)

lemma wp_success_lift[wpsimps]:
  "wp_success (lift d) Q s = dist_expect (d s) (\<lambda>x. Q x s)"
  unfolding wp_success_def by (simp add: wpsimps)

lemma wp_success_throw[wpsimps]:
  "wp_success throw Q s = 0"
  unfolding wp_success_def by (simp add: wpsimps)

lemma wp_error_return_check:
  "wp_error (return x) s = 0"
  by (simp add: wpsimps)

lemma wp_error_throw_check:
  "wp_error throw s = 1"
  by (simp add: wpsimps)

lemma wp_throw_error_post_check:
  "wp throw (\<lambda>r. case r of None \<Rightarrow> 1 | Some _ \<Rightarrow> 0) s = 1"
  by (simp add: wpsimps)

lemma wp_error_bind_check:
  "wp_error (m \<bind> k) s =
    wp m (\<lambda>r. case r of None \<Rightarrow> 1 | Some (x, s') \<Rightarrow> wp_error (k x) s') s"
  by (simp add: wpsimps)

lemma failure_prob_throw[simp]:
  "failure_prob throw s = 1"
  unfolding failure_prob_def throw.rep_eq dist_throw_def dist_delta_dist delta_map_def
  by simp

lemma failure_prob_return[simp]:
  "failure_prob (return x) s = 0"
  unfolding failure_prob_def return.rep_eq dist_return_def dist_delta_dist delta_map_def
  by simp

lemma success_prob_return[simp]:
  "success_prob (return x) s = 1"
  unfolding success_prob_def by (simp add: wpsimps)

lemma outcome_prob_notin_dom:
  assumes "Some (x, s') \<notin> dom (dist (execute m s))"
  shows "outcome_prob m s x s' = 0"
  using assms unfolding outcome_prob_def by (simp add: domIff)

lemma all_outcomes_above_thresholdI:
  assumes "\<And>x s'. outcome_prob m s x s' > t \<Longrightarrow> P x s'"
  shows "\<forall>x s'. outcome_prob m s x s' > t \<longrightarrow> P x s'"
  using assms by blast

lemma all_outcomes_above_threshold_domI:
  assumes
    "\<And>x s'. Some (x, s') \<in> dom (dist (execute m s)) \<Longrightarrow>
      outcome_prob m s x s' > t \<Longrightarrow> P x s'"
  shows "\<forall>x s'. outcome_prob m s x s' > t \<longrightarrow> P x s'"
proof (intro allI impI)
  fix x s'
  assume gt: "outcome_prob m s x s' > t"
  show "P x s'"
  proof (cases "Some (x, s') \<in> dom (dist (execute m s))")
    case True
    then show ?thesis
      using assms gt by blast
  next
    case False
    then have "outcome_prob m s x s' = 0"
      by (rule outcome_prob_notin_dom)
    then have False
      using gt zero_least[of t] by order
    then show ?thesis
      by simp
  qed
qed

subsubsection \<open>Examples\<close>

lemma return_outcomes_above_zero_example:
  "\<forall>y t. outcome_prob (return x) s y t > 0 \<longrightarrow> y = x \<and> t = s"
  unfolding outcome_prob_def return.rep_eq dist_return_def dist_delta_dist delta_map_def
  by (simp add: domIff)

lemma return_threshold_example:
  "\<forall>y t. outcome_prob (return x) s y t > 0 \<longrightarrow> y = x"
  using return_outcomes_above_zero_example[of x s] by blast

subsection \<open>Code generator\<close>

lemmas
  sm_bind_def[code]
  execute_create[code]

lemma sum_fset_by_bind_items_generic:
  "sum_fset_by x
      (\<lambda>(ms, ks). fst ks)
      (\<lambda>(ms, ks). snd ms * snd ks)
      (fbind (items d) (\<lambda>ms.
        fimage (\<lambda>ks. (ms, ks)) (items (k (fst ms))))) =
    (\<Sum>i\<in>dom (dist d).
      the (dist d i) * option_default (dist (k i) x))"
  unfolding sum_fset_by_def
  apply (simp add: fsum_ffilter_if fsum_fbind_fimage_Pair case_prod_unfold)
  unfolding fsum_items
  apply (intro sum.cong refl)
  apply (simp add: fsum_mult_left_nnreal fsum_items_key)
  by (simp add: dom_def option.case_eq_if)

lemma fsum_bind_items_total_generic:
  "fsum
      (\<lambda>(ms, ks). snd ms * snd ks)
      (fbind (items d) (\<lambda>ms.
        fimage (\<lambda>ks. (ms, ks)) (items (k (fst ms))))) = 1"
proof -
  have "fsum
      (\<lambda>(ms, ks). snd ms * snd ks)
      (fbind (items d) (\<lambda>ms.
        fimage (\<lambda>ks. (ms, ks)) (items (k (fst ms))))) =
    fsum
      (\<lambda>ms. fsum (\<lambda>ks. snd ms * snd ks) (items (k (fst ms))))
      (items d)"
    by (simp add: fsum_fbind_fimage_Pair case_prod_unfold)

  also have "... = fsum snd (items d)"
    by (intro fsum.cong refl) (simp add: fsum_items_mult_left)

  also have "... = 1"
    by simp

  finally show ?thesis .
qed

lemma dist_bind_code[code]:
  fixes m :: "'s \<Rightarrow> (('a \<times> 's) option) dist"
    and k :: "'a \<Rightarrow> 's \<Rightarrow> (('b \<times> 's) option) dist"
  shows
  "dist_bind m k s =
    dist_of_fset_by
      (\<lambda>(ms, ks). fst ks)
      (\<lambda>(ms, ks). snd ms * snd ks)
      (fbind (items (m s)) (\<lambda>ms.
        fimage (\<lambda>ks. (ms, ks))
          (items (case fst ms of None \<Rightarrow> delta_dist None | Some (x, s') \<Rightarrow> k x s'))))"
proof (rule dist_inject[THEN iffD1])
  let ?I =
    "fbind (items (m s)) (\<lambda>ms.
      fimage (\<lambda>ks. (ms, ks))
        (items (case fst ms of None \<Rightarrow> delta_dist None | Some (x, s') \<Rightarrow> k x s')))"
  let ?key = "\<lambda>(ms, ks). fst ks"
  let ?weight = "\<lambda>(ms, ks). snd ms * snd ks"
  let ?next =
    "(\<lambda>r :: ('a \<times> 's) option.
      case r of None \<Rightarrow> delta_dist (None :: ('b \<times> 's) option)
      | Some (x, s') \<Rightarrow> k x s')"

  have next_eq:
    "bind_cont_map (map_fun id dist \<circ> k) i = dist (?next i)" for i
    by (cases i) (auto simp: bind_cont_map_def dist_delta_dist o_def map_fun_def split: prod.splits)

  have next_eq_raw:
    "bind_cont_map (\<lambda>x xa. dist (k x xa)) i = dist (?next i)" for i
    by (cases i) (auto simp: bind_cont_map_def dist_delta_dist split: prod.splits)

  have total: "fsum ?weight ?I = 1"
    by (rule fsum_bind_items_total_generic)

  show "dist (dist_bind m k s) =
    dist (dist_of_fset_by ?key ?weight ?I)"
  proof
    fix x :: "('b \<times> 's) option"

    have by_sum:
      "sum_fset_by x ?key ?weight ?I =
        (\<Sum>i\<in>dom (dist (m s)).
          the (dist (m s) i) *
          option_default (dist (?next i) x))"
      by (rule sum_fset_by_bind_items_generic[of x "m s" ?next])

    have rhs:
      "dist (dist_of_fset_by ?key ?weight ?I) x =
        map_of_fset_by ?key ?weight ?I x"
      using dist_of_fset_by_rep_eq_1[OF total]
      by metis

    have "dist (dist_bind m k s) x =
      (let p =
        (\<Sum>i\<in>dom (dist (m s)).
          the (dist (m s) i) *
          option_default (dist (?next i) x))
       in if p = 0 then None else Some p)"
      unfolding dist_bind.rep_eq map_bind_def
      by (simp add: Let_def o_def map_fun_def next_eq next_eq_raw split: option.splits prod.splits)
    also have "... = map_of_fset_by ?key ?weight ?I x"
      using total by_sum
      unfolding map_of_fset_by_def
      by (simp add: Let_def)
    also have "... = dist (dist_of_fset_by ?key ?weight ?I) x"
      using rhs by simp
    finally show
      "dist (dist_bind m k s) x =
        dist (dist_of_fset_by ?key ?weight ?I) x" .

  qed
qed

subsubsection \<open>Some basic examples\<close>

fun mymap1::"bool \<Rightarrow> ((bool \<times> bool) option \<rightharpoonup> prob)"
where
  "mymap1 True = Map.map_of [(Some (True,True), 0.5),(Some (False,True), 0.5)]"
| "mymap1 False = Map.map_of [(Some (False,True), 0.5),(Some (False,False), 0.5)]"

fun mymap2::"(bool \<times> bool) option \<Rightarrow> ((bool \<times> bool) option \<rightharpoonup> prob)"
where
  "mymap2 None = delta_map None"
| "mymap2 (Some (True, True)) = Map.map_of [(Some (True,False), 0.5),(Some (False,False), 0.5)]"
| "mymap2 (Some (False, True)) = Map.map_of [(Some (False,False), 0.5),(Some (False,True), 0.5)]"
| "mymap2 (Some (True, False)) = Map.map_of [(Some (True,False), 0.5),(Some (False,False), 0.5)]"
| "mymap2 (Some (False, False)) = Map.map_of [(Some (False,False), 0.5),(Some (True,False), 0.5)]"

value "map (map_bind mymap1 mymap2 True) [Some (True,False),Some (False,False),Some (True,True),Some (False,True),None]"

value "(execute ((return 1)::(nat,nat) state_monad) 0)"

value "(execute (
        do {
        x \<leftarrow> return (1::nat);
        return (2::nat);
        return x
       } ::(nat,bool) state_monad) False)"

value "(execute (
        do {
        number \<leftarrow> die 6;
        if number = 6
          then coin 0.5 1 0
          else coin 0.1 1 0
       } ::(nat,bool) state_monad) False)"

value "execute (coin 0.5 True False) True"

value "wp_event (coin 0.5 True False) (\<lambda>a. \<exists>b. a = Some (True, b)) True"

value "execute (
        do {
        number \<leftarrow> coin 0.5 True False;
        if number
          then coin 0.2 True False
          else coin 0.7 True False
       }) False"

value "wp_event (
        do {
        number \<leftarrow> coin 0.5 True False;
        if number
          then coin 0.5 True False
          else coin 0.5 True False
       }) (\<lambda>a. \<exists>b. a = Some (b, False)) False"


end
