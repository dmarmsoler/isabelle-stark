(*  Title:      Stark/Soundness_Core_WP.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Core_WP
  imports Soundness_Core_Base
begin

text \<open>Generic probability and WP combinators used by soundness reductions.\<close>

context soundness
begin

lemma wp_event_union_bound:
  fixes P Q :: "('x \<times> 's) option \<Rightarrow> bool"
  shows
    "wp_event m (\<lambda>out. P out \<or> Q out) s \<le>
      wp_event m P s + wp_event m Q s"
proof -
  have pointwise:
    "\<And>out p. p * (if P out \<or> Q out then 1 else 0) \<le>
      p * ((if P out then 1 else 0) + (if Q out then 1 else 0) :: prob)"
    by (simp add: mult_left_mono)
  have "wp_event m (\<lambda>out. P out \<or> Q out) s \<le>
      wp m (\<lambda>out. (if P out then 1 else 0) + (if Q out then 1 else 0)) s"
    unfolding wp_event_def wp_def dist_expect_def
    by (intro sum_mono pointwise)
  also have "... = wp_event m P s + wp_event m Q s"
    unfolding wp_event_def wp_def dist_expect_def
    by (simp add: algebra_simps sum.distrib)
  finally show ?thesis .
qed

lemma wp_event_union_bound4:
  fixes A B C D :: "('x \<times> 's) option \<Rightarrow> bool"
  shows
    "wp_event m (\<lambda>out. A out \<or> B out \<or> C out \<or> D out) s \<le>
      wp_event m A s + wp_event m B s + wp_event m C s + wp_event m D s"
proof -
  have pointwise:
    "\<And>out p. p * (if A out \<or> B out \<or> C out \<or> D out then 1 else 0) \<le>
      p * ((if A out then 1 else 0) + (if B out then 1 else 0) +
        (if C out then 1 else 0) + (if D out then 1 else 0) :: prob)"
    by (simp add: mult_left_mono)
  have "wp_event m (\<lambda>out. A out \<or> B out \<or> C out \<or> D out) s \<le>
      wp m (\<lambda>out.
        (if A out then 1 else 0) + (if B out then 1 else 0) +
        (if C out then 1 else 0) + (if D out then 1 else 0)) s"
    unfolding wp_event_def wp_def dist_expect_def
    by (intro sum_mono pointwise)
  also have "... =
      wp_event m A s + wp_event m B s + wp_event m C s + wp_event m D s"
    unfolding wp_event_def wp_def dist_expect_def
    by (simp add: algebra_simps sum.distrib)
  finally show ?thesis
    .
qed

lemma wp_event_finite_UN_bound:
  fixes P :: "'a \<Rightarrow> ('x \<times> 's) option \<Rightarrow> bool"
    and C :: "'a \<Rightarrow> prob"
  assumes finite_A: "finite A"
    and bounds: "\<And>a. a \<in> A \<Longrightarrow> wp_event m (P a) s \<le> C a"
  shows
    "wp_event m (\<lambda>out. \<exists>a \<in> A. P a out) s \<le> (\<Sum>a\<in>A. C a)"
proof -
  have pointwise:
    "\<And>out p. p * (if \<exists>a \<in> A. P a out then 1 else 0) \<le>
      p * (\<Sum>a\<in>A. if P a out then 1 else 0 :: prob)"
  proof -
    fix out p
    have indicator_le:
      "(if \<exists>a \<in> A. P a out then 1 else 0 :: prob) \<le>
        (\<Sum>a\<in>A. if P a out then 1 else 0)"
    proof (cases "\<exists>a \<in> A. P a out")
      case True
      then obtain a where a: "a \<in> A" "P a out"
        by blast
      have "1 = (if P a out then 1 else 0 :: prob)"
        using a by simp
      also have "... \<le> (\<Sum>a\<in>A. if P a out then 1 else 0)"
        by (rule member_le_sum) (use a finite_A in simp_all)
      finally show ?thesis
        using True by simp
    next
      case False
      then show ?thesis by simp
    qed
    show "p * (if \<exists>a \<in> A. P a out then 1 else 0) \<le>
        p * (\<Sum>a\<in>A. if P a out then 1 else 0 :: prob)"
      by (simp add: mult_left_mono[OF indicator_le])
  qed
  have "wp_event m (\<lambda>out. \<exists>a \<in> A. P a out) s \<le>
      wp m (\<lambda>out. (\<Sum>a\<in>A. if P a out then 1 else 0)) s"
    unfolding wp_event_def wp_def dist_expect_def
    by (intro sum_mono pointwise)
  also have "... = (\<Sum>a\<in>A. wp_event m (P a) s)"
    using finite_A
  proof (induction A)
    case empty
    then show ?case
      unfolding wp_event_def wp_def dist_expect_def by simp
  next
    case (insert a A)
    have "wp m (\<lambda>out. \<Sum>x\<in>insert a A. if P x out then 1 else 0) s =
        wp m (\<lambda>out.
          (if P a out then 1 else 0) +
          (\<Sum>x\<in>A. if P x out then 1 else 0)) s"
      using insert.hyps by simp
    also have "... =
        wp_event m (P a) s +
        wp m (\<lambda>out. \<Sum>x\<in>A. if P x out then 1 else 0) s"
      unfolding wp_event_def wp_def dist_expect_def
      by (simp add: sum.distrib algebra_simps)
    also have "... = wp_event m (P a) s + (\<Sum>x\<in>A. wp_event m (P x) s)"
      using insert.IH by simp
    also have "... = (\<Sum>x\<in>insert a A. wp_event m (P x) s)"
      using insert.hyps by simp
    finally show ?case .
  qed
  also have "... \<le> (\<Sum>a\<in>A. C a)"
    by (rule sum_mono) (rule bounds, assumption)
  finally show ?thesis .
qed

lemma wp_event_mono:
  fixes P Q :: "('x \<times> 's) option \<Rightarrow> bool"
  assumes "\<And>out. P out \<Longrightarrow> Q out"
  shows "wp_event m P s \<le> wp_event m Q s"
proof -
  have pointwise:
    "\<And>out p. p * (if P out then 1 else 0) \<le>
      p * (if Q out then 1 else 0 :: prob)"
    using assms by (simp add: mult_left_mono)
  show ?thesis
    unfolding wp_event_def wp_def dist_expect_def
    by (intro sum_mono pointwise)
qed

lemma wp_event_le_1:
  fixes P :: "('x \<times> 's) option \<Rightarrow> bool"
  shows "wp_event m P s \<le> 1"
proof -
  have pointwise:
    "\<And>out p. p * (if P out then 1 else 0 :: prob) \<le> p"
    by (simp add: mult_left_le)
  have "wp_event m P s \<le>
      (\<Sum>out\<in>dom (dist (execute m s)).
        the (dist (execute m s) out))"
    unfolding wp_event_def wp_def dist_expect_def
    by (intro sum_mono pointwise)
  also have "... = 1"
    unfolding sum_map_def[symmetric] by simp
  finally show ?thesis .
qed

lemma wp_le_const_on_support:
  assumes "\<And>out. out \<in> set_dist (execute m s) \<Longrightarrow> Q out \<le> C"
  shows "wp m Q s \<le> C"
proof -
  have pointwise:
    "\<And>out p. out \<in> dom (dist (execute m s)) \<Longrightarrow>
      p * Q out \<le> p * C"
    using assms unfolding set_dist_def by (simp add: mult_left_mono)
  have "wp m Q s \<le>
      (\<Sum>out\<in>dom (dist (execute m s)).
        the (dist (execute m s) out) * C)"
    unfolding wp_def dist_expect_def
    by (intro sum_mono pointwise)
  also have "... =
      (\<Sum>out\<in>dom (dist (execute m s)).
        the (dist (execute m s) out)) * C"
    by (simp add: sum_distrib_right)
  also have "... = C"
    unfolding sum_map_def[symmetric] by simp
  finally show ?thesis .
qed

lemma wp_mono_on_support:
  assumes "\<And>out. out \<in> set_dist (execute m s) \<Longrightarrow> Q out \<le> R out"
  shows "wp m Q s \<le> wp m R s"
proof -
  have pointwise:
    "\<And>out p. out \<in> dom (dist (execute m s)) \<Longrightarrow>
      p * Q out \<le> p * R out"
    using assms unfolding set_dist_def by (simp add: mult_left_mono)
  show ?thesis
    unfolding wp_def dist_expect_def
    by (intro sum_mono pointwise) simp
qed

lemma wp_event_mono_on_support:
  fixes P Q :: "('x \<times> 's) option \<Rightarrow> bool"
  assumes "\<And>out. out \<in> set_dist (execute m s) \<Longrightarrow> P out \<Longrightarrow> Q out"
  shows "wp_event m P s \<le> wp_event m Q s"
proof -
  have pointwise:
    "\<And>out p. out \<in> dom (dist (execute m s)) \<Longrightarrow>
      p * (if P out then 1 else 0) \<le>
      p * (if Q out then 1 else 0 :: prob)"
    using assms unfolding set_dist_def by (simp add: mult_left_mono)
  show ?thesis
    unfolding wp_event_def wp_def dist_expect_def
    by (intro sum_mono pointwise) simp
qed

lemma wp_event_pos_of_support:
  assumes out: "out \<in> set_dist (execute m s)"
    and event: "P out"
  shows "0 < wp_event m P s"
proof -
  let ?D = "dom (dist (execute m s))"
  have out_dom: "out \<in> ?D"
    using out unfolding set_dist_def .
  have out_weight_pos: "0 < the (dist (execute m s) out)"
    using dist_nonzero_on_dom[OF out_dom] by simp
  have "0 < (\<Sum>x\<in>?D.
      the (dist (execute m s) x) * (if P x then 1 else 0 :: prob))"
  proof (rule sum_pos2)
    show "finite ?D"
      by simp
    show "out \<in> ?D"
      by (rule out_dom)
    show "0 < the (dist (execute m s) out) *
        (if P out then 1 else 0 :: prob)"
      using event out_weight_pos by simp
  qed simp
  then show ?thesis
    unfolding wp_event_def wp_def dist_expect_def .
qed

lemma wp_event_pos_imp_exists_support:
  assumes "0 < wp_event m P s"
  obtains out where "out \<in> set_dist (execute m s)" and "P out"
proof -
  have "\<exists>out \<in> set_dist (execute m s). P out"
  proof (rule ccontr)
    assume "\<not> (\<exists>out \<in> set_dist (execute m s). P out)"
    then have no_event:
      "\<And>out. out \<in> dom (dist (execute m s)) \<Longrightarrow> \<not> P out"
      unfolding set_dist_def by blast
    have "wp_event m P s = 0"
      unfolding wp_event_def wp_def dist_expect_def
      by (intro sum.neutral) (simp add: no_event)
    then show False
      using assms by simp
  qed
  then show ?thesis
    using that by blast
qed

lemma wp_event_bind_bound_by_head_event:
  fixes m :: "('x, 's) state_monad"
    and k :: "'x \<Rightarrow> ('y, 's) state_monad"
  assumes m_bound: "wp_event m P s \<le> C"
    and none_imp: "Q None \<Longrightarrow> P None"
    and cont_imp:
      "\<And>x t out. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        out \<in> set_dist (execute (k x) t) \<Longrightarrow>
        Q out \<Longrightarrow> P (Some (x, t))"
  shows "wp_event (m \<bind> k) Q s \<le> C"
proof -
  have bind_eq:
    "wp_event (m \<bind> k) Q s =
      wp m (\<lambda>out. case out of
          None \<Rightarrow> if Q None then 1 else 0
        | Some (x, t) \<Rightarrow> wp_event (k x) Q t) s"
    unfolding wp_event_def by (simp add: wpsimps)
  have bind_head:
    "wp_event (m \<bind> k) Q s \<le> wp_event m P s"
  proof -
    have "wp_event (m \<bind> k) Q s =
        wp m (\<lambda>out. case out of
            None \<Rightarrow> if Q None then 1 else 0
          | Some (x, t) \<Rightarrow> wp_event (k x) Q t) s"
      by (rule bind_eq)
    also have "... \<le> wp_event m P s"
      unfolding wp_event_def
    proof (rule wp_mono_on_support)
      fix out
      assume out: "out \<in> set_dist (execute m s)"
      show
        "(case out of None \<Rightarrow> if Q None then 1 else 0
          | Some (x, t) \<Rightarrow>
              wp (k x) (\<lambda>out. if Q out then 1 else 0) t)
         \<le> (if P out then 1 else 0)"
      proof (cases out)
        case None
        then show ?thesis
          using none_imp by (cases "Q None") simp_all
      next
        case (Some xt)
        then obtain x t where xt: "xt = (x, t)"
          by (cases xt) auto
        have out_eq: "out = Some (x, t)"
          using Some xt by simp
        have head_out: "Some (x, t) \<in> set_dist (execute m s)"
          using out out_eq by simp
        have wp_bound:
          "wp (k x) (\<lambda>out. if Q out then 1 else 0) t \<le>
            (if P (Some (x, t)) then 1 else 0 :: prob)"
        proof (rule wp_le_const_on_support)
          fix out'
          assume out': "out' \<in> set_dist (execute (k x) t)"
          show "(if Q out' then 1 else 0) \<le>
              (if P (Some (x, t)) then 1 else 0 :: prob)"
          proof (cases "Q out'")
            case True
            then have "P (Some (x, t))"
              by (rule cont_imp[OF head_out out'])
            then show ?thesis
              using True by simp
          next
            case False
            then show ?thesis by simp
          qed
        qed
        show ?thesis
          using wp_bound out_eq by simp
      qed
    qed
    finally show ?thesis .
  qed
  show ?thesis
    by (rule order_trans[OF bind_head m_bound])
qed

lemma wp_event_bind_cong_cont:
  fixes m :: "('x, 's) state_monad"
    and k :: "'x \<Rightarrow> ('y, 's) state_monad"
    and l :: "'x \<Rightarrow> ('z, 's) state_monad"
  assumes none: "Q None = R None"
    and cont:
      "\<And>x t. wp_event (k x) Q t = wp_event (l x) R t"
  shows "wp_event (m \<bind> k) Q s = wp_event (m \<bind> l) R s"
proof -
  have left:
    "wp_event (m \<bind> k) Q s =
      wp m (\<lambda>out. case out of
          None \<Rightarrow> if Q None then 1 else 0
        | Some (x, t) \<Rightarrow> wp_event (k x) Q t) s"
    unfolding wp_event_def by (simp add: wpsimps)
  have right:
    "wp_event (m \<bind> l) R s =
      wp m (\<lambda>out. case out of
          None \<Rightarrow> if R None then 1 else 0
        | Some (x, t) \<Rightarrow> wp_event (l x) R t) s"
    unfolding wp_event_def by (simp add: wpsimps)
  have fun_eq:
    "(\<lambda>out. case out of
        None \<Rightarrow> if Q None then 1 else 0
      | Some (x, t) \<Rightarrow> wp_event (k x) Q t) =
     (\<lambda>out. case out of
        None \<Rightarrow> if R None then 1 else 0
      | Some (x, t) \<Rightarrow> wp_event (l x) R t)"
    by (rule ext) (simp add: none cont split: option.splits prod.splits)
  show ?thesis
    unfolding left right
    by (simp add: fun_eq)
qed

lemma wp_event_bind_bound_by_head_and_cont:
  fixes m :: "('x, 's) state_monad"
    and k :: "'x \<Rightarrow> ('y, 's) state_monad"
  assumes none: "\<not> Q None"
    and cont_zero:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        \<not> P (Some (x, t)) \<Longrightarrow> wp_event (k x) Q t = 0"
    and cont_bound:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        P (Some (x, t)) \<Longrightarrow> wp_event (k x) Q t \<le> D"
  shows "wp_event (m \<bind> k) Q s \<le> wp_event m P s * D"
proof -
  have bind_eq:
    "wp_event (m \<bind> k) Q s =
      wp m (\<lambda>out. case out of
          None \<Rightarrow> if Q None then 1 else 0
        | Some (x, t) \<Rightarrow> wp_event (k x) Q t) s"
    unfolding wp_event_def by (simp add: wpsimps)
  have "wp_event (m \<bind> k) Q s \<le>
      wp m (\<lambda>out. (if P out then 1 else 0) * D) s"
    unfolding bind_eq
  proof (rule wp_mono_on_support)
    fix out
    assume out: "out \<in> set_dist (execute m s)"
    show "(case out of None \<Rightarrow> if Q None then 1 else 0
          | Some (x, t) \<Rightarrow> wp_event (k x) Q t)
        \<le> (if P out then 1 else 0) * D"
    proof (cases out)
      case None
      then show ?thesis
        using none by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) auto
      have head: "Some (x, t) \<in> set_dist (execute m s)"
        using out Some xt by simp
      show ?thesis
      proof (cases "P (Some (x, t))")
        case True
        then show ?thesis
          using cont_bound[OF head True] Some xt by simp
      next
        case False
        then show ?thesis
          using cont_zero[OF head False] Some xt by simp
      qed
    qed
  qed
  also have "... = D * wp_event m P s"
    unfolding wp_event_def wp_def dist_expect_def
    by (simp add: sum_distrib_left algebra_simps)
  also have "... = wp_event m P s * D"
    by (simp add: mult.commute)
  finally show ?thesis .
qed

lemma wp_event_bind_bound_by_cont:
  fixes m :: "('x, 's) state_monad"
    and k :: "'x \<Rightarrow> ('y, 's) state_monad"
  assumes none: "\<not> Q None"
    and cont_bound:
      "\<And>x t. Some (x, t) \<in> set_dist (execute m s) \<Longrightarrow>
        wp_event (k x) Q t \<le> C"
  shows "wp_event (m \<bind> k) Q s \<le> C"
proof -
  have "wp_event (m \<bind> k) Q s =
      wp m (\<lambda>out. case out of
          None \<Rightarrow> if Q None then 1 else 0
        | Some (x, t) \<Rightarrow> wp_event (k x) Q t) s"
    unfolding wp_event_def by (simp add: wpsimps)
  also have "... \<le> C"
  proof (rule wp_le_const_on_support)
    fix out
    assume out: "out \<in> set_dist (execute m s)"
    show "(case out of None \<Rightarrow> if Q None then 1 else 0
          | Some (x, t) \<Rightarrow> wp_event (k x) Q t) \<le> C"
    proof (cases out)
      case None
      then show ?thesis
        using none by simp
    next
      case (Some xt)
      then obtain x t where xt: "xt = (x, t)"
        by (cases xt) auto
      show ?thesis
        using cont_bound[of x t] out Some xt by simp
    qed
  qed
  finally show ?thesis .
qed

lemma sm_bind_return_map:
  "((m \<bind> (\<lambda>x. return (f x))) \<bind> k) = (m \<bind> (\<lambda>x. k (f x)))"
  by (simp add: sm_bind_assoc)

lemma wp_bind_return_map:
  fixes m :: "('x, 's) state_monad"
  shows
    "wp (m \<bind> (\<lambda>x. return (f x))) Q s =
      wp m (\<lambda>out. case out of None \<Rightarrow> Q None
        | Some (x, t) \<Rightarrow> Q (Some (f x, t))) s"
proof -
  have cont:
    "(\<lambda>r. case r of None \<Rightarrow> Q None
      | Some (x, t) \<Rightarrow> wp (return (f x)) Q t) =
     (\<lambda>out. case out of None \<Rightarrow> Q None
      | Some (x, t) \<Rightarrow> Q (Some (f x, t)))"
    by (rule ext) (simp add: wp_return split: option.splits prod.splits)
  show ?thesis
    by (subst wp_bind) (simp add: cont)
qed

lemma wp_event_bind_return_map:
  fixes m :: "('x, 's) state_monad"
  shows
    "wp_event (m \<bind> (\<lambda>x. return (f x))) P s =
      wp_event m (\<lambda>out. case out of None \<Rightarrow> P None
        | Some (x, t) \<Rightarrow> P (Some (f x, t))) s"
proof -
  have indicator_eq:
    "(\<lambda>out. case out of None \<Rightarrow> if P None then 1 else 0
      | Some (x, t) \<Rightarrow> if P (Some (f x, t)) then 1 else 0) =
     (\<lambda>out. if (case out of None \<Rightarrow> P None
      | Some (x, t) \<Rightarrow> P (Some (f x, t))) then 1 else 0)"
    by (rule ext) (simp split: option.splits prod.splits)
  show ?thesis
    unfolding wp_event_def
    by (simp add: wp_bind_return_map indicator_eq)
qed

lemma set_dist_bindI:
  fixes m :: "('x, 's) state_monad"
    and k :: "'x \<Rightarrow> ('y, 's) state_monad"
  assumes head: "Some (x, t) \<in> set_dist (execute m s)"
    and tail: "out \<in> set_dist (execute (k x) t)"
  shows "out \<in> set_dist (execute (m \<bind> k) s)"
proof -
  let ?M = "dist (execute m s)"
  let ?K = "\<lambda>r. bind_cont_map (\<lambda>x t. dist (execute (k x) t)) r"
  let ?h = "Some (x, t)"
  have head_dom: "?h \<in> dom ?M"
    using head unfolding set_dist_def .
  have tail_dom: "out \<in> dom (?K ?h)"
    using tail unfolding set_dist_def bind_cont_map_def by simp
  have tail_dist_dom: "out \<in> dom (dist (execute (k x) t))"
    using tail unfolding set_dist_def .
  have head_pos: "0 < the (?M ?h)"
    using dist_nonzero_on_dom[OF head_dom] by simp
  have tail_dist_pos: "0 < the (dist (execute (k x) t) out)"
    using dist_nonzero_on_dom[OF tail_dist_dom] by simp
  obtain p where p_eq: "dist (execute (k x) t) out = Some p"
    using tail_dist_dom by auto
  have p_pos: "0 < p"
    using tail_dist_pos p_eq by simp
  have tail_pos: "0 < option_default (?K ?h out)"
    using p_eq p_pos by (simp add: bind_cont_map_def)
  have term_pos:
    "0 < the (?M ?h) * option_default (?K ?h out)"
    using head_pos tail_pos by simp
  have sum_pos:
    "0 < (\<Sum>r\<in>dom ?M. the (?M r) * option_default (?K r out))"
  proof (rule sum_pos2)
    show "finite (dom ?M)"
      by simp
    show "?h \<in> dom ?M"
      by (rule head_dom)
    show "0 < the (?M ?h) * option_default (?K ?h out)"
      by (rule term_pos)
  qed simp
  let ?p = "(\<Sum>r\<in>dom ?M. the (?M r) * option_default (?K r out))"
  have p_nonzero: "?p \<noteq> 0"
    using sum_pos by simp
  have dist_eq: "dist (execute (m \<bind> k) s) out = Some ?p"
    unfolding sm_bind.rep_eq dist_bind.rep_eq map_bind_def
    by (simp add: Let_def o_def map_fun_def p_nonzero)
  then show ?thesis
    unfolding set_dist_def by auto
qed

end

end
