(*  Title:      Stark/Completeness_Algebra.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Completeness_Algebra
  imports Completeness_Core
begin

section \<open>Algebraic Completeness Facts\<close>

text \<open>Deterministic polynomial and degree facts used by honest completeness.\<close>

context verification
begin

lemma degree_message_decodes:
  assumes "degree q \<le> p.maxDegree"
  shows "to_nat (of_nat (degree q)) = degree q"
  using assms by (simp add: p.maxDegree_def degrees_def p.to_nat_of_nat_bounded)

lemma degree_assert_hol:
  assumes "degree q \<le> p.maxDegree"
  shows "to_nat (of_nat (degree q)) \<le> p.maxDegree"
  using assms degree_message_decodes[OF assms] by simp

lemma root_factor_pCons:
  fixes r :: 'f
  shows "XP 1 - CP r = pCons (- r) 1"
proof -
  have xp: "XP (1::'f) = pCons 0 1"
    unfolding XP_def by (simp add: monom_0 monom_Suc)
  have cp: "CP r = pCons r 0"
    unfolding CP_def by (simp add: monom_0)
  show ?thesis
    unfolding xp cp
    by (simp only: diff_pCons pCons_eq_iff)
      (simp only: diff_conv_add_uminus add_0_left diff_0_right minus_zero add_0_right)
qed

lemma poly_root_factor:
  fixes r x :: 'f
  shows "poly (XP 1 - CP r) x = x - r"
  unfolding root_factor_pCons by (simp add: algebra_simps)

lemma root_factor_nonzero:
  fixes r :: 'f
  shows "XP 1 - CP r \<noteq> 0"
  unfolding root_factor_pCons by simp

lemma root_factor_degree:
  fixes r :: 'f
  shows "degree (XP 1 - CP r) = 1"
  unfolding root_factor_pCons by simp

lemma prod_fold_acc:
  fixes roots :: "'f list"
  shows "fold (\<lambda>s acc. (XP 1 - CP s) * acc) roots acc =
    fold (\<lambda>s acc. (XP 1 - CP s) * acc) roots (1 :: 'f poly) * acc"
proof (induction roots arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons r roots)
  let ?F = "\<lambda>s acc. (XP 1 - CP s) * acc"
  let ?fac = "XP 1 - CP r"
  have lhs:
    "fold ?F (r # roots) acc =
      fold ?F roots 1 * (?fac * acc)"
    using Cons.IH[of "?fac * acc"] by simp
  have "fold ?F (r # roots) acc =
      (fold ?F roots 1 * ?fac) * acc"
    using lhs by (simp only: mult.assoc)
  also have "... = fold ?F roots ?fac * acc"
    using Cons.IH[of ?fac, symmetric] by simp
  also have "... = fold ?F (r # roots) 1 * acc"
    by simp
  finally show ?case .
qed

lemma prod_Cons:
  fixes r :: 'f and roots :: "'f list"
  shows "prod (r # roots) = (XP 1 - CP r) * (prod roots :: 'f poly)"
proof -
  let ?F = "\<lambda>s acc. (XP 1 - CP s) * acc"
  have "prod (r # roots) = fold ?F roots ((XP 1 - CP r) * 1)"
    unfolding prod_def by simp
  also have "... = fold ?F roots 1 * ((XP 1 - CP r) * 1)"
    by (rule prod_fold_acc)
  also have "... = (prod roots :: 'f poly) * (XP 1 - CP r)"
    unfolding prod_def by simp
  also have "... = (XP 1 - CP r) * (prod roots :: 'f poly)"
    by (rule mult.commute)
  finally show ?thesis .
qed

lemma prod_roots_nonzero:
  fixes roots :: "'f list"
  shows "prod roots \<noteq> (0 :: 'f poly)"
proof (induction roots)
  case Nil
  then show ?case
    unfolding prod_def by simp
next
  case (Cons r roots)
  then show ?case
    unfolding prod_Cons
    using root_factor_nonzero[of r]
    by simp
qed

lemma degree_prod_roots:
  fixes roots :: "'f list"
  shows "degree (prod roots :: 'f poly) = length roots"
proof (induction roots)
  case Nil
  then show ?case
    unfolding prod_def by simp
next
  case (Cons r roots)
  have "degree (prod (r # roots) :: 'f poly) =
      degree ((XP 1 - CP r) * prod roots :: 'f poly)"
    unfolding prod_Cons by simp
  also have "... = degree (XP 1 - CP r :: 'f poly) + degree (prod roots :: 'f poly)"
    by (rule degree_mult_eq)
      (use root_factor_nonzero[of r] prod_roots_nonzero[of roots] in simp_all)
  also have "... = Suc (length roots)"
    using Cons.IH root_factor_degree[of r] by simp
  finally show ?case
    by simp
qed

lemma prod_roots_dvd:
  fixes roots :: "'f list"
  assumes vanish: "\<And>r. r \<in> set roots \<Longrightarrow> poly q r = 0"
    and distinct: "distinct roots"
  shows "prod roots dvd q"
  using assms
proof (induction roots arbitrary: q)
  case Nil
  then show ?case
    unfolding prod_def by simp
next
  case (Cons r roots)
  have r_root: "poly q r = 0"
    using Cons.prems(1) by simp
  have fac_dvd: "(XP 1 - CP r) dvd q"
  proof -
    have "pCons (- r) 1 dvd q"
    proof -
      have "[:- r, 1:] dvd q"
        using r_root by (simp add: poly_eq_0_iff_dvd)
      moreover have "[:- r, 1:] = pCons (- r) 1"
        by simp
      ultimately show ?thesis
        by simp
    qed
    then show ?thesis
      unfolding root_factor_pCons .
  qed
  then obtain q' where q_def: "q = (XP 1 - CP r) * q'"
    unfolding dvd_def by auto
  have roots_distinct: "distinct roots"
    using Cons.prems(2) by simp
  have vanish_q': "\<And>x. x \<in> set roots \<Longrightarrow> poly q' x = 0"
  proof -
    fix x
    assume x_in: "x \<in> set roots"
    have x_ne: "x \<noteq> r"
      using Cons.prems(2) x_in by auto
    have "0 = poly q x"
      using Cons.prems(1) x_in by simp
    also have "... = poly (XP 1 - CP r) x * poly q' x"
      unfolding q_def by simp
    finally have zero_eq: "0 = poly (XP 1 - CP r) x * poly q' x" .
    then have prod_zero: "poly (XP 1 - CP r) x * poly q' x = 0"
      by simp
    moreover have "poly (XP 1 - CP r) x \<noteq> 0"
    proof -
      have "poly (XP 1 - CP r) x = x - r"
        by (rule poly_root_factor)
      then show ?thesis
        using x_ne by simp
    qed
    ultimately show "poly q' x = 0"
      by (metis mult_eq_0_iff)
  qed
  have prod_tail_dvd: "prod roots dvd q'"
    by (rule Cons.IH[OF vanish_q' roots_distinct])
  then obtain k where q'_def: "q' = prod roots * k"
    unfolding dvd_def by auto
  have "q = ((XP 1 - CP r) * prod roots) * k"
    unfolding q_def q'_def by (simp add: mult.assoc)
  also have "... = prod (r # roots) * k"
    using prod_Cons[of r roots] by simp
  finally have "q = prod (r # roots) * k" .
  then show ?case
    unfolding dvd_def by blast
qed

lemma prod_eval_nonzero:
  fixes roots :: "'f list"
  assumes x_not_root: "x \<notin> set roots"
  shows "poly (prod roots :: 'f poly) x \<noteq> 0"
  using x_not_root
proof (induction roots)
  case Nil
  then show ?case
    unfolding prod_def by simp
next
  case (Cons r roots)
  have "x \<noteq> r"
    using Cons.prems by simp
  moreover have "poly (prod roots :: 'f poly) x \<noteq> 0"
    using Cons by simp
  ultimately show ?case
    unfolding prod_Cons
    using poly_root_factor[of r x] by simp
qed

lemma h_power_mod_domain:
  "p.h ^ (k mod (clength * scale)) = p.h ^ k"
  by (rule p.h_power_mod_domain)

lemma h_power_in_H:
  "p.h ^ k \<in> set p.H"
  by (rule p.h_power_in_H)

lemma eval_coset_disjoint_from_H:
  assumes idx_bound: "i < clength * scale"
  shows "p.h ^ i * shift \<notin> set p.H"
  by (rule p.eval_coset_disjoint_from_H[OF idx_bound])

lemma g_powers_in_H:
  assumes r_bound: "r < clength"
  shows "p.g ^ r \<in> set p.H"
  by (rule p.g_powers_in_H[OF r_bound])

lemma g_map_subset_H:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
  shows "set (p.g_map roots) \<subseteq> set p.H"
  by (rule p.g_map_subset_H[OF spec_entry])

lemma query_domain_disjoint:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
    and idx_bound: "i < clength * scale"
  shows "p.h ^ i * shift \<notin> set (p.g_map roots)"
  by (rule p.query_domain_disjoint[OF spec_entry idx_bound])

lemma honest_trace_algebra_prod_roots_dvd:
  assumes hta: "honest_trace_algebra"
    and spec_entry: "(c, roots, d) \<in> set spec"
  shows "prod (p.g_map roots) dvd c p.f_powers"
proof -
  have vanish:
    "\<And>r. r \<in> set (p.g_map roots) \<Longrightarrow> poly (c p.f_powers) r = 0"
    using hta spec_entry
    unfolding honest_trace_algebra_def constraint_roots_vanish_def
    by force
  have distinct: "distinct (p.g_map roots)"
    by (rule p.g_map_distinct[OF spec_entry])
  show ?thesis
    by (rule prod_roots_dvd[OF vanish distinct])
qed

lemma poly_div_eval_dvd:
  fixes q r :: "'f poly"
  assumes dvd: "r dvd q"
    and denom: "poly r x \<noteq> 0"
  shows "poly (q div r) x = poly q x div poly r x"
proof -
  have q_eq: "q div r * r = q"
    using dvd by simp
  then have "poly (q div r) x * poly r x = poly q x"
    by (metis poly_mult)
  then show ?thesis
    using denom by (simp add: field_simps)
qed

lemma honest_trace_algebra_quotient_eval:
  assumes hta: "honest_trace_algebra"
    and spec_entry: "(c, roots, d) \<in> set spec"
    and idx_bound: "idx < clength * scale"
  shows
    "poly ((c p.f_powers) div prod (p.g_map roots)) (p.h ^ idx * shift) =
      poly (c p.f_powers) (p.h ^ idx * shift) div
        poly (prod (p.g_map roots)) (p.h ^ idx * shift)"
proof -
  have dvd: "prod (p.g_map roots) dvd c p.f_powers"
    by (rule honest_trace_algebra_prod_roots_dvd[OF hta spec_entry])
  have denom: "poly (prod (p.g_map roots)) (p.h ^ idx * shift) \<noteq> 0"
    by (rule prod_eval_nonzero)
      (use query_domain_disjoint[OF spec_entry idx_bound] in simp)
  show ?thesis
    by (rule poly_div_eval_dvd[OF dvd denom])
qed

lemma degree_div_dvd_le:
  fixes q r :: "'f poly"
  assumes dvd: "r dvd q"
    and r_nonzero: "r \<noteq> 0"
  shows "degree (q div r) \<le> degree q - degree r"
proof (cases "q div r = 0")
  case True
  then show ?thesis by simp
next
  case False
  have q_eq: "q div r * r = q"
    using dvd by simp
  have "degree q = degree (q div r * r)"
    using q_eq by simp
  also have "... = degree (q div r) + degree r"
    by (rule degree_mult_eq[OF False r_nonzero])
  finally show ?thesis
    by simp
qed

lemma honest_trace_algebra_quotient_degree:
  assumes "honest_trace_algebra"
    and "(c, roots, d) \<in> set spec"
  shows
    "degree ((c p.f_powers) div (prod (p.g_map roots))) \<le>
      d * (clength - 1) - length roots"
proof -
  let ?q = "c p.f_powers"
  let ?roots = "p.g_map roots"
  have vanish: "\<And>r. r \<in> set ?roots \<Longrightarrow> poly ?q r = 0"
    using assms
    unfolding honest_trace_algebra_def constraint_roots_vanish_def
    by force
  have deg: "degree ?q \<le> d * (clength - 1)"
    by (rule constraint_degree_bound[OF assms(2)])
  have distinct: "distinct ?roots"
    by (rule p.g_map_distinct[OF assms(2)])
  have dvd: "prod ?roots dvd ?q"
    by (rule prod_roots_dvd[OF vanish distinct])
  have qdiv_le:
    "degree (?q div prod ?roots) \<le> degree ?q - degree (prod ?roots)"
    by (rule degree_div_dvd_le[OF dvd prod_roots_nonzero])
  have roots_len: "length ?roots = length roots"
    unfolding p.g_map_def by simp
  have prod_deg: "degree (prod ?roots) = length roots"
    using degree_prod_roots[of ?roots] roots_len by simp
  have "degree (?q div prod ?roots) \<le> degree ?q - length roots"
    using qdiv_le prod_deg by simp
  also have "... \<le> d * (clength - 1) - length roots"
    using deg by simp
  finally show ?thesis .
qed

lemma maxDegree_ge_spec:
  assumes "(c, roots, d) \<in> set spec"
  shows "d * (clength - 1) - length roots \<le> p.maxDegree"
proof -
  let ?S = "{d * (clength - 1) - length rs | a rs d. (a,rs,d) \<in> set spec}"
  have finite_S: "finite ?S"
  proof -
    have "?S = (\<lambda>(_, rs, d). d * (clength - 1) - length rs) ` set spec"
      by force
    then show ?thesis by simp
  qed
  have elem: "d * (clength - 1) - length roots \<in> ?S"
    using assms by force
  have "d * (clength - 1) - length roots \<le> Max (insert 0 ?S)"
    by (rule Max_ge) (use finite_S elem in auto)
  then show ?thesis
    unfolding p.maxDegree_def degrees_def .
qed

lemma composition_term_degree:
  assumes hta: "honest_trace_algebra"
    and spec_entry: "(c, roots, d) \<in> set spec"
  shows
    "degree (CP a * ((c p.f_powers) div (prod (p.g_map roots)))) \<le> p.maxDegree"
proof -
  have qdeg:
    "degree ((c p.f_powers) div (prod (p.g_map roots))) \<le>
      d * (clength - 1) - length roots"
    using hta spec_entry by (rule honest_trace_algebra_quotient_degree)
  have "degree (CP a * ((c p.f_powers) div (prod (p.g_map roots)))) \<le>
      degree (CP a) + degree ((c p.f_powers) div (prod (p.g_map roots)))"
    by (rule degree_mult_le)
  also have "... \<le> d * (clength - 1) - length roots"
    using qdeg unfolding CP_def by (simp add: monom_0)
  also have "... \<le> p.maxDegree"
    using spec_entry by (rule maxDegree_ge_spec)
  finally show ?thesis .
qed

lemma cp_fold_degree_aux:
  assumes terms:
    "\<And>a c roots d.
      (a, (c, roots, d)) \<in> set xs \<Longrightarrow>
      degree (CP a * ((c p.f_powers) div (prod (p.g_map roots)))) \<le> p.maxDegree"
    and acc: "degree acc \<le> p.maxDegree"
  shows
    "degree
      (fold
        (\<lambda>(a, (c, roots, _)).
          (+) (CP a * ((c p.f_powers) div (prod (p.g_map roots)))))
        xs acc) \<le> p.maxDegree"
  using terms acc
proof (induction xs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain a c roots d where x: "x = (a, (c, roots, d))"
    by (cases x) (auto split: prod.splits)
  have term_deg:
    "degree (CP a * ((c p.f_powers) div (prod (p.g_map roots)))) \<le> p.maxDegree"
    using Cons.prems(1)[of a c roots d] unfolding x by simp
  have acc':
    "degree
      ((\<lambda>(a, (c, roots, _)).
          (+) (CP a * ((c p.f_powers) div (prod (p.g_map roots)))))
        x acc) \<le> p.maxDegree"
    using term_deg Cons.prems(2)
    unfolding x
    by (auto intro: degree_add_le)
  show ?case
    using Cons.IH[OF _ acc'] Cons.prems(1)
    by auto
qed

lemma composition_degree_from_honest_trace_algebra:
  assumes "honest_trace_algebra"
  shows "degree (p.cp as p.f_powers) \<le> p.maxDegree"
  unfolding p.cp_def
proof (rule cp_fold_degree_aux)
  fix a c roots d
  assume "(a, (c, roots, d)) \<in> set (zip as spec)"
  then have spec_entry: "(c, roots, d) \<in> set spec"
    by (auto dest!: set_zip_rightD)
  show "degree (CP a * ((c p.f_powers) div (prod (p.g_map roots)))) \<le> p.maxDegree"
    by (rule composition_term_degree[OF assms spec_entry])
qed simp

lemma composition_degree_from_honest_trace_valid:
  assumes "honest_trace_valid"
  shows "degree (p.cp as p.f_powers) \<le> p.maxDegree"
  using assms
  unfolding honest_trace_valid_def
  by (intro composition_degree_from_honest_trace_algebra) simp

lemma honest_degree_message_assert_hol:
  assumes "honest_trace_valid"
  shows "to_nat (of_nat (degree (p.cp as p.f_powers))) \<le> p.maxDegree"
  by (rule degree_assert_hol[OF composition_degree_from_honest_trace_valid[OF assms]])

lemma honest_degree_message_rounds:
  assumes "honest_trace_valid"
  shows "ceil_log (to_nat (of_nat (degree (p.cp as p.f_powers))) + 1) =
    ceil_log (degree (p.cp as p.f_powers) + 1)"
  using degree_message_decodes[OF composition_degree_from_honest_trace_valid[OF assms]]
  by simp

end

end
