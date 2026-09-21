theory Soundness_FRI_Polynomial_Fold_Bounds
  imports Soundness_FRI_Padded_Degree
begin

context soundness
begin

lemma poly_of_list_even_odd_recompose:
  fixes xs :: "'f list"
  shows
    "poly_of_list xs =
      pcompose (poly_of_list (nths_pred xs even)) [:0, 0, 1:] +
        [:0, 1:] *
          pcompose (poly_of_list (nths_pred xs odd)) [:0, 0, 1:]"
proof (induction xs rule: measure_induct_rule[of length])
  case (less xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a ys)
    note xs_eq = Cons
    show ?thesis
    proof (cases ys)
      case Nil
      then show ?thesis
        unfolding xs_eq by (simp add: nths_Cons)
    next
      case (Cons b zs)
      note ys_eq = Cons
      have even_tail:
        "nths_pred (a # b # zs) even = a # nths_pred zs even"
        unfolding nths_pred_def by (simp add: nths_Cons)
      have odd_tail:
        "nths_pred (a # b # zs) odd = b # nths_pred zs odd"
        unfolding nths_pred_def by (simp add: nths_Cons)
      have zs_less: "length zs < length xs"
        unfolding xs_eq ys_eq by simp
      have IH:
        "poly_of_list zs =
          pcompose (poly_of_list (nths_pred zs even)) [:0, 0, 1:] +
            [:0, 1:] *
              pcompose (poly_of_list (nths_pred zs odd)) [:0, 0, 1:]"
        by (rule less.IH[OF zs_less])
      show ?thesis
        unfolding xs_eq ys_eq even_tail odd_tail
        using IH
        by (simp add: algebra_simps)
    qed
  qed
qed

lemma polynomial_even_odd_recompose:
  fixes p :: "'f poly"
  shows "p =
    pcompose (poly_of_list (nths_pred (coeffs p) even)) [:0, 0, 1:] +
      [:0, 1:] *
        pcompose (poly_of_list (nths_pred (coeffs p) odd)) [:0, 0, 1:]"
  using poly_of_list_even_odd_recompose[of "coeffs p"]
  by simp

lemma degree_from_even_odd_parts:
  fixes p :: "'f poly"
  assumes even_degree:
    "degree (poly_of_list (nths_pred (coeffs p) even)) \<le> k"
    and odd_degree:
    "degree (poly_of_list (nths_pred (coeffs p) odd)) \<le> k"
  shows "degree p \<le> 2 * k + 1"
proof -
  let ?E = "poly_of_list (nths_pred (coeffs p) even)"
  let ?O = "poly_of_list (nths_pred (coeffs p) odd)"
  let ?X2 = "[:0, 0, 1:] :: 'f poly"
  let ?X = "[:0, 1:] :: 'f poly"
  have even_comp: "degree (pcompose ?E ?X2) \<le> 2 * k"
  proof -
    have "degree (pcompose ?E ?X2) \<le> degree ?E * degree ?X2"
      by (rule degree_pcompose_le)
    also have "... \<le> 2 * k"
      using even_degree by simp
    finally show ?thesis .
  qed
  have odd_comp: "degree (?X * pcompose ?O ?X2) \<le> 2 * k + 1"
  proof -
    have "degree (?X * pcompose ?O ?X2) \<le>
        degree ?X + degree (pcompose ?O ?X2)"
      by (rule degree_mult_le)
    also have "... \<le> 2 * k + 1"
      using degree_pcompose_le[of ?O ?X2] odd_degree
      by simp
    finally show ?thesis .
  qed
  have sum_degree:
      "degree (pcompose ?E ?X2 + ?X * pcompose ?O ?X2) \<le>
        max (degree (pcompose ?E ?X2))
          (degree (?X * pcompose ?O ?X2))"
    by (rule degree_add_le_max)
  have p_eq:
      "p = pcompose ?E ?X2 + ?X * pcompose ?O ?X2"
    by (rule polynomial_even_odd_recompose)
  have "degree p \<le>
      max (degree (pcompose ?E ?X2))
        (degree (?X * pcompose ?O ?X2))"
    using p_eq sum_degree by simp
  also have "... \<le> 2 * k + 1"
    using even_comp odd_comp by simp
  finally show ?thesis .
qed

lemma two_low_symbolic_folds_imp_degree:
  fixes p :: "'f poly"
  assumes distinct: "b1 \<noteq> b2"
    and fold1: "degree (fri_symbolic_fold_polynomial p b1) \<le> k"
    and fold2: "degree (fri_symbolic_fold_polynomial p b2) \<le> k"
  shows "degree p \<le> 2 * k + 1"
proof -
  let ?E = "poly_of_list (nths_pred (coeffs p) even)"
  let ?O = "poly_of_list (nths_pred (coeffs p) odd)"
  have difference:
      "fri_symbolic_fold_polynomial p b1 -
          fri_symbolic_fold_polynomial p b2 =
        CP (b1 - b2) * ?O"
    unfolding fri_symbolic_fold_polynomial_def CP_def
    by (simp add: monom_0 smult_diff_left)
  have difference_degree:
      "degree (fri_symbolic_fold_polynomial p b1 -
          fri_symbolic_fold_polynomial p b2) \<le> k"
    by (rule degree_diff_le[OF fold1 fold2])
  have odd_degree: "degree ?O \<le> k"
  proof (cases "?O = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have coefficient_nonzero: "CP (b1 - b2) \<noteq> 0"
      using distinct unfolding CP_def
      by (simp add: monom_0)
    have product_degree:
        "degree (CP (b1 - b2) * ?O) = degree ?O"
      using degree_mult_eq[OF coefficient_nonzero False]
      unfolding CP_def
      by (simp add: monom_0)
    show ?thesis
      using difference difference_degree product_degree by simp
  qed
  have odd_product_degree: "degree (CP b1 * ?O) \<le> k"
  proof -
    have "degree (CP b1 * ?O) \<le> degree (CP b1) + degree ?O"
      by (rule degree_mult_le)
    also have "... \<le> k"
      using odd_degree unfolding CP_def by (simp add: monom_0)
    finally show ?thesis .
  qed
  have even_identity:
      "?E = fri_symbolic_fold_polynomial p b1 - CP b1 * ?O"
    unfolding fri_symbolic_fold_polynomial_def
    by simp
  have even_degree: "degree ?E \<le> k"
    unfolding even_identity
    by (rule degree_diff_le[OF fold1 odd_product_degree])
  show ?thesis
    by (rule degree_from_even_odd_parts[OF even_degree odd_degree])
qed

definition fri_low_fold_challenges
  :: "'f poly \<Rightarrow> nat \<Rightarrow> 'f set"
where
  "fri_low_fold_challenges p k =
    {b. degree (fri_symbolic_fold_polynomial p b) \<le> k}"

lemma card_fri_low_fold_challenges_le_one:
  assumes high: "degree p > 2 * k + 1"
  shows "card (fri_low_fold_challenges p k) \<le> 1"
proof -
  have finite_set: "finite (fri_low_fold_challenges p k)"
    by simp
  have unique:
    "\<forall>b1 \<in> fri_low_fold_challenges p k.
      \<forall>b2 \<in> fri_low_fold_challenges p k. b1 = b2"
  proof (intro ballI)
    fix b1 b2
    assume b1: "b1 \<in> fri_low_fold_challenges p k"
      and b2: "b2 \<in> fri_low_fold_challenges p k"
    show "b1 = b2"
    proof (rule ccontr)
      assume "b1 \<noteq> b2"
      have "degree p \<le> 2 * k + 1"
        by (rule two_low_symbolic_folds_imp_degree[OF \<open>b1 \<noteq> b2\<close>])
          (use b1 b2 in
            \<open>simp_all add: fri_low_fold_challenges_def\<close>)
      then show False
        using high by simp
    qed
  qed
  show ?thesis
    using card_le_Suc0_iff_eq[OF finite_set] unique by simp
qed

end
end
