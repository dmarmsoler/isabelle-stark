theory Soundness_FRI_Robust_One_Round_Algebra
  imports Soundness_FRI_Robust_Incidence
begin

section \<open>FRI coefficient-pair hiding\<close>

context soundness
begin

lemma fri_fold_value_eq_of_coeff_pair_eq:
  assumes pair_eq:
    "fri_fold_coeff_pair xp xn denom =
      fri_fold_coeff_pair yp yn denom"
  shows
    "fri_fold_value b xp xn denom =
      fri_fold_value b yp yn denom"
proof -
  have first:
      "(xp + xn) div 2 = (yp + yn) div 2"
    using arg_cong[OF pair_eq, where f=fst]
    unfolding fri_fold_coeff_pair_def by simp
  have second:
      "(xp - xn) div denom = (yp - yn) div denom"
    using arg_cong[OF pair_eq, where f=snd]
    unfolding fri_fold_coeff_pair_def by simp
  have product:
      "b * ((xp - xn) div denom) =
        b * ((yp - yn) div denom)"
    by (rule arg_cong[OF second])
  show ?thesis
    unfolding fri_fold_value_def
    by (rule arg_cong2[OF first product])
qed

lemma fri_fold_coeff_pair_injective:
  assumes denom_nonzero: "denom \<noteq> 0"
    and pair_eq:
      "fri_fold_coeff_pair xp xn denom =
        fri_fold_coeff_pair yp yn denom"
  shows "xp = yp \<and> xn = yn"
proof -
  have first:
      "(xp + xn) div 2 = (yp + yn) div 2"
    using arg_cong[OF pair_eq, where f=fst]
    unfolding fri_fold_coeff_pair_def by simp
  have second:
      "(xp - xn) div denom = (yp - yn) div denom"
    using arg_cong[OF pair_eq, where f=snd]
    unfolding fri_fold_coeff_pair_def by simp
  have sum_or:
      "(2::'f) = 0 \<or> xp + xn = yp + yn"
    by (rule divide_cancel_right[THEN iffD1, OF first])
  have sum_eq: "xp + xn = yp + yn"
    using sum_or two_nonzero by blast
  have diff_or:
      "denom = 0 \<or> xp - xn = yp - yn"
    by (rule divide_cancel_right[THEN iffD1, OF second])
  have diff_eq: "xp - xn = yp - yn"
    using diff_or denom_nonzero by blast
  have xp_eq: "xp = yp"
  proof -
    have "2 * xp = (xp + xn) + (xp - xn)"
      by (simp add: algebra_simps)
    also have "... = (yp + yn) + (yp - yn)"
      using sum_eq diff_eq by simp
    also have "... = 2 * yp"
      by (simp add: algebra_simps)
    finally show ?thesis
      using two_nonzero by simp
  qed
  have xn_eq: "xn = yn"
    using sum_eq xp_eq by simp
  show ?thesis
    using xp_eq xn_eq by simp
qed

definition fri_coeff_pair_disagreement_indices ::
  "nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
where
  "fri_coeff_pair_disagreement_indices len fri_dom current claimed =
    {i. i < len div 2 \<and>
      fri_fold_coeff_pair
        (current ! i) (current ! fri_sibling_index len i)
        (fri_fold_denominator (fri_dom ! i) 1) \<noteq>
      fri_fold_coeff_pair
        (claimed ! i) (claimed ! fri_sibling_index len i)
        (fri_fold_denominator (fri_dom ! i) 1)}"

definition fri_folded_disagreement_indices ::
  "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
where
  "fri_folded_disagreement_indices b len fri_dom current claimed =
    {i. i < len div 2 \<and>
      fri_table_fold_value b current fri_dom len 1 i \<noteq>
      fri_table_fold_value b claimed fri_dom len 1 i}"

lemma finite_fri_coeff_pair_disagreement_indices:
  "finite (fri_coeff_pair_disagreement_indices
    len fri_dom current claimed)"
  unfolding fri_coeff_pair_disagreement_indices_def by simp

lemma finite_fri_folded_disagreement_indices:
  "finite (fri_folded_disagreement_indices
    b len fri_dom current claimed)"
  unfolding fri_folded_disagreement_indices_def by simp

lemma fri_folded_disagreement_indices_subset_pairs:
  "fri_folded_disagreement_indices b len fri_dom current claimed \<subseteq>
    fri_coeff_pair_disagreement_indices len fri_dom current claimed"
proof
  fix i
  assume folded:
      "i \<in> fri_folded_disagreement_indices
        b len fri_dom current claimed"
  then have i_bound: "i < len div 2"
    and value_diff:
      "fri_table_fold_value b current fri_dom len 1 i \<noteq>
        fri_table_fold_value b claimed fri_dom len 1 i"
    unfolding fri_folded_disagreement_indices_def by blast+
  have pair_diff:
      "fri_fold_coeff_pair
          (current ! i) (current ! fri_sibling_index len i)
          (fri_fold_denominator (fri_dom ! i) 1) \<noteq>
        fri_fold_coeff_pair
          (claimed ! i) (claimed ! fri_sibling_index len i)
          (fri_fold_denominator (fri_dom ! i) 1)"
  proof
    assume pair_eq:
      "fri_fold_coeff_pair
          (current ! i) (current ! fri_sibling_index len i)
          (fri_fold_denominator (fri_dom ! i) 1) =
        fri_fold_coeff_pair
          (claimed ! i) (claimed ! fri_sibling_index len i)
          (fri_fold_denominator (fri_dom ! i) 1)"
    have
      "fri_table_fold_value b current fri_dom len 1 i =
        fri_table_fold_value b claimed fri_dom len 1 i"
      unfolding fri_table_fold_value_def
      by (rule fri_fold_value_eq_of_coeff_pair_eq[OF pair_eq])
    then show False using value_diff by contradiction
  qed
  show
    "i \<in> fri_coeff_pair_disagreement_indices
      len fri_dom current claimed"
    unfolding fri_coeff_pair_disagreement_indices_def
    using i_bound pair_diff by simp
qed

lemma fri_pair_not_folded_disagreement_imp_hiding:
  assumes pair:
      "i \<in> fri_coeff_pair_disagreement_indices
        len fri_dom current claimed"
    and not_folded:
      "i \<notin> fri_folded_disagreement_indices
        b len fri_dom current claimed"
  shows
    "b \<in> fri_table_local_hiding_challenges
      current claimed fri_dom len 1 i"
proof -
  have i_bound: "i < len div 2"
    using pair unfolding fri_coeff_pair_disagreement_indices_def by simp
  have folded_eq:
      "fri_table_fold_value b current fri_dom len 1 i =
        fri_table_fold_value b claimed fri_dom len 1 i"
    using not_folded i_bound
    unfolding fri_folded_disagreement_indices_def by simp
  show ?thesis
    using folded_eq
    unfolding fri_table_local_hiding_challenges_def
      fri_local_hiding_challenges_def
      fri_table_fold_value_def
    by simp
qed

lemma fri_pair_hiding_indices_lower_bound:
  assumes folded_close:
      "card (fri_folded_disagreement_indices
        b len fri_dom current claimed) \<le> t"
  shows
    "card (fri_coeff_pair_disagreement_indices
        len fri_dom current claimed) - t \<le>
      card (hiding_indices
        (fri_coeff_pair_disagreement_indices
          len fri_dom current claimed)
        (\<lambda>i. fri_table_local_hiding_challenges
          current claimed fri_dom len 1 i)
        b)"
proof -
  let ?P =
    "fri_coeff_pair_disagreement_indices len fri_dom current claimed"
  let ?F =
    "fri_folded_disagreement_indices b len fri_dom current claimed"
  let ?H =
    "hiding_indices ?P
      (\<lambda>i. fri_table_local_hiding_challenges
        current claimed fri_dom len 1 i) b"
  have finite_P: "finite ?P"
    by (rule finite_fri_coeff_pair_disagreement_indices)
  have finite_F: "finite ?F"
    by (rule finite_fri_folded_disagreement_indices)
  have F_subset: "?F \<subseteq> ?P"
    by (rule fri_folded_disagreement_indices_subset_pairs)
  have diff_subset: "?P - ?F \<subseteq> ?H"
    unfolding hiding_indices_def
    using fri_pair_not_folded_disagreement_imp_hiding by blast
  have finite_H: "finite ?H"
    by (rule finite_subset[OF _ finite_P])
      (unfold hiding_indices_def, auto)
  have diff_card: "card (?P - ?F) = card ?P - card ?F"
    by (rule card_Diff_subset[OF finite_F F_subset])
  have radius_mono: "card ?P - t \<le> card ?P - card ?F"
    using folded_close by simp
  have lower_diff: "card ?P - t \<le> card (?P - ?F)"
    using radius_mono diff_card by simp
  have card_subset: "card (?P - ?F) \<le> card ?H"
    by (rule card_mono[OF finite_H diff_subset])
  show ?thesis
    using lower_diff card_subset by linarith
qed

lemma fri_raw_disagreements_le_twice_pair_disagreements:
  assumes len_pos: "0 < len"
    and even_len: "2 dvd len"
    and denominator_nonzero:
      "\<And>i. i < len div 2 \<Longrightarrow>
        fri_fold_denominator (fri_dom ! i) 1 \<noteq> 0"
  shows
    "card (code_disagreement_indices {..<len}
        (nth current) (nth claimed)) \<le>
      2 * card (fri_coeff_pair_disagreement_indices
        len fri_dom current claimed)"
proof -
  let ?P =
    "fri_coeff_pair_disagreement_indices len fri_dom current claimed"
  let ?E0 =
    "{i. i < len div 2 \<and> current ! i \<noteq> claimed ! i}"
  let ?E1 =
    "{i. i < len div 2 \<and>
      current ! fri_sibling_index len i \<noteq>
        claimed ! fri_sibling_index len i}"
  let ?R =
    "code_disagreement_indices {..<len} (nth current) (nth claimed)"
  have half_pos: "0 < len div 2"
    using len_pos even_len by (cases len) auto
  have finite_P: "finite ?P"
    by (rule finite_fri_coeff_pair_disagreement_indices)
  have finite_E0: "finite ?E0"
    by simp
  have finite_E1: "finite ?E1"
    by simp
  have E0_subset: "?E0 \<subseteq> ?P"
  proof
    fix i
    assume i_mem: "i \<in> ?E0"
    then have i_bound: "i < len div 2"
      and value_diff: "current ! i \<noteq> claimed ! i"
      by simp_all
    show "i \<in> ?P"
    proof (rule ccontr)
      assume "i \<notin> ?P"
      then have pair_eq:
          "fri_fold_coeff_pair
              (current ! i) (current ! fri_sibling_index len i)
              (fri_fold_denominator (fri_dom ! i) 1) =
            fri_fold_coeff_pair
              (claimed ! i) (claimed ! fri_sibling_index len i)
              (fri_fold_denominator (fri_dom ! i) 1)"
        using i_bound
        unfolding fri_coeff_pair_disagreement_indices_def by simp
      have pair_values: "current ! i = claimed ! i \<and>
            current ! fri_sibling_index len i =
              claimed ! fri_sibling_index len i"
        by (rule fri_fold_coeff_pair_injective[
              OF denominator_nonzero[OF i_bound] pair_eq])
      have value_eq: "current ! i = claimed ! i"
        using pair_values by blast
      show False
        using value_eq value_diff by contradiction
    qed
  qed
  have E1_subset: "?E1 \<subseteq> ?P"
  proof
    fix i
    assume i_mem: "i \<in> ?E1"
    then have i_bound: "i < len div 2"
      and value_diff:
        "current ! fri_sibling_index len i \<noteq>
          claimed ! fri_sibling_index len i"
      by simp_all
    show "i \<in> ?P"
    proof (rule ccontr)
      assume "i \<notin> ?P"
      then have pair_eq:
          "fri_fold_coeff_pair
              (current ! i) (current ! fri_sibling_index len i)
              (fri_fold_denominator (fri_dom ! i) 1) =
            fri_fold_coeff_pair
              (claimed ! i) (claimed ! fri_sibling_index len i)
              (fri_fold_denominator (fri_dom ! i) 1)"
        using i_bound
        unfolding fri_coeff_pair_disagreement_indices_def by simp
      have pair_values: "current ! i = claimed ! i \<and>
            current ! fri_sibling_index len i =
              claimed ! fri_sibling_index len i"
        by (rule fri_fold_coeff_pair_injective[
              OF denominator_nonzero[OF i_bound] pair_eq])
      have value_eq:
          "current ! fri_sibling_index len i =
            claimed ! fri_sibling_index len i"
        using pair_values by blast
      show False
        using value_eq value_diff by contradiction
    qed
  qed
  have raw_cover:
      "?R \<subseteq> ?E0 \<union> fri_sibling_index len ` ?E1"
  proof
    fix j
    assume j_mem: "j \<in> ?R"
    then have j_bound: "j < len"
      and value_diff: "current ! j \<noteq> claimed ! j"
      unfolding code_disagreement_indices_def by simp_all
    show "j \<in> ?E0 \<union> fri_sibling_index len ` ?E1"
    proof (cases "j < len div 2")
      case True
      then have "j \<in> ?E0"
        using value_diff by simp
      then show ?thesis by simp
    next
      case False
      let ?i = "j mod (len div 2)"
      have i_bound: "?i < len div 2"
        using half_pos by simp
      have sibling_eq:
          "j = fri_sibling_index len ?i"
        by (rule fri_sibling_index_mod_half_second_half[
              OF even_len j_bound False])
      have sibling_eq_sym:
          "fri_sibling_index len ?i = j"
        by (rule sym[OF sibling_eq])
      have value_diff_i:
          "current ! fri_sibling_index len ?i \<noteq>
            claimed ! fri_sibling_index len ?i"
        using value_diff sibling_eq_sym by simp
      have i_mem: "?i \<in> ?E1"
        using i_bound value_diff_i by simp
      have image_mem:
          "fri_sibling_index len ?i \<in>
            fri_sibling_index len ` ?E1"
        using i_mem by blast
      have "j \<in> fri_sibling_index len ` ?E1"
        using sibling_eq image_mem by simp
      then show ?thesis by simp
    qed
  qed
  have finite_cover:
      "finite (?E0 \<union> fri_sibling_index len ` ?E1)"
    using finite_E0 finite_E1 by simp
  have raw_card:
      "card ?R \<le> card (?E0 \<union> fri_sibling_index len ` ?E1)"
    by (rule card_mono[OF finite_cover raw_cover])
  have union_card:
      "card (?E0 \<union> fri_sibling_index len ` ?E1) \<le>
        card ?E0 + card (fri_sibling_index len ` ?E1)"
    by (rule card_Un_le)
  have image_card:
      "card (fri_sibling_index len ` ?E1) \<le> card ?E1"
    by (rule card_image_le[OF finite_E1])
  have E0_card: "card ?E0 \<le> card ?P"
    by (rule card_mono[OF finite_P E0_subset])
  have E1_card: "card ?E1 \<le> card ?P"
    by (rule card_mono[OF finite_P E1_subset])
  show ?thesis
    using raw_card union_card image_card E0_card E1_card by linarith
qed

lemma fri_pair_local_hiding_card_le_one:
  assumes pair:
      "i \<in> fri_coeff_pair_disagreement_indices
        len fri_dom current claimed"
  shows
    "card (fri_table_local_hiding_challenges
      current claimed fri_dom len 1 i) \<le> 1"
  by (rule fri_table_local_hiding_challenges_card_le_one)
    (use pair in
      \<open>simp add: fri_coeff_pair_disagreement_indices_def\<close>)

section \<open>Canonical polynomial representatives and two-fold reconstruction\<close>

definition fri_rs_code_polynomial ::
  "nat \<Rightarrow> 'f list \<Rightarrow> (nat \<Rightarrow> 'f) \<Rightarrow> 'f poly"
where
  "fri_rs_code_polynomial d fri_dom word =
    (SOME p. degree p \<le> d \<and>
      word = nth (map (poly p) fri_dom))"

lemma fri_rs_code_polynomial_spec:
  assumes word:
      "word \<in> fri_rs_code_functions d fri_dom"
  shows
    "degree (fri_rs_code_polynomial d fri_dom word) \<le> d \<and>
      word = nth (map
        (poly (fri_rs_code_polynomial d fri_dom word)) fri_dom)"
proof -
  obtain p where p_degree: "degree p \<le> d"
    and word_eq: "word = nth (map (poly p) fri_dom)"
    using word unfolding fri_rs_code_functions_def
      fri_rs_code_tables_def by auto
  show ?thesis
    unfolding fri_rs_code_polynomial_def
    by (rule someI2[where a=p]) (use p_degree word_eq in auto)
qed

lemma fri_rs_code_polynomial_degree:
  assumes "word \<in> fri_rs_code_functions d fri_dom"
  shows "degree (fri_rs_code_polynomial d fri_dom word) \<le> d"
  using fri_rs_code_polynomial_spec[OF assms] by blast

lemma fri_rs_code_polynomial_represents:
  assumes "word \<in> fri_rs_code_functions d fri_dom"
  shows
    "word = nth (map
      (poly (fri_rs_code_polynomial d fri_dom word)) fri_dom)"
  using fri_rs_code_polynomial_spec[OF assms] by blast

definition fri_two_fold_odd_part ::
  "'f \<Rightarrow> 'f \<Rightarrow> 'f poly \<Rightarrow> 'f poly \<Rightarrow> 'f poly"
where
  "fri_two_fold_odd_part b0 b q0 q =
    CP (inverse (b - b0)) * (q - q0)"

definition fri_two_fold_even_part ::
  "'f \<Rightarrow> 'f \<Rightarrow> 'f poly \<Rightarrow> 'f poly \<Rightarrow> 'f poly"
where
  "fri_two_fold_even_part b0 b q0 q =
    q0 - CP b0 * fri_two_fold_odd_part b0 b q0 q"

definition fri_two_fold_reconstruction ::
  "'f \<Rightarrow> 'f \<Rightarrow> 'f poly \<Rightarrow> 'f poly \<Rightarrow> 'f poly"
where
  "fri_two_fold_reconstruction b0 b q0 q =
    pcompose (fri_two_fold_even_part b0 b q0 q) [:0, 0, 1:] +
      [:0, 1:] *
        pcompose (fri_two_fold_odd_part b0 b q0 q) [:0, 0, 1:]"

lemma fri_two_fold_odd_part_degree:
  assumes q0_degree: "degree q0 \<le> k"
    and q_degree: "degree q \<le> k"
  shows "degree (fri_two_fold_odd_part b0 b q0 q) \<le> k"
proof -
  have diff_degree: "degree (q - q0) \<le> k"
    by (rule degree_diff_le[OF q_degree q0_degree])
  have product_degree:
      "degree (CP (inverse (b - b0)) * (q - q0)) \<le>
        degree (CP (inverse (b - b0))) + degree (q - q0)"
    by (rule degree_mult_le)
  show ?thesis
    unfolding fri_two_fold_odd_part_def
    using product_degree diff_degree
    by (simp add: CP_def monom_0)
qed

lemma fri_two_fold_even_part_degree:
  assumes q0_degree: "degree q0 \<le> k"
    and q_degree: "degree q \<le> k"
  shows "degree (fri_two_fold_even_part b0 b q0 q) \<le> k"
proof -
  have odd_degree:
      "degree (fri_two_fold_odd_part b0 b q0 q) \<le> k"
    by (rule fri_two_fold_odd_part_degree[OF q0_degree q_degree])
  have product_degree:
      "degree (CP b0 * fri_two_fold_odd_part b0 b q0 q) \<le> k"
  proof -
    have "degree (CP b0 * fri_two_fold_odd_part b0 b q0 q) \<le>
        degree (CP b0) +
          degree (fri_two_fold_odd_part b0 b q0 q)"
      by (rule degree_mult_le)
    also have "... \<le> k"
      using odd_degree by (simp add: CP_def monom_0)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding fri_two_fold_even_part_def
    by (rule degree_diff_le[OF q0_degree product_degree])
qed

lemma fri_two_fold_reconstruction_degree:
  assumes q0_degree: "degree q0 \<le> k"
    and q_degree: "degree q \<le> k"
  shows "degree (fri_two_fold_reconstruction b0 b q0 q) \<le> 2 * k + 1"
proof -
  let ?E = "fri_two_fold_even_part b0 b q0 q"
  let ?O = "fri_two_fold_odd_part b0 b q0 q"
  let ?X2 = "[:0, 0, 1:] :: 'f poly"
  let ?X = "[:0, 1:] :: 'f poly"
  have even_degree: "degree ?E \<le> k"
    by (rule fri_two_fold_even_part_degree[OF q0_degree q_degree])
  have odd_degree: "degree ?O \<le> k"
    by (rule fri_two_fold_odd_part_degree[OF q0_degree q_degree])
  have even_comp: "degree (pcompose ?E ?X2) \<le> 2 * k"
  proof -
    have "degree (pcompose ?E ?X2) \<le> degree ?E * degree ?X2"
      by (rule degree_pcompose_le)
    also have "... \<le> 2 * k"
      using even_degree by simp
    finally show ?thesis .
  qed
  have odd_comp:
      "degree (?X * pcompose ?O ?X2) \<le> 2 * k + 1"
  proof -
    have "degree (?X * pcompose ?O ?X2) \<le>
        degree ?X + degree (pcompose ?O ?X2)"
      by (rule degree_mult_le)
    also have "... \<le> 2 * k + 1"
      using degree_pcompose_le[of ?O ?X2] odd_degree by simp
    finally show ?thesis .
  qed
  have sum_degree:
      "degree (pcompose ?E ?X2 + ?X * pcompose ?O ?X2) \<le>
        max (degree (pcompose ?E ?X2))
          (degree (?X * pcompose ?O ?X2))"
    by (rule degree_add_le_max)
  show ?thesis
    unfolding fri_two_fold_reconstruction_def
    using sum_degree even_comp odd_comp by linarith
qed

lemma fri_two_fold_reconstruction_eval:
  "poly (fri_two_fold_reconstruction b0 b q0 q) z =
    poly (fri_two_fold_even_part b0 b q0 q) (z ^ 2) +
      z * poly (fri_two_fold_odd_part b0 b q0 q) (z ^ 2)"
  unfolding fri_two_fold_reconstruction_def
  by (simp add: poly_pcompose power2_eq_square)

lemma fri_two_fold_even_at_anchor:
  "poly (fri_two_fold_even_part b0 b q0 q) x +
      b0 * poly (fri_two_fold_odd_part b0 b q0 q) x =
    poly q0 x"
  unfolding fri_two_fold_even_part_def CP_def
  by (simp add: poly_monom)

lemma fri_two_fold_at_other:
  assumes distinct: "b \<noteq> b0"
  shows
    "poly (fri_two_fold_even_part b0 b q0 q) x +
        b * poly (fri_two_fold_odd_part b0 b q0 q) x =
      poly q x"
proof -
  have difference_nonzero: "b - b0 \<noteq> 0"
    using distinct by simp
  have odd_eval:
      "poly (fri_two_fold_odd_part b0 b q0 q) x =
        inverse (b - b0) * (poly q x - poly q0 x)"
    unfolding fri_two_fold_odd_part_def CP_def
    by (simp add: poly_monom)
  have even_eval:
      "poly (fri_two_fold_even_part b0 b q0 q) x =
        poly q0 x -
          b0 * poly (fri_two_fold_odd_part b0 b q0 q) x"
  proof -
    show ?thesis
      unfolding fri_two_fold_even_part_def CP_def
      by (simp add: poly_monom)
  qed
  have first:
      "poly (fri_two_fold_even_part b0 b q0 q) x +
          b * poly (fri_two_fold_odd_part b0 b q0 q) x =
        poly q0 x +
          (b - b0) * poly (fri_two_fold_odd_part b0 b q0 q) x"
    using even_eval by (simp add: algebra_simps)
  have second:
      "poly q0 x +
          (b - b0) * poly (fri_two_fold_odd_part b0 b q0 q) x =
        poly q0 x +
          (b - b0) *
            (inverse (b - b0) * (poly q x - poly q0 x))"
    using odd_eval by simp
  have associate:
      "(b - b0) *
          (inverse (b - b0) * (poly q x - poly q0 x)) =
        ((b - b0) * inverse (b - b0)) *
          (poly q x - poly q0 x)"
    by (simp only: mult.assoc[symmetric])
  have cancel: "(b - b0) * inverse (b - b0) = 1"
    using difference_nonzero by simp
  have scaled:
      "(b - b0) *
          (inverse (b - b0) * (poly q x - poly q0 x)) =
        poly q x - poly q0 x"
    using associate cancel by simp
  have shifted:
      "poly q0 x +
          (b - b0) *
            (inverse (b - b0) * (poly q x - poly q0 x)) =
        poly q0 x + (poly q x - poly q0 x)"
    by (rule arg_cong[OF scaled])
  have third:
      "poly q0 x +
          (b - b0) *
            (inverse (b - b0) * (poly q x - poly q0 x)) =
        poly q x"
    using shifted by simp
  show ?thesis
    using first second third by simp
qed

lemma fri_fold_value_even_odd:
  fixes ev od z b :: 'f
  assumes z_nonzero: "z \<noteq> 0"
  shows
    "fri_fold_value b (ev + z * od) (ev - z * od)
        (fri_fold_denominator z 1) = ev + b * od"
  unfolding fri_fold_value_def fri_fold_denominator_def
  using z_nonzero two_nonzero
  by (simp add: field_simps)

lemma fri_two_fold_reconstruction_fold_anchor:
  assumes z_nonzero: "z \<noteq> 0"
  shows
    "fri_fold_value b0
        (poly (fri_two_fold_reconstruction b0 b q0 q) z)
        (poly (fri_two_fold_reconstruction b0 b q0 q) (-z))
        (fri_fold_denominator z 1) =
      poly q0 (z ^ 2)"
proof -
  let ?p = "fri_two_fold_reconstruction b0 b q0 q"
  let ?E = "fri_two_fold_even_part b0 b q0 q"
  let ?O = "fri_two_fold_odd_part b0 b q0 q"
  have pos: "poly ?p z = poly ?E (z ^ 2) + z * poly ?O (z ^ 2)"
    by (rule fri_two_fold_reconstruction_eval)
  have neg: "poly ?p (-z) = poly ?E (z ^ 2) - z * poly ?O (z ^ 2)"
    using fri_two_fold_reconstruction_eval[of b0 b q0 q "-z"]
    by (simp add: power2_eq_square)
  have inputs:
      "fri_fold_value b0 (poly ?p z) (poly ?p (-z))
          (fri_fold_denominator z 1) =
        fri_fold_value b0
          (poly ?E (z ^ 2) + z * poly ?O (z ^ 2))
          (poly ?E (z ^ 2) - z * poly ?O (z ^ 2))
          (fri_fold_denominator z 1)"
    using pos neg by simp
  have normalized:
      "fri_fold_value b0
          (poly ?E (z ^ 2) + z * poly ?O (z ^ 2))
          (poly ?E (z ^ 2) - z * poly ?O (z ^ 2))
          (fri_fold_denominator z 1) =
        poly ?E (z ^ 2) + b0 * poly ?O (z ^ 2)"
    by (rule fri_fold_value_even_odd[OF z_nonzero])
  have target:
      "poly ?E (z ^ 2) + b0 * poly ?O (z ^ 2) =
        poly q0 (z ^ 2)"
    by (rule fri_two_fold_even_at_anchor)
  show ?thesis
    using inputs normalized target by simp
qed

lemma fri_two_fold_reconstruction_fold_other:
  assumes distinct: "b \<noteq> b0"
    and z_nonzero: "z \<noteq> 0"
  shows
    "fri_fold_value b
        (poly (fri_two_fold_reconstruction b0 b q0 q) z)
        (poly (fri_two_fold_reconstruction b0 b q0 q) (-z))
        (fri_fold_denominator z 1) =
      poly q (z ^ 2)"
proof -
  let ?p = "fri_two_fold_reconstruction b0 b q0 q"
  let ?E = "fri_two_fold_even_part b0 b q0 q"
  let ?O = "fri_two_fold_odd_part b0 b q0 q"
  have pos: "poly ?p z = poly ?E (z ^ 2) + z * poly ?O (z ^ 2)"
    by (rule fri_two_fold_reconstruction_eval)
  have neg: "poly ?p (-z) = poly ?E (z ^ 2) - z * poly ?O (z ^ 2)"
    using fri_two_fold_reconstruction_eval[of b0 b q0 q "-z"]
    by (simp add: power2_eq_square)
  have inputs:
      "fri_fold_value b (poly ?p z) (poly ?p (-z))
          (fri_fold_denominator z 1) =
        fri_fold_value b
          (poly ?E (z ^ 2) + z * poly ?O (z ^ 2))
          (poly ?E (z ^ 2) - z * poly ?O (z ^ 2))
          (fri_fold_denominator z 1)"
    using pos neg by simp
  have normalized:
      "fri_fold_value b
          (poly ?E (z ^ 2) + z * poly ?O (z ^ 2))
          (poly ?E (z ^ 2) - z * poly ?O (z ^ 2))
          (fri_fold_denominator z 1) =
        poly ?E (z ^ 2) + b * poly ?O (z ^ 2)"
    by (rule fri_fold_value_even_odd[OF z_nonzero])
  have target:
      "poly ?E (z ^ 2) + b * poly ?O (z ^ 2) =
        poly q (z ^ 2)"
    by (rule fri_two_fold_at_other[OF distinct])
  show ?thesis
    using inputs normalized target by simp
qed

lemma fri_two_challenge_fold_values_injective:
  assumes challenges_distinct: "b \<noteq> b0"
    and denominator_nonzero: "denom \<noteq> 0"
    and anchor_eq:
      "fri_fold_value b0 xp xn denom =
        fri_fold_value b0 yp yn denom"
    and other_eq:
      "fri_fold_value b xp xn denom =
        fri_fold_value b yp yn denom"
  shows "xp = yp \<and> xn = yn"
proof -
  let ?px = "fri_fold_coeff_pair xp xn denom"
  let ?py = "fri_fold_coeff_pair yp yn denom"
  have anchor_linear:
      "fst ?px + b0 * snd ?px = fst ?py + b0 * snd ?py"
    using anchor_eq
    unfolding fri_fold_value_def fri_fold_coeff_pair_def by simp
  have other_linear:
      "fst ?px + b * snd ?px = fst ?py + b * snd ?py"
    using other_eq
    unfolding fri_fold_value_def fri_fold_coeff_pair_def by simp
  have anchor_delta:
      "fst ?px - fst ?py = b0 * (snd ?py - snd ?px)"
    using anchor_linear by (simp add: algebra_simps)
  have other_delta:
      "fst ?px - fst ?py = b * (snd ?py - snd ?px)"
    using other_linear by (simp add: algebra_simps)
  have scaled_equal:
      "b0 * (snd ?py - snd ?px) =
        b * (snd ?py - snd ?px)"
    by (rule trans[OF sym[OF anchor_delta] other_delta])
  have product_zero:
      "(b - b0) * (snd ?px - snd ?py) = 0"
    using scaled_equal by (simp add: algebra_simps)
  have challenge_difference_nonzero: "b - b0 \<noteq> 0"
    using challenges_distinct by simp
  have second_eq: "snd ?px = snd ?py"
  proof -
    have "snd ?px - snd ?py = 0"
      using product_zero challenge_difference_nonzero by simp
    then show ?thesis by simp
  qed
  have first_eq: "fst ?px = fst ?py"
    using anchor_linear second_eq by simp
  have pair_eq: "?px = ?py"
    by (rule prod_eqI[OF first_eq second_eq])
  show ?thesis
    by (rule fri_fold_coeff_pair_injective[
          OF denominator_nonzero pair_eq])
qed

end

end
