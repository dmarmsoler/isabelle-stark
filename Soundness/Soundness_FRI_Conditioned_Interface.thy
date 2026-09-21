theory Soundness_FRI_Conditioned_Interface
  imports
    Soundness_FRI_Polynomial_Fold_Bounds
    Polynomial_Interpolation.Lagrange_Interpolation
begin

context soundness
begin

lemma degree_poly_of_list_less_length_soundness:
  assumes "xs \<noteq> []"
  shows "degree (poly_of_list xs) < length xs"
proof -
  have "degree (poly_of_list xs) = length (coeffs (poly_of_list xs)) - 1"
    by (simp add: degree_eq_length_coeffs)
  also have "... \<le> length xs - 1"
  proof -
    have "length (coeffs (poly_of_list xs)) \<le> length xs"
      by (simp add: length_strip_while_le)
    with assms show ?thesis by linarith
  qed
  also have "... < length xs"
    using assms by simp
  finally show ?thesis .
qed

lemma degree_nths_even_coeffs_le_half_soundness:
  "degree (poly_of_list (nths_pred (coeffs q) even)) \<le> degree q div 2"
proof (cases "coeffs q = []")
  case True
  then show ?thesis by simp
next
  case False
  let ?xs = "nths_pred (coeffs q) even"
  have len: "length ?xs = Suc (length (coeffs q)) div 2"
    by (rule nths_pred_even_length_eq)
  show ?thesis
  proof (cases "?xs = []")
    case True
    then show ?thesis by simp
  next
    case xs_ne: False
    have dlt: "degree (poly_of_list ?xs) < length ?xs"
      using xs_ne by (rule degree_poly_of_list_less_length_soundness)
    have "degree (poly_of_list ?xs) < Suc (length (coeffs q)) div 2"
      using dlt len by simp
    then have "degree (poly_of_list ?xs) \<le> (length (coeffs q) - 1) div 2"
      by linarith
    then show ?thesis
      by (simp add: degree_eq_length_coeffs)
  qed
qed

lemma degree_nths_odd_coeffs_le_half_soundness:
  "degree (poly_of_list (nths_pred (coeffs q) odd)) \<le> degree q div 2"
proof (cases "coeffs q = []")
  case True
  then show ?thesis by simp
next
  case False
  let ?xs = "nths_pred (coeffs q) odd"
  have len: "length ?xs = length (coeffs q) div 2"
    by (rule nths_pred_odd_length_eq)
  show ?thesis
  proof (cases "?xs = []")
    case True
    then show ?thesis by simp
  next
    case xs_ne: False
    have dlt: "degree (poly_of_list ?xs) < length ?xs"
      using xs_ne by (rule degree_poly_of_list_less_length_soundness)
    then have "degree (poly_of_list ?xs) < Suc (length (coeffs q)) div 2"
      using len by linarith
    then have "degree (poly_of_list ?xs) \<le> (length (coeffs q) - 1) div 2"
      by linarith
    then show ?thesis
      by (simp add: degree_eq_length_coeffs)
  qed
qed

lemma fri_symbolic_fold_degree_le_half:
  "degree (fri_symbolic_fold_polynomial q b) \<le> degree q div 2"
proof -
  define odd_coefficients where
    "odd_coefficients = nths_pred (coeffs q) odd"
  define even_coefficients where
    "even_coefficients = nths_pred (coeffs q) even"
  define oddp where "oddp = CP b * poly_of_list odd_coefficients"
  define evenp where "evenp = poly_of_list even_coefficients"
  have odd_le: "degree oddp \<le> degree q div 2"
  proof -
    have "degree oddp \<le> degree (CP b) + degree (poly_of_list odd_coefficients)"
      unfolding oddp_def by (rule degree_mult_le)
    also have "... \<le> degree q div 2"
      unfolding CP_def odd_coefficients_def
      using degree_nths_odd_coeffs_le_half_soundness[of q]
      by (simp add: monom_0)
    finally show ?thesis .
  qed
  have even_le: "degree evenp \<le> degree q div 2"
    unfolding evenp_def even_coefficients_def
    by (rule degree_nths_even_coeffs_le_half_soundness)
  have "degree (fri_symbolic_fold_polynomial q b) = degree (oddp + evenp)"
    unfolding fri_symbolic_fold_polynomial_def oddp_def evenp_def
      odd_coefficients_def even_coefficients_def
    by simp
  also have "... \<le> degree q div 2"
    using odd_le even_le by (rule degree_add_le)
  finally show ?thesis .
qed

lemma poly_of_list_even_odd_decompose_soundness:
  fixes xs :: "'f list"
    and x :: 'f
  shows
    "poly (poly_of_list xs) x =
      poly (poly_of_list (nths_pred xs even)) (x * x) +
        x * poly (poly_of_list (nths_pred xs odd)) (x * x)"
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
      have poly_tail:
        "poly (poly_of_list zs) x =
          poly (poly_of_list (nths_pred zs even)) (x * x) +
            x * poly (poly_of_list (nths_pred zs odd)) (x * x)"
        by (rule less.IH[OF zs_less])
      show ?thesis
        unfolding xs_eq ys_eq even_tail odd_tail
        using poly_tail
        by (simp add: algebra_simps power2_eq_square)
    qed
  qed
qed

lemma poly_even_part_reconstruct_soundness:
  fixes q :: "'f poly"
    and x :: 'f
  shows
    "poly (poly_of_list (nths_pred (coeffs q) even)) (x * x) =
      (poly q x + poly q (-x)) div 2"
proof -
  have decomp_x:
    "poly q x =
      poly (poly_of_list (nths_pred (coeffs q) even)) (x * x) +
        x * poly (poly_of_list (nths_pred (coeffs q) odd)) (x * x)"
    using poly_of_list_even_odd_decompose_soundness[of "coeffs q" x]
    by simp
  have decomp_neg:
    "poly q (-x) =
      poly (poly_of_list (nths_pred (coeffs q) even)) (x * x) -
        x * poly (poly_of_list (nths_pred (coeffs q) odd)) (x * x)"
    using poly_of_list_even_odd_decompose_soundness[of "coeffs q" "-x"]
    by (simp add: algebra_simps power2_eq_square)
  show ?thesis
    using decomp_x decomp_neg two_nonzero
    by (simp add: field_simps)
qed

lemma poly_odd_part_reconstruct_soundness:
  fixes q :: "'f poly"
    and x :: 'f
  assumes x_nonzero: "x \<noteq> 0"
  shows
    "poly (poly_of_list (nths_pred (coeffs q) odd)) (x * x) =
      (poly q x - poly q (-x)) div (2 * x)"
proof -
  have decomp_x:
    "poly q x =
      poly (poly_of_list (nths_pred (coeffs q) even)) (x * x) +
        x * poly (poly_of_list (nths_pred (coeffs q) odd)) (x * x)"
    using poly_of_list_even_odd_decompose_soundness[of "coeffs q" x]
    by simp
  have decomp_neg:
    "poly q (-x) =
      poly (poly_of_list (nths_pred (coeffs q) even)) (x * x) -
        x * poly (poly_of_list (nths_pred (coeffs q) odd)) (x * x)"
    using poly_of_list_even_odd_decompose_soundness[of "coeffs q" "-x"]
    by (simp add: algebra_simps power2_eq_square)
  show ?thesis
    using decomp_x decomp_neg two_nonzero x_nonzero
    by (simp add: field_simps)
qed

lemma fri_symbolic_fold_polynomial_eval:
  fixes q :: "'f poly"
    and b z :: 'f
  assumes z_nonzero: "z \<noteq> 0"
  shows
    "((poly q z + poly q (-z)) div 2 +
        b * ((poly q z - poly q (-z)) div (2 * z))) =
      poly (fri_symbolic_fold_polynomial q b) (z * z)"
proof -
  let ?E = "poly (poly_of_list (nths_pred (coeffs q) even)) (z * z)"
  let ?O = "poly (poly_of_list (nths_pred (coeffs q) odd)) (z * z)"
  have even:
    "?E = (poly q z + poly q (-z)) div 2"
    by (rule poly_even_part_reconstruct_soundness)
  have odd:
    "?O = (poly q z - poly q (-z)) div (2 * z)"
    by (rule poly_odd_part_reconstruct_soundness[OF z_nonzero])
  have next_poly_eval:
    "poly (fri_symbolic_fold_polynomial q b) (z * z) = b * ?O + ?E"
    unfolding fri_symbolic_fold_polynomial_def CP_def
    by (simp add: monom_0 algebra_simps)
  have lhs:
    "((poly q z + poly q (-z)) div 2 +
        b * ((poly q z - poly q (-z)) div (2 * z))) =
      ?E + b * ?O"
    using even odd by simp
  also have "... = poly (fri_symbolic_fold_polynomial q b) (z * z)"
    using next_poly_eval by (simp add: algebra_simps)
  finally show ?thesis .
qed

definition fri_table_interpolant
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f poly"
where
  "fri_table_interpolant fri_dom table =
    lagrange_interpolation_poly (zip fri_dom table)"

lemma degree_fri_table_interpolant_le:
  "degree (fri_table_interpolant fri_dom table) \<le>
    min (length fri_dom) (length table) - 1"
  unfolding fri_table_interpolant_def
  using degree_lagrange_interpolation_poly[of "zip fri_dom table"]
  by simp

lemma fri_table_interpolant_reproduces:
  assumes distinct_dom: "distinct fri_dom"
    and lengths: "length table = length fri_dom"
  shows
    "map (poly (fri_table_interpolant fri_dom table)) fri_dom = table"
proof (rule nth_equalityI)
  show
    "length (map (poly (fri_table_interpolant fri_dom table)) fri_dom) =
      length table"
    using lengths by simp
next
  fix i
  assume i_bound:
    "i < length
      (map (poly (fri_table_interpolant fri_dom table)) fri_dom)"
  have zip_mem: "zip fri_dom table ! i \<in> set (zip fri_dom table)"
    by (rule nth_mem) (use i_bound lengths in simp)
  have zip_nth:
      "zip fri_dom table ! i = (fri_dom ! i, table ! i)"
    using i_bound lengths by simp
  have pair_mem: "(fri_dom ! i, table ! i) \<in> set (zip fri_dom table)"
    using zip_mem zip_nth by simp
  have distinct_fst: "distinct (map fst (zip fri_dom table))"
    using distinct_dom lengths by simp
  have eval:
    "poly (fri_table_interpolant fri_dom table) (fri_dom ! i) = table ! i"
    unfolding fri_table_interpolant_def
    by (rule lagrange_interpolation_poly[OF distinct_fst refl pair_mem])
  show
    "map (poly (fri_table_interpolant fri_dom table)) fri_dom ! i =
      table ! i"
    using i_bound eval by simp
qed

lemma fri_table_interpolant_low_degree_iff:
  assumes distinct_dom: "distinct fri_dom"
    and lengths: "length table = length fri_dom"
  shows
    "fri_table_low_degree_on d fri_dom table \<longleftrightarrow>
      degree (fri_table_interpolant fri_dom table) \<le> d"
proof
  assume low: "fri_table_low_degree_on d fri_dom table"
  then obtain p where p_degree: "degree p \<le> d"
    and table: "table = map (poly p) fri_dom"
    unfolding fri_table_low_degree_on_def by blast
  have interpolant_reproduces:
    "map (poly (fri_table_interpolant fri_dom table)) fri_dom = table"
    by (rule fri_table_interpolant_reproduces[OF distinct_dom lengths])
  have p_reproduces: "map (poly p) fri_dom = table"
    using table by simp
  show "degree (fri_table_interpolant fri_dom table) \<le> d"
  proof (cases "length fri_dom - 1 \<le> d")
    case True
    show ?thesis
      using degree_fri_table_interpolant_le[of fri_dom table]
        lengths True by simp
  next
    case False
    have fri_dom_nonempty: "fri_dom \<noteq> []"
      using False by auto
    have interpolant_degree:
      "degree (fri_table_interpolant fri_dom table) < length fri_dom"
    proof -
      have
        "degree (fri_table_interpolant fri_dom table) \<le> length fri_dom - 1"
        using degree_fri_table_interpolant_le[of fri_dom table] lengths
        by simp
      also have "length fri_dom - 1 < length fri_dom"
        using fri_dom_nonempty by simp
      finally show ?thesis .
    qed
    have p_degree_strict: "degree p < length fri_dom"
      using p_degree False by linarith
    have card_dom: "card (set fri_dom) = length fri_dom"
      using distinct_dom by (simp add: distinct_card)
    have eval_eq:
      "\<And>x. x \<in> set fri_dom \<Longrightarrow>
        poly (fri_table_interpolant fri_dom table) x = poly p x"
    proof -
      fix x
      assume x_mem: "x \<in> set fri_dom"
      obtain i where i_bound: "i < length fri_dom"
        and x_eq: "fri_dom ! i = x"
        using x_mem unfolding in_set_conv_nth by blast
      have
        "map (poly (fri_table_interpolant fri_dom table)) fri_dom ! i =
          map (poly p) fri_dom ! i"
        using interpolant_reproduces p_reproduces by simp
      then show
        "poly (fri_table_interpolant fri_dom table) x = poly p x"
        using i_bound x_eq by simp
    qed
    have interpolant_card:
      "degree (fri_table_interpolant fri_dom table) < card (set fri_dom)"
      using interpolant_degree card_dom by linarith
    have p_card: "degree p < card (set fri_dom)"
      using p_degree_strict card_dom by linarith
    have polynomial_eq: "fri_table_interpolant fri_dom table = p"
      by (rule poly_eqI_degree[OF eval_eq interpolant_card p_card])
    show ?thesis using polynomial_eq p_degree by simp
  qed
next
  assume degree: "degree (fri_table_interpolant fri_dom table) \<le> d"
  have reproduces:
      "table = map (poly (fri_table_interpolant fri_dom table)) fri_dom"
    using fri_table_interpolant_reproduces[OF distinct_dom lengths]
    by simp
  show "fri_table_low_degree_on d fri_dom table"
    unfolding fri_table_low_degree_on_def
    by (intro exI[of _ "fri_table_interpolant fri_dom table"] conjI
        degree reproduces)
qed

lemma distinct_fri_round_domain:
  assumes len_pos: "0 < len"
    and pw_pos: "0 < pw"
    and round: "len * pw = clength * scale"
  shows
    "distinct
      (map (\<lambda>idx. (h ^ idx * shift) ^ pw) [0..<len])"
proof -
  have inj:
      "inj_on (\<lambda>idx. (h ^ idx * shift) ^ pw) (set [0..<len])"
  proof (intro inj_onI)
    fix i j
    assume i_in: "i \<in> set [0..<len]"
      and j_in: "j \<in> set [0..<len]"
      and eq:
        "(h ^ i * shift) ^ pw = (h ^ j * shift) ^ pw"
    have i_product: "i * pw < len * pw"
      using i_in pw_pos by simp
    have i_bound: "i * pw < clength * scale"
      using i_product round by simp
    have j_product: "j * pw < len * pw"
      using j_in pw_pos by simp
    have j_bound: "j * pw < clength * scale"
      using j_product round by simp
    have shift_power_nonzero: "shift ^ pw \<noteq> 0"
      using shift_nonzero by simp
    have multiplied_eq:
        "h ^ (i * pw) * shift ^ pw = h ^ (j * pw) * shift ^ pw"
      using eq by (simp add: power_mult power_mult_distrib)
    have power_eq: "h ^ (i * pw) = h ^ (j * pw)"
      using multiplied_eq shift_power_nonzero mult_right_cancel by blast
    have exponent_eq: "i * pw = j * pw"
      by (rule h_power_inj_on_eval_domain[OF i_bound j_bound power_eq])
    show "i = j"
      using exponent_eq pw_pos by simp
  qed
  show ?thesis
    using inj by (simp add: distinct_map)
qed

lemma fri_table_fold_value_polynomial:
  fixes p :: "'f poly"
  assumes len_pos: "0 < len"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
    and fri_dom:
      "fri_dom = map (\<lambda>idx. (h ^ idx * shift) ^ pw) [0..<len]"
    and layer: "layer = map (poly p) fri_dom"
    and idx_bound: "idx < len div 2"
  shows
    "fri_table_fold_value b layer fri_dom len pw idx =
      poly (fri_symbolic_fold_polynomial p b) ((fri_dom ! idx) ^ 2)"
proof -
  have idx_len: "idx < len"
    using idx_bound by simp
  have sibling_len: "fri_sibling_index len idx < len"
    using len_pos unfolding fri_sibling_index_def by simp
  have dom_idx:
      "fri_dom ! idx = (h ^ idx * shift) ^ pw"
    using fri_dom idx_len by simp
  have dom_sibling:
      "fri_dom ! fri_sibling_index len idx =
        (h ^ fri_sibling_index len idx * shift) ^ pw"
    using fri_dom sibling_len by simp
  have sibling_neg:
      "fri_dom ! fri_sibling_index len idx = - (fri_dom ! idx)"
    using fri_sibling_domain_round[OF len_pos even_len round, of idx]
      dom_idx dom_sibling
    unfolding fri_sibling_index_def by simp
  have z_nonzero: "fri_dom ! idx \<noteq> 0"
    using dom_idx h_nonzero shift_nonzero by simp
  have layer_idx: "layer ! idx = poly p (fri_dom ! idx)"
    using layer fri_dom idx_len by simp
  have layer_sibling:
      "layer ! fri_sibling_index len idx = poly p (- (fri_dom ! idx))"
    using layer fri_dom sibling_len sibling_neg by simp
  show ?thesis
    unfolding fri_table_fold_value_def fri_fold_value_def
      fri_fold_denominator_def
    using layer_idx layer_sibling
      fri_symbolic_fold_polynomial_eval[OF z_nonzero, of p b]
    by (simp add: power2_eq_square)
qed

definition fri_polynomial_agreement_indices
  :: "'f poly \<Rightarrow> 'f poly \<Rightarrow> 'f list \<Rightarrow> nat set"
where
  "fri_polynomial_agreement_indices p q fri_dom =
    {i. i < length fri_dom \<and> poly p (fri_dom ! i) = poly q (fri_dom ! i)}"

lemma fri_polynomial_agreement_indices_card_bound:
  assumes distinct_dom: "distinct fri_dom"
    and different: "p \<noteq> q"
  shows
    "card (fri_polynomial_agreement_indices p q fri_dom) \<le>
      max (degree p) (degree q)"
proof -
  let ?A = "fri_polynomial_agreement_indices p q fri_dom"
  let ?R = "p - q"
  have finite_A: "finite ?A"
    unfolding fri_polynomial_agreement_indices_def by simp
  have index_bound: "\<And>i. i \<in> ?A \<Longrightarrow> i < length fri_dom"
    unfolding fri_polynomial_agreement_indices_def by simp
  have inj: "inj_on (\<lambda>i. fri_dom ! i) ?A"
  proof (intro inj_onI)
    fix i j
    assume i_in: "i \<in> ?A"
      and j_in: "j \<in> ?A"
      and eq: "fri_dom ! i = fri_dom ! j"
    show "i = j"
      by (rule nth_eq_iff_index_eq[THEN iffD1])
        (use distinct_dom index_bound[OF i_in] index_bound[OF j_in] eq
          in simp_all)
  qed
  have residual_nonzero: "?R \<noteq> 0"
    using different by simp
  have image_subset:
      "(\<lambda>i. fri_dom ! i) ` ?A \<subseteq> {x. poly ?R x = 0}"
  proof
    fix x
    assume x_in: "x \<in> (\<lambda>i. fri_dom ! i) ` ?A"
    then obtain i where i_in: "i \<in> ?A"
      and x_eq: "x = fri_dom ! i"
      by blast
    have agreement:
        "poly p (fri_dom ! i) = poly q (fri_dom ! i)"
      using i_in unfolding fri_polynomial_agreement_indices_def by simp
    show "x \<in> {x. poly ?R x = 0}"
      using agreement x_eq by simp
  qed
  have "card ?A = card ((\<lambda>i. fri_dom ! i) ` ?A)"
    by (simp add: card_image inj)
  also have "... \<le> card {x. poly ?R x = 0}"
    by (rule card_mono[OF poly_roots_finite[OF residual_nonzero]
          image_subset])
  also have "... \<le> degree ?R"
    by (rule poly_roots_degree[OF residual_nonzero])
  also have "... \<le> max (degree p) (degree q)"
    by (rule degree_diff_le_max)
  finally show ?thesis .
qed

lemma high_degree_sampled_fold_challenge_or_agreement:
  fixes p :: "'f poly"
  assumes len_pos: "0 < len"
    and even_len: "2 dvd len"
    and round: "len * pw = clength * scale"
    and fri_dom:
      "fri_dom = map (\<lambda>i. (h ^ i * shift) ^ pw) [0..<len]"
    and layer: "layer = map (poly p) fri_dom"
    and next_dom:
      "successor_dom = map (\<lambda>i. (fri_dom ! i) ^ 2) [0..<len div 2]"
    and next_low: "fri_table_low_degree_on k successor_dom next_layer"
    and high: "degree p > 2 * k + 1"
    and idx_bound: "idx < len div 2"
    and sampled:
      "next_layer ! idx = fri_table_fold_value b layer fri_dom len pw idx"
  shows
    "b \<in> fri_low_fold_challenges p k \<or>
      (\<exists>q. degree q \<le> k \<and> next_layer = map (poly q) successor_dom \<and>
        idx \<in> fri_polynomial_agreement_indices
          (fri_symbolic_fold_polynomial p b) q successor_dom)"
proof (cases "b \<in> fri_low_fold_challenges p k")
  case True
  then show ?thesis by simp
next
  case False
  from next_low obtain q where q_degree: "degree q \<le> k"
    and next_layer: "next_layer = map (poly q) successor_dom"
    unfolding fri_table_low_degree_on_def by blast
  have folded_high:
      "degree (fri_symbolic_fold_polynomial p b) > k"
    using False unfolding fri_low_fold_challenges_def by simp
  have different: "fri_symbolic_fold_polynomial p b \<noteq> q"
  proof
    assume "fri_symbolic_fold_polynomial p b = q"
    then show False using folded_high q_degree by simp
  qed
  have successor_length: "length successor_dom = len div 2"
    using next_dom by simp
  have successor_idx:
      "successor_dom ! idx = (fri_dom ! idx) ^ 2"
    using next_dom idx_bound by simp
  have next_value:
      "next_layer ! idx = poly q (successor_dom ! idx)"
    using next_layer successor_length idx_bound by simp
  have folded_value:
      "fri_table_fold_value b layer fri_dom len pw idx =
        poly (fri_symbolic_fold_polynomial p b) (successor_dom ! idx)"
    using fri_table_fold_value_polynomial[
        OF len_pos even_len round fri_dom layer idx_bound, of b]
      successor_idx by simp
  have agreement:
      "poly (fri_symbolic_fold_polynomial p b) (successor_dom ! idx) =
        poly q (successor_dom ! idx)"
    using sampled next_value folded_value by simp
  have membership:
      "idx \<in> fri_polynomial_agreement_indices
        (fri_symbolic_fold_polynomial p b) q successor_dom"
    using idx_bound successor_length agreement
    unfolding fri_polynomial_agreement_indices_def by simp
  show ?thesis
    using q_degree next_layer membership by blast
qed

end

end
