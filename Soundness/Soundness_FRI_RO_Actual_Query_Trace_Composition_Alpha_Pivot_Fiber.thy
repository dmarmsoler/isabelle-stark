(*  Title:      Stark/Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Fiber.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Pivot_Fiber
  imports Soundness_FRI_RO_Actual_Query_Trace_Composition_Alpha_Exact
begin

context soundness
begin

definition composition_alpha_root_good
where
  "composition_alpha_root_good f r \<longleftrightarrow>
    (\<exists>c roots d.
      (c, roots, d) \<in> violated_constraints f \<and> r \<in> set roots) \<and>
    (\<exists>i < length spec.
      common_denominator_constraint_root_residual
        f r (1, spec ! i) \<noteq> 0)"

definition composition_alpha_selected_root
where
  "composition_alpha_selected_root f =
    (SOME r. composition_alpha_root_good f r)"

lemma composition_alpha_root_good_exists:
  assumes violated: "violated_constraints f \<noteq> {}"
  shows "\<exists>r. composition_alpha_root_good f r"
proof -
  from violated_constraints_has_common_denominator_coefficient[OF violated]
  obtain i c roots d r where
    i_bound: "i < length spec"
    and spec_i: "spec ! i = (c, roots, d)"
    and entry: "(c, roots, d) \<in> violated_constraints f"
    and r_in: "r \<in> set roots"
    and coeff:
      "poly (c (trace_powers_of f)) (g ^ r) *
        poly (constraint_root_cofactor roots) (g ^ r) \<noteq> 0"
    by blast
  have residual:
      "common_denominator_constraint_root_residual
        f r (1, spec ! i) \<noteq> 0"
    using spec_i r_in coeff
    unfolding common_denominator_constraint_root_residual_def
    by simp
  show ?thesis
    unfolding composition_alpha_root_good_def
  proof (rule exI[of _ r], intro conjI)
    show "\<exists>c roots d.
        (c, roots, d) \<in> violated_constraints f \<and> r \<in> set roots"
      using entry r_in by blast
    show "\<exists>i<length spec.
        common_denominator_constraint_root_residual f r
          (1, spec ! i) \<noteq> 0"
      using i_bound residual by blast
  qed
qed

lemma composition_alpha_selected_root_good:
  assumes violated: "violated_constraints f \<noteq> {}"
  shows
    "composition_alpha_root_good f
      (composition_alpha_selected_root f)"
  unfolding composition_alpha_selected_root_def
  by (rule someI_ex[OF composition_alpha_root_good_exists[OF violated]])

lemma composition_alpha_selected_root_violated:
  assumes violated: "violated_constraints f \<noteq> {}"
  obtains c roots d where
    "(c, roots, d) \<in> violated_constraints f"
    "composition_alpha_selected_root f \<in> set roots"
  using composition_alpha_selected_root_good[OF violated]
  unfolding composition_alpha_root_good_def
  by blast

lemma composition_alpha_selected_root_has_nonzero:
  assumes violated: "violated_constraints f \<noteq> {}"
  shows
    "\<exists>i < length spec.
      common_denominator_constraint_root_residual f
        (composition_alpha_selected_root f) (1, spec ! i) \<noteq> 0"
  using composition_alpha_selected_root_good[OF violated]
  unfolding composition_alpha_root_good_def
  by blast


definition composition_alpha_nonzero_positions
where
  "composition_alpha_nonzero_positions f =
    {i. i < length spec \<and>
      common_denominator_constraint_root_residual f
        (composition_alpha_selected_root f) (1, spec ! i) \<noteq> 0}"

definition composition_alpha_pivot
where
  "composition_alpha_pivot f =
    Max (composition_alpha_nonzero_positions f)"

lemma finite_composition_alpha_nonzero_positions[simp]:
  "finite (composition_alpha_nonzero_positions f)"
  unfolding composition_alpha_nonzero_positions_def
  by (rule finite_subset[of _ "{..<length spec}"]) auto

lemma composition_alpha_nonzero_positions_nonempty:
  assumes violated: "violated_constraints f \<noteq> {}"
  shows "composition_alpha_nonzero_positions f \<noteq> {}"
  using composition_alpha_selected_root_has_nonzero[OF violated]
  unfolding composition_alpha_nonzero_positions_def
  by blast

lemma composition_alpha_pivot_mem:
  assumes violated: "violated_constraints f \<noteq> {}"
  shows
    "composition_alpha_pivot f \<in>
      composition_alpha_nonzero_positions f"
  unfolding composition_alpha_pivot_def
proof (rule Max_in)
  show "finite (composition_alpha_nonzero_positions f)"
    by simp
  show "composition_alpha_nonzero_positions f \<noteq> {}"
    by (rule composition_alpha_nonzero_positions_nonempty[OF violated])
qed

lemma composition_alpha_pivot_bound:
  assumes violated: "violated_constraints f \<noteq> {}"
  shows "composition_alpha_pivot f < length spec"
  using composition_alpha_pivot_mem[OF violated]
  unfolding composition_alpha_nonzero_positions_def
  by blast

lemma composition_alpha_pivot_nonzero:
  assumes violated: "violated_constraints f \<noteq> {}"
  shows
    "common_denominator_constraint_root_residual f
      (composition_alpha_selected_root f)
      (1, spec ! composition_alpha_pivot f) \<noteq> 0"
  using composition_alpha_pivot_mem[OF violated]
  unfolding composition_alpha_nonzero_positions_def
  by blast

lemma composition_alpha_after_pivot_zero:
  assumes violated: "violated_constraints f \<noteq> {}"
    and pivot_lt: "composition_alpha_pivot f < j"
    and j_bound: "j < length spec"
  shows
    "common_denominator_constraint_root_residual f
      (composition_alpha_selected_root f) (1, spec ! j) = 0"
proof (rule ccontr)
  assume nonzero:
    "common_denominator_constraint_root_residual f
      (composition_alpha_selected_root f) (1, spec ! j) \<noteq> 0"
  have j_mem:
      "j \<in> composition_alpha_nonzero_positions f"
    unfolding composition_alpha_nonzero_positions_def
    using j_bound nonzero by simp
  have "j \<le> composition_alpha_pivot f"
    unfolding composition_alpha_pivot_def
    by (rule Max_ge[OF finite_composition_alpha_nonzero_positions j_mem])
  then show False
    using pivot_lt by simp
qed


lemma common_denominator_constraint_root_residual_scale:
  "common_denominator_constraint_root_residual f r (a, entry) =
    a * common_denominator_constraint_root_residual f r (1, entry)"
  unfolding common_denominator_constraint_root_residual_def
  by (cases entry) (simp add: algebra_simps)

lemma composition_trace_bad_alpha_space_violated:
  assumes as_bad: "as \<in> composition_trace_bad_alpha_space trace_table"
  shows
    "violated_constraints (low_degree_trace_witness trace_table) \<noteq> {}"
  using as_bad
  unfolding composition_trace_bad_alpha_space_def Let_def
  by (auto split: if_splits)

lemma composition_trace_bad_alpha_space_hides:
  assumes as_bad: "as \<in> composition_trace_bad_alpha_space trace_table"
  shows
    "random_combination_common_denominator_hides_violations
      (low_degree_trace_witness trace_table) as"
  using as_bad
  unfolding composition_trace_bad_alpha_space_def Let_def
    common_denominator_hiding_alpha_space_def
  by (auto split: if_splits)

lemma composition_trace_bad_alpha_space_length:
  assumes as_bad: "as \<in> composition_trace_bad_alpha_space trace_table"
  shows "length as = length spec"
  using as_bad composition_trace_bad_alpha_space_subset_alpha_space
  unfolding alpha_space_def
  by blast

lemma composition_trace_bad_alpha_space_selected_root_zero:
  assumes as_bad: "as \<in> composition_trace_bad_alpha_space trace_table"
  shows
    "common_denominator_composition_root_residual
      (low_degree_trace_witness trace_table) as
      (composition_alpha_selected_root
        (low_degree_trace_witness trace_table)) = 0"
proof -
  let ?f = "low_degree_trace_witness trace_table"
  have violated: "violated_constraints ?f \<noteq> {}"
    by (rule composition_trace_bad_alpha_space_violated[OF as_bad])
  from composition_alpha_selected_root_violated[OF violated]
  obtain c roots d where
    entry: "(c, roots, d) \<in> violated_constraints ?f"
    and root:
      "composition_alpha_selected_root ?f \<in> set roots"
    by blast
  have hides:
      "random_combination_common_denominator_hides_violations ?f as"
    by (rule composition_trace_bad_alpha_space_hides[OF as_bad])
  show ?thesis
    using hides entry root
    unfolding random_combination_common_denominator_hides_violations_def
    by auto
qed


lemma composition_trace_bad_alpha_pivot_prefix_unique:
  assumes as_bad:
      "as \<in> composition_trace_bad_alpha_space trace_table"
    and bs_bad:
      "bs \<in> composition_trace_bad_alpha_space trace_table"
    and prefix_eq:
      "take
        (composition_alpha_pivot
          (low_degree_trace_witness trace_table)) as =
       take
        (composition_alpha_pivot
          (low_degree_trace_witness trace_table)) bs"
  shows
    "as ! composition_alpha_pivot
        (low_degree_trace_witness trace_table) =
     bs ! composition_alpha_pivot
        (low_degree_trace_witness trace_table)"
proof -
  let ?f = "low_degree_trace_witness trace_table"
  let ?r = "composition_alpha_selected_root ?f"
  let ?i = "composition_alpha_pivot ?f"
  let ?C =
    "common_denominator_constraint_root_residual ?f ?r
      (1, spec ! ?i)"
  let ?B_as =
    "\<Sum>j\<in>{0..<length spec} - {?i}.
      common_denominator_constraint_root_residual ?f ?r
        (as ! j, spec ! j)"
  let ?B_bs =
    "\<Sum>j\<in>{0..<length spec} - {?i}.
      common_denominator_constraint_root_residual ?f ?r
        (bs ! j, spec ! j)"
  have violated: "violated_constraints ?f \<noteq> {}"
    by (rule composition_trace_bad_alpha_space_violated[OF as_bad])
  have i_bound: "?i < length spec"
    by (rule composition_alpha_pivot_bound[OF violated])
  have C_nonzero: "?C \<noteq> 0"
    by (rule composition_alpha_pivot_nonzero[OF violated])
  have len_as: "length as = length spec"
    by (rule composition_trace_bad_alpha_space_length[OF as_bad])
  have len_bs: "length bs = length spec"
    by (rule composition_trace_bad_alpha_space_length[OF bs_bad])
  have zero_as:
      "common_denominator_composition_root_residual ?f as ?r = 0"
    by (rule
      composition_trace_bad_alpha_space_selected_root_zero[OF as_bad])
  have zero_bs:
      "common_denominator_composition_root_residual ?f bs ?r = 0"
    by (rule
      composition_trace_bad_alpha_space_selected_root_zero[OF bs_bad])
  have outside_terms:
    "\<And>j. j \<in> {0..<length spec} - {?i} \<Longrightarrow>
      common_denominator_constraint_root_residual ?f ?r
        (as ! j, spec ! j) =
      common_denominator_constraint_root_residual ?f ?r
        (bs ! j, spec ! j)"
  proof -
    fix j
    assume j_in: "j \<in> {0..<length spec} - {?i}"
    then have j_bound: "j < length spec"
      and j_ne: "j \<noteq> ?i"
      by simp_all
    show
      "common_denominator_constraint_root_residual ?f ?r
          (as ! j, spec ! j) =
       common_denominator_constraint_root_residual ?f ?r
          (bs ! j, spec ! j)"
    proof (cases "j < ?i")
      case True
      have as_nth: "as ! j = take ?i as ! j"
        using True by simp
      have bs_nth: "bs ! j = take ?i bs ! j"
        using True by simp
      have "as ! j = bs ! j"
        using prefix_eq as_nth bs_nth by simp
      then show ?thesis by simp
    next
      case False
      then have i_lt_j: "?i < j"
        using j_ne by linarith
      have coeff_zero:
          "common_denominator_constraint_root_residual ?f ?r
            (1, spec ! j) = 0"
        by (rule composition_alpha_after_pivot_zero[
              OF violated i_lt_j j_bound])
      have as_scale:
          "common_denominator_constraint_root_residual ?f ?r
              (as ! j, spec ! j) =
            (as ! j) *
              common_denominator_constraint_root_residual ?f ?r
                (1, spec ! j)"
        by (rule common_denominator_constraint_root_residual_scale)
      have bs_scale:
          "common_denominator_constraint_root_residual ?f ?r
              (bs ! j, spec ! j) =
            (bs ! j) *
              common_denominator_constraint_root_residual ?f ?r
                (1, spec ! j)"
        by (rule common_denominator_constraint_root_residual_scale)
      show ?thesis
        using as_scale bs_scale coeff_zero by simp
    qed
  qed
  have B_eq: "?B_as = ?B_bs"
    by (intro sum.cong refl outside_terms)
  have split_as:
      "common_denominator_composition_root_residual ?f as ?r =
        common_denominator_constraint_root_residual ?f ?r
          (as ! ?i, spec ! ?i) + ?B_as"
    by (rule common_denominator_composition_root_residual_split_index[
          OF len_as i_bound])
  have split_bs:
      "common_denominator_composition_root_residual ?f bs ?r =
        common_denominator_constraint_root_residual ?f ?r
          (bs ! ?i, spec ! ?i) + ?B_bs"
    by (rule common_denominator_composition_root_residual_split_index[
          OF len_bs i_bound])
  have as_scale:
      "common_denominator_constraint_root_residual ?f ?r
          (as ! ?i, spec ! ?i) = (as ! ?i) * ?C"
    by (rule common_denominator_constraint_root_residual_scale)
  have bs_scale:
      "common_denominator_constraint_root_residual ?f ?r
          (bs ! ?i, spec ! ?i) = (bs ! ?i) * ?C"
    by (rule common_denominator_constraint_root_residual_scale)
  have equation_as: "?C * (as ! ?i) + ?B_as = 0"
    using split_as zero_as as_scale
    by (simp add: mult.commute)
  have equation_bs: "?C * (bs ! ?i) + ?B_as = 0"
    using split_bs zero_bs B_eq bs_scale
    by (simp add: mult.commute)
  show ?thesis
    by (rule linear_equation_solution_unique[
          OF C_nonzero equation_as equation_bs])
qed


definition composition_trace_bad_alpha_pivot_values
where
  "composition_trace_bad_alpha_pivot_values trace_table prefix =
    {y. \<exists>as \<in> composition_trace_bad_alpha_space trace_table.
      take
        (composition_alpha_pivot
          (low_degree_trace_witness trace_table)) as = prefix \<and>
      y = as ! composition_alpha_pivot
        (low_degree_trace_witness trace_table)}"

lemma composition_trace_bad_alpha_pivot_values_card_le_one:
  "card
      (composition_trace_bad_alpha_pivot_values trace_table prefix) \<le> 1"
proof (cases
    "composition_trace_bad_alpha_pivot_values trace_table prefix = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain y0 where y0:
      "y0 \<in> composition_trace_bad_alpha_pivot_values trace_table prefix"
    by blast
  have subset:
      "composition_trace_bad_alpha_pivot_values trace_table prefix \<subseteq> {y0}"
  proof
    fix y
    assume y:
        "y \<in> composition_trace_bad_alpha_pivot_values trace_table prefix"
    from y0 obtain as0 where
      as0_bad: "as0 \<in> composition_trace_bad_alpha_space trace_table"
      and as0_prefix:
        "take
          (composition_alpha_pivot
            (low_degree_trace_witness trace_table)) as0 = prefix"
      and y0_eq:
        "y0 = as0 ! composition_alpha_pivot
          (low_degree_trace_witness trace_table)"
      unfolding composition_trace_bad_alpha_pivot_values_def
      by blast
    from y obtain as where
      as_bad: "as \<in> composition_trace_bad_alpha_space trace_table"
      and as_prefix:
        "take
          (composition_alpha_pivot
            (low_degree_trace_witness trace_table)) as = prefix"
      and y_eq:
        "y = as ! composition_alpha_pivot
          (low_degree_trace_witness trace_table)"
      unfolding composition_trace_bad_alpha_pivot_values_def
      by blast
    have pivot_eq:
        "as ! composition_alpha_pivot
            (low_degree_trace_witness trace_table) =
         as0 ! composition_alpha_pivot
            (low_degree_trace_witness trace_table)"
      by (rule composition_trace_bad_alpha_pivot_prefix_unique[
            OF as_bad as0_bad])
        (use as_prefix as0_prefix in simp)
    show "y \<in> {y0}"
      using y_eq y0_eq pivot_eq by simp
  qed
  show ?thesis
    by (rule order_trans[OF card_mono[of "{y0}" _] _])
      (use subset in simp_all)
qed

lemma composition_trace_bad_alpha_pivot_value_member:
  assumes as_bad: "as \<in> composition_trace_bad_alpha_space trace_table"
  shows
    "as ! composition_alpha_pivot
        (low_degree_trace_witness trace_table) \<in>
      composition_trace_bad_alpha_pivot_values trace_table
        (take
          (composition_alpha_pivot
            (low_degree_trace_witness trace_table)) as)"
  unfolding composition_trace_bad_alpha_pivot_values_def
  using as_bad by blast

end
end