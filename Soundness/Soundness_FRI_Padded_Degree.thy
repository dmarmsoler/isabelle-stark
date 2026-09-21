(*  Title:      Stark/Soundness_FRI_Padded_Degree.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Padded_Degree
  imports Soundness_FRI_Internal_Bounds
begin

text \<open>
  A verifier that performs @{term "ceil_log (Suc d)"} binary folds naturally
  distinguishes degree at the padded power-of-two threshold, rather than at an
  arbitrary exact bound @{term d}.  This theory makes that distinction explicit
  so that later soundness bounds do not misclassify the padding interval as a
  small bad-challenge event.
\<close>

context soundness
begin

definition fri_padded_degree_bound :: "nat \<Rightarrow> nat"
where
  "fri_padded_degree_bound d = 2 ^ ceil_log (Suc d) - 1"

lemma ceil_log_Suc_power_gt_soundness:
  "d < 2 ^ ceil_log (Suc d)"
proof (cases d)
  case 0
  then show ?thesis
    unfolding ceil_log_def by simp
next
  case (Suc d')
  then show ?thesis
    using floor_log_exp2_gt[of d]
    unfolding ceil_log_def
    by simp
qed

lemma fri_degree_le_padded_degree_bound:
  "d \<le> fri_padded_degree_bound d"
  unfolding fri_padded_degree_bound_def
  using ceil_log_Suc_power_gt_soundness[of d]
  by linarith

definition fri_symbolic_fold_polynomial
  :: "'f poly \<Rightarrow> 'f \<Rightarrow> 'f poly"
where
  "fri_symbolic_fold_polynomial p b =
    CP b * poly_of_list (nths_pred (coeffs p) odd) +
      poly_of_list (nths_pred (coeffs p) even)"

lemma nths_pred_X3_odd [simp]:
  "nths_pred ([0, 0, 0, 1] :: 'f list) odd = [0, 1]"
  by (simp add: nths_pred_def nths_Cons)

lemma nths_pred_X3_even [simp]:
  "nths_pred ([0, 0, 0, 1] :: 'f list) even = [0, 0]"
  by (simp add: nths_pred_def nths_Cons)

lemma coeffs_monom_one_3 [simp]:
  "coeffs (monom (1 :: 'f) 3) = [0, 0, 0, 1]"
  by (simp add: coeffs_monom numeral_eq_Suc)

lemma fri_symbolic_fold_X3:
  "fri_symbolic_fold_polynomial (monom 1 3) b = [:0, b:]"
  unfolding fri_symbolic_fold_polynomial_def CP_def
  by (simp only: coeffs_monom_one_3 nths_pred_X3_odd
      nths_pred_X3_even; simp add: monom_0)

lemma fri_symbolic_fold_X3_exact_degree_gap:
  "degree (monom (1 :: 'f) 3) > 2 \<and>
    (\<forall>b :: 'f.
      degree (fri_symbolic_fold_polynomial (monom 1 3) b) \<le> 2 div 2)"
  unfolding fri_symbolic_fold_X3
  by (simp add: degree_monom_eq)

end
end
