(* Title: Stark/Soundness_Square_Allocation_Bound.thy
   License: BSD-3-Clause *)

theory Soundness_Square_Allocation_Bound
  imports Soundness_Square_Weighted_Ledger Soundness_Square_Allocation_Arithmetic
begin

section \<open>Allocation-uniform weighted ledger\<close>

text \<open>The middle coordinate is eliminated only when maximizing the existing
  error formula: no staged adversary allocation is forbidden. The exact clipped
  vertex then maximizes the remaining integer quadratic. Padding unused scalar
  allowance is a monotone arithmetic comparison, not an execution modification.
  Every modulo and exceptional charge remains in the original ledger.\<close>

subsection \<open>Exact maximum at a fixed total budget\<close>

lemma square_middle_transfer_identity:
  "square_mca_common_numerator R (Suc s) j opening +
    square_mca_common_numerator R s j (Suc opening) =
    2*square_mca_common_numerator R s (Suc j) opening + 8*j+401"
  apply (rule of_nat_eq_iff[where 'a=real, THEN iffD1])
  by (simp add: square_mca_common_numerator_def Let_def algebra_simps power2_eq_square)

lemma square_middle_elimination:
  "\<exists>k t. k+t=s+j+opening \<and>
    square_mca_common_numerator R s j opening \<le>
      square_mca_common_numerator R k 0 t"
proof (induction j arbitrary: s "opening")
  case 0
  then show ?case by auto
next
  case (Suc j)
  have step: "square_mca_common_numerator R s (Suc j) opening \<le>
      square_mca_common_numerator R (Suc s) j opening \<or>
    square_mca_common_numerator R s (Suc j) opening \<le>
      square_mca_common_numerator R s j (Suc opening)"
    using square_middle_transfer_identity[of R s j "opening"] by arith
  obtain k t where left: "k+t=Suc s+j+opening"
    "square_mca_common_numerator R (Suc s) j opening \<le>
      square_mca_common_numerator R k 0 t" using Suc.IH[of "Suc s" "opening"] by blast
  obtain k' t' where right: "k'+t'=s+j+Suc opening"
    "square_mca_common_numerator R s j (Suc opening) \<le>
      square_mca_common_numerator R k' 0 t'" using Suc.IH[of s "Suc opening"] by blast
  show ?case using step left right by (auto intro: order_trans)
qed

lemma square_allocation_quadratic_identity:
  "square_mca_common_numerator R s 0 opening + 8*s^2 =
    square_mca_common_numerator R 0 0 (s+opening) +
      (8*(s+opening)+159+9996*R)*s"
  apply (rule of_nat_eq_iff[where 'a=real, THEN iffD1])
  by (simp add: square_mca_common_numerator_def Let_def algebra_simps power2_eq_square)

definition square_maximizing_early_budget :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "square_maximizing_early_budget R Q = allocation_vertex (8*Q+159+9996*R) Q"

lemma square_maximizing_early_budget_explicit:
  "square_maximizing_early_budget R Q = min Q ((8*Q+167+9996*R) div 16)"
  by (simp add: square_maximizing_early_budget_def allocation_vertex_def algebra_simps)

lemma square_maximizing_early_budget_zero:
  "square_maximizing_early_budget R 0 = 0"
  by (simp add: square_maximizing_early_budget_explicit)

lemma square_maximizing_early_budget_le:
  "square_maximizing_early_budget R Q \<le> Q"
  unfolding square_maximizing_early_budget_def by (rule allocation_vertex_le)

lemma square_common_numerator_maximum:
  assumes total: "s+j+opening=Q"
  shows "square_mca_common_numerator R s j opening \<le>
    square_mca_common_numerator R (square_maximizing_early_budget R Q) 0
      (Q-square_maximizing_early_budget R Q)"
proof -
  obtain u w where sum: "u+w=Q" and le:
    "square_mca_common_numerator R s j opening \<le>
      square_mca_common_numerator R u 0 w"
    using square_middle_elimination[of s j "opening" R] total by blast
  let ?k = "square_maximizing_early_budget R Q"
  have ksum: "?k+(Q-?k)=Q" using square_maximizing_early_budget_le[of R Q] by simp
  have umax: "real (8*Q+159+9996*R)*real u - 8*(real u)^2 \<le>
    real (8*Q+159+9996*R)*real ?k - 8*(real ?k)^2"
    unfolding square_maximizing_early_budget_def
    by (rule allocation_vertex_max) (use sum in arith)
  have eu: "real (square_mca_common_numerator R u 0 w) + 8*(real u)^2 =
      real (square_mca_common_numerator R 0 0 Q) +
      real (8*Q+159+9996*R)*real u"
    using arg_cong[OF square_allocation_quadratic_identity[of R u w], of real]
    by (simp add: sum)
  have ek: "real (square_mca_common_numerator R ?k 0 (Q-?k)) + 8*(real ?k)^2 =
      real (square_mca_common_numerator R 0 0 Q) +
      real (8*Q+159+9996*R)*real ?k"
    using arg_cong[OF square_allocation_quadratic_identity[of R ?k "Q-?k"], of real]
    by (simp add: ksum)
  have "real (square_mca_common_numerator R u 0 w) \<le>
      real (square_mca_common_numerator R ?k 0 (Q-?k))"
    using umax eu ek by linarith
  then have "square_mca_common_numerator R u 0 w \<le>
      square_mca_common_numerator R ?k 0 (Q-?k)" by simp
  with le show ?thesis by (rule order_trans)
qed

subsection \<open>Uniform ledger and unused allowance\<close>

lemma square_common_numerator_opening_mono:
  assumes "opn \<le> opn'"
  shows "square_mca_common_numerator R s j opn \<le>
    square_mca_common_numerator R s j opn'"
  unfolding square_mca_common_numerator_def Let_def
  by (intro add_le_mono mult_le_mono power_mono order_refl assms; simp)

definition square_uniform_ledger :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "square_uniform_ledger F R Q =
    square_weighted_ledger F R (square_maximizing_early_budget R Q) 0
      (Q-square_maximizing_early_budget R Q)"

lemma square_weighted_ledger_allocation_bound:
  assumes total: "s+j+opn=Q"
  shows "square_weighted_ledger F R s j opn \<le> square_uniform_ledger F R Q"
proof -
  have sum: "square_maximizing_early_budget R Q +
      (Q-square_maximizing_early_budget R Q)=Q"
    using square_maximizing_early_budget_le[of R Q] by simp
  have common: "real (square_mca_common_numerator R s j opn) / real F \<le>
      real (square_mca_common_numerator R (square_maximizing_early_budget R Q) 0
        (Q-square_maximizing_early_budget R Q)) / real F"
    by (intro divide_right_mono) (use square_common_numerator_maximum[OF total, of R] in auto)
  show ?thesis
    unfolding square_uniform_ledger_def square_weighted_ledger_def Let_def
    using common total sum by simp
qed

lemma square_modulo_base_nonnegative: "0 \<le> square_modulo_base F B"
  by (simp add: square_modulo_base_def)

lemma square_weighted_ledger_opening_mono:
  assumes "opn \<le> opn'"
  shows "square_weighted_ledger F R s j opn \<le>
    square_weighted_ledger F R s j opn'"
proof -
  let ?n = "real (s+j+opn+100+1964*R)"
  let ?m = "real (s+j+opn'+100+1964*R)"
  let ?p = "square_modulo_base F 54953^R+2*square_modulo_base F 54954^R"
  have nm: "?n \<le> ?m" using assms by simp
  have n1: "1 \<le> ?n" by simp
  have p0: "0 \<le> ?p"
    by (intro add_nonneg_nonneg mult_nonneg_nonneg zero_le_power
      square_modulo_base_nonnegative; simp)
  have c: "real (square_mca_common_numerator R s j opn) / real F \<le>
      real (square_mca_common_numerator R s j opn') / real F"
    by (intro divide_right_mono)
      (use square_common_numerator_opening_mono[OF assms, of R s j] in auto)
  have target: "?n / real F \<le> ?m / real F"
    by (intro divide_right_mono nm; simp)
  have sampling: "?n*?p \<le> ?m*?p" by (rule mult_right_mono[OF nm p0])
  have product: "5*?n*(?n-1) \<le> 5*?m*(?m-1)"
    by (intro mult_mono) (use nm n1 in auto)
  have connection: "5*?n*(?n-1)/(2*real F) \<le> 5*?m*(?m-1)/(2*real F)"
    by (intro divide_right_mono product; simp)
  show ?thesis
    unfolding square_weighted_ledger_def Let_def
    using c target sampling connection
    by argo
qed

lemma square_weighted_ledger_at_most_budget:
  assumes cap: "s+j+opn \<le> Q"
  shows "square_weighted_ledger F R s j opn \<le> square_uniform_ledger F R Q"
proof -
  let ?extra = "Q-(s+j+opn)"
  have sum: "s+j+(opn+?extra)=Q" using cap by arith
  have "square_weighted_ledger F R s j opn \<le>
      square_weighted_ledger F R s j (opn+?extra)"
    by (rule square_weighted_ledger_opening_mono) simp
  also have "... \<le> square_uniform_ledger F R Q"
    by (rule square_weighted_ledger_allocation_bound[OF sum])
  finally show ?thesis .
qed

lemma square_uniform_ledger_mono:
  assumes "Q \<le> Q'"
  shows "square_uniform_ledger F R Q \<le> square_uniform_ledger F R Q'"
  unfolding square_uniform_ledger_def[of F R Q]
  by (rule square_weighted_ledger_at_most_budget)
    (use square_maximizing_early_budget_le[of R Q] assms in auto)

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then writeln ("Checked allocation arithmetic: " ^ Thm.string_of_thm @{context} th)
    else error "Unexpected proof dependency")
    @{thms allocation_vertex_max square_middle_transfer_identity
      square_middle_elimination square_allocation_quadratic_identity
      square_common_numerator_maximum square_weighted_ledger_allocation_bound
      square_weighted_ledger_opening_mono square_weighted_ledger_at_most_budget
      square_uniform_ledger_mono};
\<close>

end
