(* Title: Stark/Soundness_Square_Allocation_Arithmetic.thy
   License: BSD-3-Clause *)

theory Soundness_Square_Allocation_Arithmetic
imports Complex_Main
begin

section \<open>Exact clipped integer-quadratic maximization\<close>

text \<open>The vertex is the nearest integer to B/16, clipped to the allowed
  interval. Both neighboring directions are proved explicitly, including
  zero budget, clipping and the half-integer tie. This is pure arithmetic;
  no allocation is excluded from the adversary experiment.\<close>

definition allocation_vertex :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "allocation_vertex B Q = min Q ((B+8) div 16)"


lemma allocation_vertex_le: "allocation_vertex B Q \<le> Q"
  by (simp add: allocation_vertex_def)

lemma allocation_div_bounds:
  "16*((B+8) div 16) \<le> B+8"
  "B+8 < 16*(((B+8) div 16)+1)"
  for B :: nat
  by arith+

lemma allocation_vertex_left:
  assumes "x < allocation_vertex B Q"
  shows "8*(x+allocation_vertex B Q) \<le> B"
proof -
  have k: "allocation_vertex B Q \<le> (B+8) div 16"
    by (simp add: allocation_vertex_def)
  show ?thesis using assms k allocation_div_bounds(1)[of B]
    by simp
qed

lemma allocation_vertex_right:
  assumes "allocation_vertex B Q < x" "x \<le> Q"
  shows "B \<le> 8*(x+allocation_vertex B Q)"
proof -
  have k: "allocation_vertex B Q = (B+8) div 16"
    using assms unfolding allocation_vertex_def by auto
  show ?thesis using assms allocation_div_bounds(2)[of B] unfolding k
    by simp
qed

lemma allocation_vertex_max:
  assumes "x \<le> Q"
  shows "real B * real x - 8*(real x)^2 \<le>
    real B * real (allocation_vertex B Q) - 8*(real (allocation_vertex B Q))^2"
proof (cases "x < allocation_vertex B Q")
  case True
  have a: "(0::real) \<le> real (allocation_vertex B Q) - real x"
    using True by simp
  have b: "(0::real) \<le> real B - 8*(real x+real (allocation_vertex B Q))"
    using allocation_vertex_left[OF True]
    by (simp only: of_nat_le_iff[symmetric, where 'a=real] of_nat_mult
      of_nat_add of_nat_numeral; simp)
  have prod: "0 \<le> (real (allocation_vertex B Q)-real x) *
    (real B-8*(real x+real (allocation_vertex B Q)))"
    by (rule mult_nonneg_nonneg[OF a b])
  show ?thesis using prod by (simp add: algebra_simps power2_eq_square)
next
  case False
  show ?thesis
  proof (cases "x = allocation_vertex B Q")
    case True
    then show ?thesis by simp
  next
    case neq: False
    have gt: "allocation_vertex B Q < x" using False neq by arith
    have a: "(0::real) \<le> real x-real (allocation_vertex B Q)"
      using gt by simp
    have b: "(0::real) \<le> 8*(real x+real (allocation_vertex B Q))-real B"
      using allocation_vertex_right[OF gt assms]
      by (simp only: of_nat_le_iff[symmetric, where 'a=real] of_nat_mult
        of_nat_add of_nat_numeral; simp)
    have prod: "0 \<le> (real x-real (allocation_vertex B Q)) *
      (8*(real x+real (allocation_vertex B Q))-real B)"
      by (rule mult_nonneg_nonneg[OF a b])
    show ?thesis using prod by (simp add: algebra_simps power2_eq_square)
  qed
qed

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then writeln ("Checked quadratic theorem: " ^ Thm.string_of_thm @{context} th)
    else error "Unexpected quadratic proof dependency")
    @{thms allocation_vertex_le allocation_div_bounds allocation_vertex_left
      allocation_vertex_right allocation_vertex_max};
\<close>

end
