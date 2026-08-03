(*  Title:      Stark/NNReal.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory NNReal
  imports
    Complex_Main
    "HOL-Library.FSet"
    "HOL-Library.Conditional_Parametricity"
begin

section \<open>Finite Non-negative Real Numbers\<close>

text \<open>
  HOL-Probability already provides the extended non-negative real numbers
  (usually called \<open>ennreal\<close>).  That type is ideal for measure theory:
  non-negative integrals and measures may naturally take the value infinity.

  The probabilistic state monad in this development only uses finite,
  discrete probability weights.  For that purpose it is useful to have a
  smaller type of finite non-negative real numbers, implemented as a subtype
  of @{typ real}.  This avoids proof obligations about infinity while keeping
  non-negativity as a type invariant.
\<close>


subsection \<open>Type definition\<close>

typedef nnreal = "{x :: real. 0 \<le> x}"
  morphisms nn2real real2nn
  by auto

setup_lifting type_definition_nnreal

lemma nn2real_nonneg[simp]: "0 \<le> nn2real x"
  using nn2real[of x] by simp

lemma real2nn_nn2real[simp]: "real2nn (nn2real x) = x"
  by (rule nn2real_inverse)

lemma nn2real_real2nn[simp]:
  assumes "0 \<le> x"
  shows "nn2real (real2nn x) = x"
  using assms by (auto intro: real2nn_inverse)


subsection \<open>Basic operations\<close>

instantiation nnreal :: zero
begin

lift_definition zero_nnreal :: nnreal is 0 by simp

instance ..

end

instantiation nnreal :: one
begin

lift_definition one_nnreal :: nnreal is 1 by simp

instance ..

end

instantiation nnreal :: plus
begin

lift_definition plus_nnreal :: "nnreal \<Rightarrow> nnreal \<Rightarrow> nnreal" is "(+)" by simp

instance ..

end

instantiation nnreal :: times
begin

lift_definition times_nnreal :: "nnreal \<Rightarrow> nnreal \<Rightarrow> nnreal" is "(*)" by simp

instance ..

end

instantiation nnreal :: ord
begin

lift_definition less_eq_nnreal :: "nnreal \<Rightarrow> nnreal \<Rightarrow> bool" is "(\<le>)" .

lift_definition less_nnreal :: "nnreal \<Rightarrow> nnreal \<Rightarrow> bool" is "(<)" .

instance ..

end

instantiation nnreal :: minus
begin

lift_definition minus_nnreal :: "nnreal \<Rightarrow> nnreal \<Rightarrow> nnreal"
  is "\<lambda>x y. max 0 (x - y)"
  by simp

instance ..

end

instantiation nnreal :: divide
begin

lift_definition divide_nnreal :: "nnreal \<Rightarrow> nnreal \<Rightarrow> nnreal" is "(/)" by simp

instance ..

end

instantiation nnreal :: inverse
begin

lift_definition inverse_nnreal :: "nnreal \<Rightarrow> nnreal" is inverse by simp

instance ..

end

instantiation nnreal :: equal
begin

lift_definition equal_nnreal :: "nnreal \<Rightarrow> nnreal \<Rightarrow> bool" is "(=)" .

instance by (intro_classes, transfer, auto)

end

subsection \<open>Algebra and order instances\<close>

instantiation nnreal :: linordered_semidom
begin

instance
  by (intro_classes;transfer,(simp|linarith|algebra))
  (metis max.absorb2 max.order_iff mult_nonneg_nonpos nle_le right_diff_distrib' zero_le_mult_iff)

end

instantiation nnreal :: comm_monoid_diff
begin

instance
  by intro_classes (transfer; auto simp: max_def)

end

subsection \<open>Representation simp rules\<close>

lemma nn2real_eq_iff[simp]: "nn2real x = nn2real y \<longleftrightarrow> x = y"
  by transfer simp

lemma nn2real_le_iff[simp]: "nn2real x \<le> nn2real y \<longleftrightarrow> x \<le> y"
  by transfer simp

lemma nn2real_less_iff[simp]: "nn2real x < nn2real y \<longleftrightarrow> x < y"
  by transfer simp

lemma nn2real_0[simp]: "nn2real 0 = 0"
  by transfer simp

lemma nn2real_1[simp]: "nn2real 1 = 1"
  by transfer simp

lemma nn2real_add[simp]: "nn2real (x + y) = nn2real x + nn2real y"
  by transfer simp

lemma nn2real_mult[simp]: "nn2real (x * y) = nn2real x * nn2real y"
  by transfer simp

lemma nn2real_minus[simp]:
  "nn2real (x - y) = max 0 (nn2real x - nn2real y)"
  by transfer simp

lemma nn2real_inverse[simp]: "nn2real (inverse x) = inverse (nn2real x)"
  by transfer simp

lemma nn2real_divide[simp]: "nn2real (x / y) = nn2real x / nn2real y"
  by transfer simp

lemma nn2real_numeral[simp]: "nn2real (numeral n) = numeral n"
  by (induct n) (simp_all only: numeral.simps nn2real_1 nn2real_add)

lemma nn2real_eq_transfer_aux[transfer_rule]:
  "Transfer.Rel (rel_fun (=) (rel_fun pcr_nnreal (=))) (\<lambda>x y. nn2real x = y) (=)"
  by (smt (verit) Rel_def cr_nnreal_def nn2real_eq_iff nnreal.pcr_cr_eq
      rel_funI)

lemma real2nn_0[simp]: "real2nn 0 = 0"
  apply transfer_start
      apply transfer_step
     apply transfer_step
    apply transfer_step
  apply (rule nn2real_eq_transfer_aux)
  apply transfer_end
  by simp

lemma real2nn_1[simp]: "real2nn 1 = 1"
  apply transfer_start
      apply transfer_step
     apply transfer_step
    apply transfer_step
  apply (rule nn2real_eq_transfer_aux)
  apply transfer_end
  by simp

lemma real2nn_add[simp]:
  assumes "0 \<le> x" "0 \<le> y"
  shows "real2nn (x + y) = real2nn x + real2nn y"
  by (metis assms(1,2) nn2real_add nn2real_real2nn real2nn_nn2real)

lemma real2nn_mult[simp]:
  assumes "0 \<le> x" "0 \<le> y"
  shows "real2nn (x * y) = real2nn x * real2nn y"
  by (simp add: assms(1,2) times_nnreal_def)

subsection \<open>Conversions from natural numbers\<close>

lift_definition nnreal :: "nat \<Rightarrow> nnreal" is of_nat by linarith

parametric_constant of_nat_transfer[transfer_rule]: of_nat_def

lemma nn2real_nnreal[simp]: "nn2real (nnreal n) = real n"
  by transfer simp

lemma real2nn_eq_transfer_aux[transfer_rule]:
  "Transfer.Rel (rel_fun pcr_nnreal (rel_fun (=) (=))) (\<lambda>y x. x = real2nn y) (=)"
  by (smt (verit) Rel_abs Rel_def cr_nnreal_def nnreal.pcr_cr_eq
      real2nn_nn2real)

lemma nnreal_of_nat[simp]: "nnreal n = of_nat n"
  by transfer simp

lemma nnreal_leq_simp[simp]: "nnreal x \<le> nnreal y \<longleftrightarrow> x \<le> y"
  by transfer simp

lemma nnreal_less_simp[simp]: "nnreal x < nnreal y \<longleftrightarrow> x < y"
  by transfer simp

lemma nnreal_0[simp]: "nnreal 0 = 0"
  by transfer simp

lemma nnreal_Suc[simp]: "nnreal (Suc n) = nnreal n + 1"
  by transfer simp

lemma nnreal_eq_0_iff[simp]: "nnreal n = 0 \<longleftrightarrow> n = 0"
  by transfer simp


subsection \<open>Arithmetic simp rules\<close>

lemma zero_least[simp]: "0 \<le> (x::nnreal)"
  by transfer simp

lemma zero_less_iff_neq_zero[simp]: "0 < (x::nnreal) \<longleftrightarrow> x \<noteq> 0"
  using zero_least[of x] by (auto simp: le_less)

lemma nnreal_add_eq_0_iff[simp]:
  "(x + y = 0) \<longleftrightarrow> x = 0 \<and> y = (0::nnreal)"
  by transfer auto

lemma nnreal_mult_eq_0_iff[simp]:
  "(x * y = 0) \<longleftrightarrow> x = 0 \<or> y = (0::nnreal)"
  by transfer auto

lemma div_one_nnreal[simp]: "(p::nnreal) / 1 = p"
  by transfer simp

lemma divide_self: "(a::nnreal) \<noteq> 0 \<Longrightarrow> a / a = 1"
  by transfer simp

lemma times_div_1:
  assumes "x \<noteq> 0"
  shows "x * (1 / x) = (1::nnreal)"
  using assms by transfer simp

lemma zero_div[simp]: "0 / (q::nnreal) = 0"
  by transfer simp

lemma divide_eq_0_nnreal[simp]:
  "((a::nnreal) / q = 0) \<longleftrightarrow> a = 0 \<or> q = 0"
  by transfer auto

lemma add_divide_nnreal:
  "((a::nnreal) + b) / q = a / q + b / q"
  by transfer (simp add: add_divide_distrib)

lemma minus_nnreal_code[code]:
  "nn2real (x - y) = (if x \<ge> y then nn2real x - nn2real y else 0)"
  by transfer auto


subsection \<open>Finite sums\<close>

lemma fsum_fset_sum:
  "fsum f A = (\<Sum>x\<in>fset A. f x)"
  unfolding fsum_def apply transfer
  by (metis fsum.F.rep_eq fsum_def)

lemma fsum_divide_nnreal:
  "fsum (\<lambda>x. f x / q) A = fsum f A / (q::nnreal)"
proof (induct A)
  case empty
  show ?case
    by (simp add: fsum_fset_sum)
next
  case (insert x A)
  then show ?case
    by (simp add: fsum_fset_sum add_divide_nnreal)
qed

lemma sum_divide_nnreal:
  assumes "finite A"
  shows "(\<Sum>x\<in>A. f x / (q::nnreal)) = (\<Sum>x\<in>A. f x) / q"
  using assms
proof induct
  case empty
  show ?case by simp
next
  case (insert x A)
  then show ?case
    by (simp add: add_divide_nnreal)
qed

lemma fsum_mult_left_nnreal:
  "fsum (\<lambda>x. (c::nnreal) * f x) A = c * fsum f A"
  unfolding fsum_fset_sum
  by (simp add: sum_distrib_left)

lemma sum_constant_nnreal:
  assumes "finite S"
  shows "(\<Sum>x\<in>S. c) = nnreal (card S) * (c::nnreal)"
  using assms
proof induction
  case empty
  show ?case by simp
next
  case (insert x S)
  then show ?case
    by (simp add: algebra_simps)
qed

lemma sum_1_nnreal:
  assumes "finite S"
  shows "(\<Sum>x\<in>S. (1::nnreal)) = nnreal (card S)"
  using assms
proof induction
  case empty
  show ?case by simp
next
  case (insert x S)
  then show ?case by (simp add: Groups.add_ac(2))
qed

end
