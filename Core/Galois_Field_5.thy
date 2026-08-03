(*  Title:      Stark/Galois_Field_5.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Galois_Field_5
  imports "HOL-Number_Theory.Number_Theory"
    "HOL-Library.Cardinality"
    "Berlekamp_Zassenhaus.Finite_Field"
begin

section \<open>The Field GF(5)\<close>

text \<open>
  This theory provides a small executable finite field instance used by the
  square-sequence example.  The instance is intentionally small so that example
  proof generation and verification remain feasible inside Isabelle.
\<close>

typedef gf5 = "{0 .. 4 :: int}"
  by auto

setup_lifting type_definition_gf5

lift_definition gf5_0:: gf5
is 0 by simp

lift_definition gf5_1:: gf5
is 1 by simp

lift_definition gf5_2:: gf5
is 2 by simp

lift_definition gf5_3:: gf5
is 3 by simp

lift_definition gf5_4:: gf5
is 4 by simp

lemma [simp]: "gf5_0 \<noteq> gf5_1"
  by transfer simp

lemma [simp]: "gf5_0 \<noteq> gf5_2"
  by transfer simp

lemma [simp]: "gf5_0 \<noteq> gf5_3"
  by transfer simp

lemma [simp]: "gf5_0 \<noteq> gf5_4"
  by transfer simp

lemma [simp]: "gf5_1 \<noteq> gf5_2"
  by transfer simp

lemma [simp]: "gf5_1 \<noteq> gf5_3"
  by transfer simp

lemma [simp]: "gf5_1 \<noteq> gf5_4"
  by transfer simp

lemma [simp]: "gf5_2 \<noteq> gf5_3"
  by transfer simp

lemma [simp]: "gf5_2 \<noteq> gf5_4"
  by transfer simp

lemma [simp]: "gf5_3 \<noteq> gf5_4"
  by transfer simp

instantiation gf5 :: field
begin
lift_definition zero_gf5 :: "gf5" is "0" by auto
lift_definition one_gf5 :: "gf5" is "1" by auto
lift_definition uminus_gf5 :: "gf5 \<Rightarrow> gf5" is "\<lambda>x. (5 - x) mod 5" by auto
lift_definition plus_gf5 :: "gf5 \<Rightarrow> gf5 \<Rightarrow> gf5" is "\<lambda>x y. (x + y) mod 5" by auto
definition minus_gf5 :: "gf5 \<Rightarrow> gf5 \<Rightarrow> gf5" where "minus_gf5 x y = (x + (uminus y))"
lift_definition times_gf5 :: "gf5 \<Rightarrow> gf5 \<Rightarrow> gf5" is "\<lambda>x y. (x * y) mod 5" by auto
lift_definition inverse_gf5 :: "gf5 \<Rightarrow> gf5" is "\<lambda>x. if x = 2 then 3 else if x = 3 then 2 else x" by auto
definition divide_gf5 :: "gf5 \<Rightarrow> gf5 \<Rightarrow> gf5" where "divide_gf5 x y = (x * inverse y)"

instance
  apply standard
              apply (transfer, simp add: mod_mult_left_eq mod_mult_right_eq mult.assoc)
             apply (transfer, simp add: mult.commute)
            apply (transfer, simp)
           apply (transfer, presburger)
          apply (transfer, presburger)
         apply (transfer, simp)
        apply (transfer, presburger)
       apply (simp add: minus_gf5_def)
      apply (transfer, simp add: distrib_right mod_add_eq mod_mult_left_eq)
     apply (transfer, simp)
    apply (transfer, (case_tac "a=1"; auto), (case_tac "a=4"; auto))
   apply (simp add: divide_gf5_def)
  by (transfer, presburger)
end

lift_definition to_nat::"gf5 \<Rightarrow> nat"
is nat .

lift_definition of_nat::"nat \<Rightarrow> gf5"
is "\<lambda>x::nat. int (x mod 5)" by auto

lemma of_nat_to_nat[simp]: "of_nat (to_nat  x) = x"
  apply transfer by fastforce

lemma gf5_cases[cases type:gf5]:
  fixes x::gf5
  obtains
   "x = gf5_0" | "x = gf5_1" | "x = gf5_2" | "x = gf5_3"  | "x = gf5_4"
  apply transfer
  by fastforce

lemma gf5_Univ: "(UNIV::gf5 set) = {gf5_0,gf5_1,gf5_2,gf5_3,gf5_4}"
  using gf5_cases by blast

instantiation gf5 :: enum
begin

definition enum_gf5 :: "gf5 list"
  where "enum_gf5 = [gf5_0, gf5_1, gf5_2, gf5_3, gf5_4]"

definition enum_all_gf5 :: "(gf5 \<Rightarrow> bool) \<Rightarrow> bool"
  where "enum_all_gf5 P \<equiv> P gf5_0 \<and> P gf5_1 \<and> P gf5_2 \<and> P gf5_3 \<and> P gf5_4"

definition enum_ex_gf5 :: "(gf5 \<Rightarrow> bool) \<Rightarrow> bool"
  where "enum_ex_gf5 P \<equiv> P gf5_0 \<or> P gf5_1 \<or> P gf5_2 \<or> P gf5_3 \<or> P gf5_4"

instance
  apply (standard)
  by (auto simp add: gf5_Univ enum_gf5_def enum_all_gf5_def enum_ex_gf5_def)
end

instance gf5 :: finite_field
proof
  interpret type_definition Rep_gf5 Abs_gf5 "{0 .. 4 :: int}"
    by (rule type_definition_gf5)
  show "finite (UNIV :: gf5 set)"
    by simp
qed

instantiation gf5 :: equal
begin
lift_definition equal_gf5 :: "gf5 \<Rightarrow> gf5 \<Rightarrow> bool"
is "(=)" parametric eq_transfer .

instance
  by (standard) (transfer, simp)
end

lemma card_5_iff: "card S = 5 \<longleftrightarrow> (\<exists>v w x y z. S = {v,w,x,y,z}
  \<and> v \<noteq> w \<and> v \<noteq> x \<and> v \<noteq> y \<and> v \<noteq> z
  \<and> w \<noteq> x \<and> w \<noteq> y \<and> w \<noteq> z
  \<and> x \<noteq> y \<and> x \<noteq> z
  \<and> y \<noteq> z)"
  by (fastforce simp: card_Suc_eq numeral_eq_Suc)

lemma gf5_size[simp]: "CARD (gf5) = 5"
proof -
  have "(\<exists>v w x y z. {gf5_0, gf5_1, gf5_2, gf5_3, gf5_4} = {v, w, x, y, z} \<and> v \<noteq> w \<and> v \<noteq> x \<and> v \<noteq> y \<and> v \<noteq> z \<and> w \<noteq> x \<and> w \<noteq> y \<and> w \<noteq> z \<and> x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z)"
    by (metis gf5_0.rep_eq gf5_1.rep_eq gf5_2.rep_eq gf5_3.rep_eq gf5_4.rep_eq numeral_eq_iff numeral_eq_one_iff semiring_norm(85) verit_eq_simplify(12,14,8) zero_neq_numeral)
  then show ?thesis using card_5_iff gf5_Univ by fastforce
qed

text \<open>Proth numbers: \<^url>\<open>https://en.wikipedia.org/wiki/Proth_prime\<close>, they are useful for FTTs\<close>

class proth = finite +
  assumes proth_card: "\<exists>k n. CARD('a) = k * 2^n + 1"

class proth_field = finite_field + proth + prime_card


instantiation gf5::proth_field
begin
instance proof
  show "normalization_semidom_class.prime CARD(gf5)" by simp
next
  show "\<exists>k n. CARD(gf5) = k * 2 ^ n + 1"
  apply (simp)
  by (metis power_even_eq power2_eq_square numeral_Bit0_eq_double)
qed

end

lemma gen_2_gf5:
  fixes x::gf5
  assumes "x \<noteq> gf5_0"
  shows "\<exists>i. gf5_2 ^ i = x"
proof (cases x)
  case 1
  with assms show ?thesis by satx
next
  case 2
  then show ?thesis
    by (metis gf5_1_def one_gf5_def power_0)
next
  case 3
  then show ?thesis
    by (meson power_Suc0_right)
next
  case 4
  moreover have "gf5_2 * gf5_2 * gf5_2 = gf5_3"
    by transfer simp
  moreover have "((gf5_2::gf5)^3) = gf5_2 * gf5_2 * gf5_2"
    by (rule power3_eq_cube)
  ultimately show ?thesis by metis
next
  case 5
  moreover have "gf5_2 * gf5_2 = gf5_4"
    by transfer simp
  moreover have "((gf5_2::gf5)^2) = gf5_2 * gf5_2"
    by (rule power2_eq_square)
  ultimately show ?thesis by metis
qed

lemma "to_nat (0::gf5) = 0" by eval
lemma "to_nat (1::gf5) = 1" by eval
lemma "to_nat (2::gf5) = 2" by eval
lemma "to_nat (7::gf5) = 2" by eval
lemma "((of_nat 0)::gf5) = 0" by eval
lemma "((of_nat 1)::gf5) = 1" by eval
lemma "((of_nat 2)::gf5) = 2" by eval
lemma "((of_nat 3)::gf5) = 3" by eval

lemma gf5_0: "0 = gf5_0" apply transfer by presburger

end
