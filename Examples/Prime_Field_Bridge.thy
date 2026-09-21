(*  Title:      Stark/Prime_Field_Bridge.thy
    License:    BSD-3-Clause
*)

theory Prime_Field_Bridge
  imports Stark_Core.Stark "HOL-Number_Theory.Residue_Primitive_Roots"
begin

section \<open>Prime-field instantiation infrastructure\<close>

text \<open>These facts discharge existing field, encoding and domain obligations.
  They do not interpret a computation specification, select a numerical field
  or generator, or certify a concrete soundness target. The residue-field
  arithmetic is reused from the AFP rather than redefined.\<close>

subsection \<open>Field class and canonical encodings\<close>

text \<open>The existing proth class permits exponent zero; its class predicate alone
  does not supply a nontrivial power-of-two factor of the field size minus one.
  The required evaluation-domain divisibility remains an explicit arithmetic
  obligation, discharged separately in any later interpretation.\<close>

instance mod_ring :: (prime_card) proth_field
proof (intro_classes)
  show "prime CARD('a mod_ring)" by (simp add: prime_card)
next
  have eq: "CARD('a) - 1 + 1 = CARD('a)"
    using nontriv[where 'a='a] by arith
  show "\<exists>k n. CARD('a mod_ring) = k * 2^n + 1"
    by (rule exI[of _ "CARD('a)-1"], rule exI[of _ 0])
      (simp only: CARD_mod_ring power_0 mult.right_neutral eq)
qed

definition stark_mod_ring_decode :: "'a::prime_card mod_ring \<Rightarrow> nat"
  where "stark_mod_ring_decode x = nat (to_int_mod_ring x)"

definition stark_mod_ring_encode :: "nat \<Rightarrow> 'a::prime_card mod_ring"
  where "stark_mod_ring_encode n = of_int_mod_ring (int n)"

lemma stark_mod_ring_encode_decode [simp]:
  "stark_mod_ring_encode (stark_mod_ring_decode x) = x"
  unfolding stark_mod_ring_encode_def stark_mod_ring_decode_def
  using to_int_mod_ring.rep_eq[of x] Rep_mod_ring[of x]
    of_int_mod_ring_to_int_mod_ring[of x] by auto

lemma stark_mod_ring_decode_encode:
  assumes "n < CARD('a::prime_card)"
  shows "stark_mod_ring_decode (stark_mod_ring_encode n :: 'a mod_ring) = n"
  using assms unfolding stark_mod_ring_decode_def stark_mod_ring_encode_def
  by (simp add: of_nat_of_int_mod_ring)

lemma stark_mod_ring_decode_less:
  fixes x :: "'a::prime_card mod_ring"
  shows "stark_mod_ring_decode x < CARD('a)"
  unfolding stark_mod_ring_decode_def
  using Rep_mod_ring[of x] to_int_mod_ring.rep_eq[of x] by auto

lemma stark_mod_ring_decode_range:
  "range (stark_mod_ring_decode :: 'a::prime_card mod_ring \<Rightarrow> nat) = {0..<CARD('a)}"
proof (rule equalityI)
  show "range (stark_mod_ring_decode :: 'a mod_ring \<Rightarrow> nat) \<subseteq> {0..<CARD('a)}"
    using stark_mod_ring_decode_less[where 'a='a] by auto
next
  show "{0..<CARD('a)} \<subseteq> range (stark_mod_ring_decode :: 'a mod_ring \<Rightarrow> nat)"
  proof (rule subsetI)
    fix n assume "n \<in> {0..<CARD('a)}"
    then have "stark_mod_ring_decode (stark_mod_ring_encode n :: 'a mod_ring) = n"
      by (simp add: stark_mod_ring_decode_encode)
    then show "n \<in> range (stark_mod_ring_decode :: 'a mod_ring \<Rightarrow> nat)"
      by (metis rangeI)
  qed
qed

subsection \<open>Full multiplicative generator from modular primitive roots\<close>

text \<open>The library's prime-cardinality assumption provides primitive-root
  existence. The congruence bridge below transports both the order equation
  and the absence of smaller positive orders to the existing @{const exact_order}
  definition. It does not mistake a root for the evaluation domain alone for
  a generator of the full multiplicative group.\<close>

lemma stark_mod_ring_power_cong:
  "(of_int_mod_ring (int a) :: 'a::prime_card mod_ring)^m = 1 \<longleftrightarrow>
    [a^m = 1] (mod CARD('a))"
  by transfer
    (metis (mono_tags, lifting) cong_def cong_int_iff of_nat_1 of_nat_power
      one_mod_card_int power_mod)

lemma stark_mod_ring_primitive_root_order:
  assumes root: "residue_primroot CARD('a::prime_card) a"
  shows "exact_order (of_int_mod_ring (int a) :: 'a mod_ring) (CARD('a)-1)"
proof -
  have order: "ord CARD('a) a = CARD('a)-1"
    using root prime_card[where 'a='a]
    by (simp add: residue_primroot_def totient_prime)
  have positive: "0 < CARD('a)-1" using nontriv[where 'a='a] by arith
  have power: "(of_int_mod_ring (int a) :: 'a mod_ring)^(CARD('a)-1) = 1"
    unfolding stark_mod_ring_power_cong using ord[of a "CARD('a)"] order by simp
  have minimal: "(of_int_mod_ring (int a) :: 'a mod_ring)^m \<noteq> 1"
    if "0<m" "m<CARD('a)-1" for m
    unfolding stark_mod_ring_power_cong using ord_minimal[of m "CARD('a)" a] order that
    by presburger
  show ?thesis unfolding exact_order_def using positive power minimal by blast
qed

theorem stark_mod_ring_full_generator_exists:
  "\<exists>omega :: 'a::prime_card mod_ring. exact_order omega (CARD('a)-1)"
proof -
  obtain a where "residue_primroot CARD('a) a"
    using prime_primitive_root_exists[OF nontriv[where 'a='a] prime_card[where 'a='a]] by blast
  then show ?thesis using stark_mod_ring_primitive_root_order[where 'a='a] by blast
qed

subsection \<open>Divisor-order roots and a proper shifted domain\<close>

text \<open>These helper lemmas are available before interpreting the STARK locale.
  Their divisor-order argument follows the same power calculation as the
  existing trace- and evaluation-domain order proofs within that locale.\<close>

lemma stark_exact_order_nonzero:
  fixes omega :: "'f::field"
  assumes "exact_order omega M"
  shows "omega \<noteq> 0"
  using assms unfolding exact_order_def by (cases M) auto

lemma stark_exact_order_divisor:
  fixes omega :: "'f::field"
  assumes order: "exact_order omega M" and D: "0<D" "D dvd M"
  shows "exact_order (omega^(M div D)) D"
proof -
  obtain q where M: "M=D*q" using D(2) unfolding dvd_def by blast
  have q: "0<q" using order M unfolding exact_order_def by (cases q) auto
  have division: "M div D = q" using M D(1) by simp
  have power: "(omega^(M div D))^D=1"
    using order M division unfolding exact_order_def
    by (simp add: power_mult[symmetric] mult.commute)
  have minimal: "(omega^(M div D))^m \<noteq> 1" if "0<m" "m<D" for m
  proof -
    have positive: "0<q*m" using q that by simp
    have smaller: "q*m<M" using q that M by (simp add: mult_less_mono2)
    show ?thesis using order positive smaller division
      unfolding exact_order_def by (simp add: power_mult[symmetric])
  qed
  show ?thesis unfolding exact_order_def using D(1) power minimal by blast
qed

lemma stark_full_generator_outside_subgroup:
  fixes omega :: "'f::field"
  assumes order: "exact_order omega M" and D: "0<D" "D dvd M" "D<M"
  shows "omega \<notin> set (map ((^) (omega^(M div D))) [0..<D])"
proof (rule notI)
  assume member: "omega \<in> set (map ((^) (omega^(M div D))) [0..<D])"
  obtain i where i: "omega=(omega^(M div D))^i" using member by auto
  have power: "(omega^(M div D))^D=1"
    using stark_exact_order_divisor[OF order D(1,2)]
    unfolding exact_order_def by blast
  have "omega^D=((omega^(M div D))^D)^i"
    using i
    by (metis power_mult[symmetric] mult.commute)
  also have "...=1" using power by simp
  finally show False using order D(1,3) unfolding exact_order_def by blast
qed

lemma stark_mod_ring_two_nonzero:
  assumes "2<CARD('a::prime_card)"
  shows "(2::'a mod_ring) \<noteq> 0"
proof (rule notI)
  assume zero: "(2::'a mod_ring)=0"
  have "CARD('a) dvd 2"
    using of_nat_0_mod_ring_dvd[of 2, where 'a='a] zero by simp
  then show False using assms by (auto dest: dvd_imp_le)
qed

lemma stark_mod_ring_degree_decode:
  assumes degree: "max_degree<CARD('a::prime_card)" and n: "n\<le>max_degree"
  shows "stark_mod_ring_decode (stark_mod_ring_encode n :: 'a mod_ring) = n"
  by (rule stark_mod_ring_decode_encode) (use degree n in arith)

text \<open>Write F for the common cardinality of the index type and its residue
  field. For a nontrivial proper divisor D of F minus one, the witness supplies
  a full generator and a root of exact order D. Choosing the full generator
  itself as the shift gives a nonzero element outside that root subgroup.
  These arithmetic conditions are hypotheses to discharge, not new assumptions
  on the verifier or public soundness theorem. Characteristic two is not
  silently admitted to this domain construction.\<close>

theorem stark_mod_ring_domain_witness:
  assumes domain: "1<D" "D dvd CARD('a::prime_card)-1" "D<CARD('a)-1"
  obtains omega :: "'a::prime_card mod_ring"
    where "exact_order omega (CARD('a)-1)"
      and "omega \<noteq> 0"
      and "(2::'a mod_ring) \<noteq> 0"
      and "exact_order (omega^((CARD('a)-1) div D)) D"
      and "omega \<notin> set (map ((^) (omega^((CARD('a)-1) div D))) [0..<D])"
proof -
  obtain omega :: "'a mod_ring" where order: "exact_order omega (CARD('a)-1)"
    using stark_mod_ring_full_generator_exists[where 'a='a] by blast
  have positive: "0<D" using domain by arith
  have two: "(2::'a mod_ring) \<noteq> 0"
    by (rule stark_mod_ring_two_nonzero) (use domain in arith)
  show thesis
    by (rule that[OF order stark_exact_order_nonzero[OF order] two
          stark_exact_order_divisor[OF order positive domain(2)]
          stark_full_generator_outside_subgroup[OF order positive domain(2,3)]])
qed

subsection \<open>Small boundary and nonvacuity regressions\<close>

text \<open>The generator result also covers characteristic two, where two is zero.
  A separate proper-domain witness uses the existing GF(5) cardinality type.
  Neither regression constitutes a cryptographic parameter interpretation.\<close>

lemma stark_mod_ring_characteristic_two_regression:
  "exact_order (1::bool mod_ring) 1 \<and> (2::bool mod_ring)=0"
  unfolding exact_order_def
  using of_nat_card_eq_0[where 'a=bool]
  by auto

lemma stark_mod_ring_proper_domain_regression:
  "\<exists>omega::gf5 mod_ring. exact_order omega 4 \<and> omega\<noteq>0 \<and>
    omega \<notin> set (map ((^) (omega^2)) [0..<2])"
  using stark_mod_ring_domain_witness[where 'a=gf5 and D=2] by auto

end
