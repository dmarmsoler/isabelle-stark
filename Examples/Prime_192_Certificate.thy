(*  Title:      Stark/Prime_192_Certificate.thy
    License:    BSD-3-Clause
*)

theory Prime_192_Certificate
  imports Prime_192_Replay "HOL-Number_Theory.Pocklington"
begin

section \<open>Pocklington certificate for the concrete field cardinality\<close>

text \<open>The factored part of F minus one is 2 to the power 128. Its only prime
  divisor is two, and its square exceeds F. Thus the certificate needs no
  factorization of the odd cofactor. Subtraction below is natural subtraction:
  positivity of the reduced half-power is proved before transferring the
  predecessor coprimality through congruence.\<close>

lemma reduced_predecessor_coprime:
  fixes h n :: nat
  assumes residue: "h mod n \<noteq> 0" and coprime: "coprime (h mod n - 1) n"
  shows "coprime (h-1) n"
proof -
  have bounds: "1 \<le> h mod n" "1 \<le> h"
    using residue mod_less_eq_dividend[of h n] by arith+
  have congruence: "[h mod n - 1 = h-1] (mod n)"
    by (rule cong_diff_nat) (use bounds in \<open>simp_all add: cong_def\<close>)
  show ?thesis using congruence coprime by (rule cong_imp_coprime)
qed

lemma pocklington_power_two_residue:
  fixes n a k m :: nat
  assumes n: "2 \<le> n" and factor: "n-1=2^m*k" and size: "n\<le>(2^m)^2"
    and full: "mod_exp a (n-1) n = 1"
    and half: "mod_exp a ((n-1) div 2) n \<noteq> 0"
    and gcd: "coprime (mod_exp a ((n-1) div 2) n - 1) n"
  shows "prime n"
proof -
  have congruence: "[a^(n-1)=1] (mod n)"
    using full n by (simp add: cong_def mod_exp_def)
  have predecessor: "coprime (a^((n-1) div 2)-1) n"
    by (rule reduced_predecessor_coprime)
      (use half gcd in \<open>simp_all add: mod_exp_def\<close>)
  show ?thesis
  proof (rule pocklington[OF n factor size congruence])
    show "\<forall>p. prime p \<and> p dvd 2^m \<longrightarrow> coprime (a^((n-1) div p)-1) n"
    proof (intro allI impI)
      fix p :: nat assume p: "prime p \<and> p dvd 2^m"
      have dvd2: "p dvd 2" using p by (blast dest: prime_dvd_power)
      have lower: "1<p" using p prime_gt_1_nat by blast
      have upper: "p\<le>2" using dvd2 by (auto dest: dvd_imp_le)
      have "p=2" using lower upper by linarith
      thus "coprime (a^((n-1) div p)-1) n" using predecessor by simp
    qed
  qed
qed

lemma mod_exp_double:
  "mod_exp (a::nat) (e*2) n = (mod_exp a e n)^2 mod n"
  by (simp add: mod_exp_def power_mult power_mod)


definition certificate_prime_192 :: nat
  where "certificate_prime_192 =
    3531942672373065915328229302366199208109272268385770536961"

method_setup certificate_bounded_simp = \<open>
  Scan.lift Parse.nat >> (fn seconds => fn ctxt =>
    SIMPLE_METHOD (fn st =>
      (case Timeout.apply (Time.fromSeconds seconds)
        (Seq.pull o ALLGOALS (asm_full_simp_tac ctxt)) st of
        NONE => Seq.empty | SOME (result,_) => Seq.single result)))
\<close>

context
begin

declare gcd_non_0_nat [simp]

lemma certificate_prime_192_coprime:
  "coprime (certificate_prime_192-1-1) certificate_prime_192"
  unfolding certificate_prime_192_def coprime_iff_gcd_eq_1
  using [[simp_depth_limit=100]]
  by (certificate_bounded_simp 30)

end

text \<open>Reconstruct the complete original modular-power equality. The numerical
  audit files are not loaded or trusted. The replay checks all recurrence
  steps, the exponent expression, both terminal cases and the outer modulo.
  The full-power condition below reuses this half-power proof.\<close>

ML \<open>val prime_192_half_power_result = run_full_half_power ();\<close>

local_setup \<open>fn lthy =>
  snd (Local_Theory.note
    ((Binding.name "certificate_half_power_192", []), [prime_192_half_power_result]) lthy)\<close>

local_setup \<open>fn lthy =>
  let
    val (_, facts) = Prime_192_Replay_Arithmetic.mulmod "full_power_reuse" (Prime_192_Replay_Arithmetic.p-1) (Prime_192_Replay_Arithmetic.p-1);
  in snd (Local_Theory.note ((Binding.name "predecessor_square_facts", []), facts) lthy) end\<close>

lemma certificate_full_power_192:
  "mod_exp 13 (certificate_prime_192-1) certificate_prime_192=1"
proof -
  have exponent: "certificate_prime_192-1 = ((certificate_prime_192-1) div 2)*2"
    by (simp add: certificate_prime_192_def)
  have half: "mod_exp 13 ((certificate_prime_192-1) div 2) certificate_prime_192 =
      certificate_prime_192-1"
    unfolding certificate_prime_192_def by (rule certificate_half_power_192)
  have predecessor: "certificate_prime_192-1 =
      3531942672373065915328229302366199208109272268385770536960"
    by (simp add: certificate_prime_192_def)
  have square: "(certificate_prime_192-1)^2 mod certificate_prime_192=1"
    by (simp only: predecessor; simp only: certificate_prime_192_def power2_eq_square predecessor_square_facts)
  show ?thesis
    by (subst exponent, subst mod_exp_double) (simp only: half square)
qed

theorem certificate_prime_192_is_prime:
  "prime certificate_prime_192"
proof (rule pocklington_power_two_residue[where a=13 and m=128 and k=10379446647006781035])
  show "2 \<le> certificate_prime_192" by (simp add: certificate_prime_192_def)
  show "certificate_prime_192-1 = 2^128*10379446647006781035"
    by (simp add: certificate_prime_192_def)
  show "certificate_prime_192 \<le> (2^128)^2" by (simp add: certificate_prime_192_def)
  show "mod_exp 13 (certificate_prime_192-1) certificate_prime_192=1"
    by (rule certificate_full_power_192)
  show "mod_exp 13 ((certificate_prime_192-1) div 2) certificate_prime_192 \<noteq> 0"
    by (simp only: certificate_prime_192_def certificate_half_power_192; simp)
  show "coprime (mod_exp 13 ((certificate_prime_192-1) div 2) certificate_prime_192 - 1) certificate_prime_192"
    using certificate_prime_192_coprime
    by (simp only: certificate_prime_192_def certificate_half_power_192)
qed

ML \<open>Prime_192_Replay_Arithmetic.inspect "primality theorem" @{thm certificate_prime_192_is_prime};\<close>

end
