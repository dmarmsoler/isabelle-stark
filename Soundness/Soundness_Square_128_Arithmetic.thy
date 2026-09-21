(* Title: Stark/Soundness_Square_128_Arithmetic.thy
   License: BSD-3-Clause *)

theory Soundness_Square_128_Arithmetic
  imports Complex_Main
begin

section \<open>Small arithmetic certificate for the approved target\<close>

text \<open>These HOL arithmetic facts support the fixed 640-query, total-budget
  at-most two-to-the-twentieth profile. The dyadic estimate is a conservative
  intermediate for this target only, not a change to the exact modulo sampler
  or source error. The next layer must connect every numeral to that source.
  No diagnostic file or external arithmetic oracle is trusted.\<close>

lemma square_128_dyadic_block:
  "(27/32::real)^128 \<le> 1/2^31"
  by (simp add: power_divide)

lemma square_128_dyadic_power:
  fixes x :: real
  assumes nonneg: "0 \<le> x" and bound: "x \<le> 27/32"
  shows "x^640 \<le> 1/2^155"
proof -
  have block: "x^128 \<le> 1/2^31"
    by (rule order_trans[OF power_mono[OF bound nonneg] square_128_dyadic_block])
  have "(x^128)^5 \<le> (1/2^31::real)^5"
    by (rule power_mono[OF block]) (use nonneg in auto)
  then show ?thesis
    by (simp add: power_mult[symmetric] power_divide)
qed

lemma square_128_sampling:
  fixes p1 p2 :: real
  assumes bounds: "0 \<le> p1" "p1 \<le> 27/32" "0 \<le> p2" "p2 \<le> 27/32"
  shows "2305636*(p1^640 + 2*p2^640) \<le> 1/2^132"
proof -
  have p1: "p1^640 \<le> 1/2^155"
    by (rule square_128_dyadic_power[OF bounds(1,2)])
  have p2: "p2^640 \<le> 1/2^155"
    by (rule square_128_dyadic_power[OF bounds(3,4)])
  have scaled: "(2305636::real)*(1/2^155 + 2*(1/2^155)) \<le> 1/2^132"
    by simp
  show ?thesis using p1 p2 scaled by argo
qed

lemma square_128_nonsampling:
  "(68662639825042::real) /
    3531942672373065915328229302366199208109272268385770536961 \<le> 1/2^144"
  by simp

lemma square_128_total:
  "(1/2^132::real) + 1/2^144 \<le> 1/2^128"
  by simp
ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
    then ()
    else error "Unexpected arithmetic certificate dependency")
    @{thms square_128_dyadic_block square_128_dyadic_power square_128_sampling
      square_128_nonsampling square_128_total};
\<close>
end
