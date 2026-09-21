theory FS_Square_135_Arithmetic
 imports Complex_Main
begin

section \<open>Arithmetic certificate for the refined conventional-query bound\<close>

text \<open>Small exact rational blocks bound 640 unchanged modulo samples.
  The final inequality uses the complete refined ledger at Q equal to two
  to the twentieth. All arithmetic is kernel-checked; external diagnostics
  are not proof inputs. The source connection is established separately.\<close>

lemma fs_135_block:
 "(68/81::real)^16 \<le> 125/2048"
 by (simp add: power_divide)

lemma fs_135_blocks:
 "(125/2048::real)^40 \<le> 2/(5*2^160)"
 by (simp add: power_divide)

lemma fs_135_power:
 fixes x :: real
 assumes nonneg: "0\<le>x" and bound: "x\<le>68/81"
 shows "x^640\<le>2/(5*2^160)"
proof -
 have block: "x^16\<le>125/2048"
  by (rule order_trans[OF power_mono[OF bound nonneg] fs_135_block])
 have "(x^16)^40\<le>(125/2048::real)^40"
  by (rule power_mono[OF block]) (use nonneg in auto)
 then show ?thesis using fs_135_blocks by (simp add: power_mult[symmetric])
qed

lemma fs_135_rational_target:
 "(149531366400678730::real)/(2*3531942672373065915328229302366199208109272268385770536961) +
  1963186*(2/(5*2^160)+2*(2/(5*2^160))) \<le> 1/2^135"
 by simp

lemma fs_135_total:
 fixes p1 p2 :: real
 assumes bounds: "0\<le>p1" "p1\<le>68/81" "0\<le>p2" "p2\<le>68/81"
 shows "(149531366400678730::real)/(2*3531942672373065915328229302366199208109272268385770536961) +
   1963186*(p1^640+2*p2^640) \<le> 1/2^135"
 using fs_135_power[OF bounds(1,2)] fs_135_power[OF bounds(3,4)] fs_135_rational_target
 by argo

ML \<open>
 List.app (fn th =>
   if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
   then () else error "Unexpected refined numerical dependency")
   @{thms fs_135_block fs_135_blocks fs_135_power fs_135_rational_target fs_135_total};
\<close>
end
