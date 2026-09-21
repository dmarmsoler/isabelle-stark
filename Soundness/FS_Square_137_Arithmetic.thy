theory FS_Square_137_Arithmetic
 imports FS_Square_135_Arithmetic
begin

section \<open>Arithmetic certificate for the prefix-refined conventional FS bound\<close>

text \<open>Reuse the existing exact 640-sample power bound. Only the complete
  nonsampling numerator changes. The rational target is kernel-checked;
  external decimal estimates and threshold searches are not proof inputs.\<close>

lemma fs_137_rational_target:
 "(14268787487890250::real)/(2*3531942672373065915328229302366199208109272268385770536961) +
  1963186*(2/(5*2^160)+2*(2/(5*2^160))) \<le> 1/2^137"
 by simp

lemma fs_137_total:
 fixes p1 p2 :: real
 assumes bounds: "0\<le>p1" "p1\<le>68/81" "0\<le>p2" "p2\<le>68/81"
 shows "(14268787487890250::real)/(2*3531942672373065915328229302366199208109272268385770536961) +
   1963186*(p1^640+2*p2^640) \<le> 1/2^137"
 using fs_135_power[OF bounds(1,2)] fs_135_power[OF bounds(3,4)] fs_137_rational_target
 by argo

ML \<open>
 List.app (fn th =>
   if null (Thm.hyps_of th) andalso null (Thm_Deps.all_oracles [th])
   then () else error "Unexpected prefix numerical dependency")
   @{thms fs_137_rational_target fs_137_total};
\<close>
end
