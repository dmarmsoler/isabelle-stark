theory FS_Square_192_135
 imports FS_Square_Refined_Ledger FS_Square_135_Arithmetic
begin

section \<open>Refined concrete target for conventional FS adversaries\<close>

text \<open>The source ledger and exact modulo bases connect the rational
  certificate to false-statement and incorrect-endpoint acceptance. The original
  adaptive, privately randomized FS program makes at most two to the twentieth
  oracle calls. The certified field, 640 repetitions and public premises are
  unchanged. This is a fixed-statement, classical field-valued ROM result, not
  QROM, bit-hash implementation security, knowledge extraction or an unrestricted
  work-factor claim. Larger-query thresholds and decimal estimates are external
  diagnostics, not additional certified profiles.\<close>

lemma fs_135_bases:
 "0\<le>square_modulo_base field_cardinality_192 54953"
 "square_modulo_base field_cardinality_192 54953\<le>68/81"
 "0\<le>square_modulo_base field_cardinality_192 54954"
 "square_modulo_base field_cardinality_192 54954\<le>68/81"
 by (simp_all add: square_modulo_base_def field_cardinality_192_def certificate_prime_192_def)

lemma fs_135_ledger:
 "square_fs_refined_ledger field_cardinality_192 (2^20) =
   149531366400678730/(2*real field_cardinality_192) +
   1963186*(square_modulo_base field_cardinality_192 54953^640 +
     2*square_modulo_base field_cardinality_192 54954^640)"
 by (simp add: square_fs_refined_ledger_def)

theorem square_fs_135_refined_target:
 "square_fs_refined_ledger field_cardinality_192 (2^20)\<le>(1/2^135::real)"
 unfolding fs_135_ledger
 using fs_135_total[OF fs_135_bases]
 by (simp add: field_cardinality_192_def certificate_prime_192_def)

ML \<open>
 List.app (fn th =>
   if null(Thm.hyps_of th) andalso Thm.nprems_of th=0 andalso null(Thm_Deps.all_oracles [th])
   then () else error "Unexpected refined closed target dependency")
   @{thms fs_135_bases fs_135_ledger square_fs_135_refined_target};
\<close>

context
 fixes a z :: field_192
   and combine :: "field_192 \<Rightarrow> field_192 \<Rightarrow> field_192"
   and et ec em :: prob
begin

interpretation square_fs_135: soundness combine field_generator_192 field_generator_192
 64 1024 2 stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
 "square_workload_spec 1024 a z" 640 "square_workload_spec2 1024 a z" et ec em
 by (rule square_192_soundness) simp

theorem square_192_fs_135_soundness:
 assumes false_statement: "\<not>square_fs_135.exists_valid_trace"
   and bound: "fs_query_bound (2^20) P"
 shows "nn2real(square_fs_135.fs_acceptance_probability P)\<le>(1/2^135::real)"
proof -
 have source: "nn2real(square_fs_135.fs_acceptance_probability P)\<le>
   square_fs_refined_ledger field_cardinality_192 (2^20)"
  by (rule square_fs_135.square_fs_refined_soundness
    [OF _ _ _ _ _ bound false_statement]) simp_all
 show ?thesis by (rule order_trans[OF source square_fs_135_refined_target])
qed

corollary square_192_fs_135_incorrect_endpoint:
 assumes incorrect: "z\<noteq>a^(2^1023)" and bound: "fs_query_bound (2^20) P"
 shows "nn2real(square_fs_135.fs_acceptance_probability P)\<le>(1/2^135::real)"
proof -
 have false_statement: "\<not>square_fs_135.exists_valid_trace"
  using square_192_semantics(1)[of a z] incorrect by blast
 show ?thesis by (rule square_192_fs_135_soundness[OF false_statement bound])
qed

end

ML \<open>
 List.app (fn th =>
   if null(Thm.hyps_of th) andalso Thm.nprems_of th=2 andalso null(Thm_Deps.all_oracles [th])
   then () else error "Unexpected refined FS target premises or proof dependency")
   @{thms square_192_fs_135_soundness square_192_fs_135_incorrect_endpoint};
\<close>
end
