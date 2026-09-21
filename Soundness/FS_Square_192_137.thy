theory FS_Square_192_137
 imports FS_Square_Prefix_Ledger
   FS_Square_137_Arithmetic FS_Square_192_135
begin

section \<open>Prefix-refined concrete target for conventional FS adversaries\<close>

text \<open>The source ledger and unchanged exact modulo bases connect the rational
  certificate to the original FS experiment. Apply the existing concrete locale
  fact directly instead of registering another full locale interpretation.
  Only the false statement (or incorrect endpoint) and original query cap are
  public premises. This is a fixed-statement classical field-valued ROM bound,
  not QROM, knowledge extraction or an unrestricted work-factor guarantee.
  Decimal estimates and larger-query thresholds remain external diagnostics.\<close>

lemma fs_137_ledger:
 "square_fs_prefix_ledger field_cardinality_192 (2^20) =
   14268787487890250/(2*real field_cardinality_192) +
   1963186*(square_modulo_base field_cardinality_192 54953^640 +
     2*square_modulo_base field_cardinality_192 54954^640)"
 by (simp add: square_fs_prefix_ledger_def)

theorem square_fs_137_prefix_target:
 "square_fs_prefix_ledger field_cardinality_192 (2^20)\<le>(1/2^137::real)"
 unfolding fs_137_ledger
 using fs_137_total[OF fs_135_bases]
 by (simp add: field_cardinality_192_def certificate_prime_192_def)

ML \<open>
 List.app (fn th =>
   if null(Thm.hyps_of th) andalso Thm.nprems_of th=0 andalso null(Thm_Deps.all_oracles [th])
   then () else error "Unexpected prefix closed target dependency")
   @{thms fs_137_ledger square_fs_137_prefix_target};
\<close>
context fixes a z :: field_192
begin

theorem square_192_fs_137_soundness:
 assumes false_statement:
   "\<not>soundness.exists_valid_trace field_generator_192 1024 2 field_cardinality_192
     (square_workload_spec 1024 a z)"
   and bound: "fs_query_bound (2^20) P"
 shows "nn2real(soundness.fs_acceptance_probability
   field_generator_192 field_generator_192 64 1024 2 stark_mod_ring_decode
   field_cardinality_192 (square_workload_spec 1024 a z) 640
   (square_workload_spec2 1024 a z) P)\<le>(1/2^137::real)"
proof -
 have concrete_locale: "soundness field_generator_192 field_generator_192 64 1024 2
   stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
   (square_workload_spec 1024 a z) 640 (square_workload_spec2 1024 a z)"
  by (rule square_192_soundness) simp
 have source: "nn2real(soundness.fs_acceptance_probability
   field_generator_192 field_generator_192 64 1024 2 stark_mod_ring_decode
   field_cardinality_192 (square_workload_spec 1024 a z) 640
   (square_workload_spec2 1024 a z) P)\<le>
   square_fs_prefix_ledger field_cardinality_192 (2^20)"
  by (rule soundness.square_fs_prefix_soundness
    [OF concrete_locale _ _ _ _ _ bound false_statement]) simp_all
 show ?thesis by (rule order_trans[OF source square_fs_137_prefix_target])
qed

corollary square_192_fs_137_incorrect_endpoint:
 assumes incorrect: "z\<noteq>a^(2^1023)" and bound: "fs_query_bound (2^20) P"
 shows "nn2real(soundness.fs_acceptance_probability
   field_generator_192 field_generator_192 64 1024 2 stark_mod_ring_decode
   field_cardinality_192 (square_workload_spec 1024 a z) 640
   (square_workload_spec2 1024 a z) P)\<le>(1/2^137::real)"
proof -
 have false_statement:
   "\<not>soundness.exists_valid_trace field_generator_192 1024 2 field_cardinality_192
     (square_workload_spec 1024 a z)"
  using square_192_semantics(1)[of a z] incorrect by blast
 show ?thesis by (rule square_192_fs_137_soundness[OF false_statement bound])
qed

end

ML \<open>
 List.app (fn th =>
   if null(Thm.hyps_of th) andalso Thm.nprems_of th=2 andalso null(Thm_Deps.all_oracles [th])
   then () else error "Unexpected prefix FS target premises or proof dependency")
   @{thms square_192_fs_137_soundness square_192_fs_137_incorrect_endpoint};
\<close>
end
