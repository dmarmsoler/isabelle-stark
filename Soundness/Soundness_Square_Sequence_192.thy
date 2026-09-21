(*  Title:      Stark/Soundness_Square_Sequence_192.thy
    License:    BSD-3-Clause
*)

theory Soundness_Square_Sequence_192
  imports Soundness_Square_Sequence_Workload Stark_Examples.Prime_Field_192
begin

section \<open>Square-sequence obligations on the certified 192-bit field\<close>

text \<open>The field, generator and domain are fixed independently of the endpoints
  and repetition count. The only hypothesis of the locale-predicate theorem is
  the existing positive-repetition requirement. No budget or security target
  is selected; none of the three public soundness premises is changed.\<close>

theorem square_192_soundness:
  fixes a z :: field_192
  assumes R: "0<R"
  shows "soundness field_generator_192 field_generator_192 64 1024 2
    stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
    (square_workload_spec 1024 a z) R (square_workload_spec2 1024 a z)"
proof -
  have L: "2\<le>(1024::nat)" "\<exists>k. (1024::nat)=2^k"
    by simp (rule exI[of _ 10], simp)
  have S: "\<exists>k. (64::nat)=2^k" by (rule exI[of _ 6]) simp
  show ?thesis
    using square_workload_mod_ring_soundness[where 'a=field_index_192,
      OF L S _ _ _ R, where omega=field_generator_192 and a=a and z=z]
      field_generator_192_order field_192_domain_arithmetic
    by simp
qed


text \<open>The valid-trace conclusions do not depend on a repetition count. A
  single positive repetition is used only to access the existing locale's
  semantic lemmas, not as an amplification or security profile. Compatibility
  and legacy error parameters remain arbitrary and impose no budget constraint.
  This proves the computation implication and true/false nonvacuity cases,
  not interpolation completeness or an authenticated execution construction.\<close>

lemma square_192_semantics:
  fixes a z :: field_192 and combine :: "field_192 \<Rightarrow> field_192 \<Rightarrow> field_192"
    and et ec em :: prob
  shows "soundness.exists_valid_trace field_generator_192 1024 2 field_cardinality_192
      (square_workload_spec 1024 a z) \<longrightarrow> z=a^(2^1023)"
    and "soundness.exists_valid_trace field_generator_192 1024 2 field_cardinality_192
      (square_workload_spec 1024 1 1)"
    and "\<not>soundness.exists_valid_trace field_generator_192 1024 2 field_cardinality_192
      (square_workload_spec 1024 1 0)"
proof -
  interpret arbitrary: soundness combine field_generator_192 field_generator_192 64 1024 2
    stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
    "square_workload_spec 1024 a z" 1 "square_workload_spec2 1024 a z" et ec em
    by (rule square_192_soundness) simp
  interpret yes: soundness combine field_generator_192 field_generator_192 64 1024 2
    stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
    "square_workload_spec 1024 1 1" 1 "square_workload_spec2 1024 1 1" et ec em
    by (rule square_192_soundness) simp
  interpret no: soundness combine field_generator_192 field_generator_192 64 1024 2
    stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
    "square_workload_spec 1024 1 0" 1 "square_workload_spec2 1024 1 0" et ec em
    by (rule square_192_soundness) simp
  show "soundness.exists_valid_trace field_generator_192 1024 2 field_cardinality_192
      (square_workload_spec 1024 a z) \<longrightarrow> z=a^(2^1023)"
    using arbitrary.square_workload_valid_trace_endpoint by simp
  show "soundness.exists_valid_trace field_generator_192 1024 2 field_cardinality_192
      (square_workload_spec 1024 1 1)"
    by (rule yes.square_workload_true_statement) simp_all
  show "\<not>soundness.exists_valid_trace field_generator_192 1024 2 field_cardinality_192
      (square_workload_spec 1024 1 0)"
    by (rule no.square_workload_false_statement) simp_all
qed


ML \<open>
  List.app (Prime_192_Replay_Arithmetic.inspect "concrete workload semantics")
    @{thms square_192_semantics};
  val locale_fact = @{thm square_192_soundness};
  val _ = if null (Thm.hyps_of locale_fact) andalso Thm.nprems_of locale_fact=1
    andalso null (Thm_Deps.all_oracles [locale_fact])
    then writeln "Locale-predicate theorem: only the displayed positive-repetition premise"
    else error "Unexpected concrete workload dependency";
\<close>

end
