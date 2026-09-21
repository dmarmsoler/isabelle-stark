(* Title: Stark/Soundness_Square_128_Target.thy
   License: BSD-3-Clause *)

theory Soundness_Square_128_Target
  imports Soundness_Square_Uniform_Soundness
    Soundness_Square_Sequence_192 Soundness_Square_128_Arithmetic
begin

section \<open>Closed target certificate for the source-connected ledger\<close>

text \<open>The approved profile uses the existing certified field and square
  workload, exactly 640 query repetitions and total declared staged allowance
  at most two-to-the-twentieth. Every numeral below is checked against the
  original ledger definitions. Both exact modulo fibers and every exceptional
  and connection charge remain. The dyadic estimate is only an intermediate
  inequality; it does not change the sampler or public bound.
  This theorem certifies the upper target, not optimality, an attack probability
  lower bound, or a larger-budget or quantum-oracle security claim.\<close>

lemma square_128_vertex:
  "square_maximizing_early_budget 640 (2^20) = 924138"
  by (simp add: square_maximizing_early_budget_explicit)

lemma square_128_common:
  "square_mca_common_numerator 640 924138 0 124438 = 55372749872256"
  by (simp add: square_mca_common_numerator_def Let_def)

lemma square_128_bases:
  "0 \<le> square_modulo_base field_cardinality_192 54953"
  "square_modulo_base field_cardinality_192 54953 \<le> 27/32"
  "0 \<le> square_modulo_base field_cardinality_192 54954"
  "square_modulo_base field_cardinality_192 54954 \<le> 27/32"
  by (simp_all add: square_modulo_base_def field_cardinality_192_def
    certificate_prime_192_def)

lemma square_128_ledger:
  "square_uniform_ledger field_cardinality_192 640 (2^20) =
    68662639825042 / real field_cardinality_192 +
    2305636 * (square_modulo_base field_cardinality_192 54953^640 +
      2*square_modulo_base field_cardinality_192 54954^640)"
  using square_128_vertex
  by (simp add: square_uniform_ledger_def square_weighted_ledger_def Let_def
    square_128_common add_divide_distrib algebra_simps)

theorem square_128_uniform_target:
  "square_uniform_ledger field_cardinality_192 640 (2^20) \<le> (1/2^128::real)"
proof -
  have nonsampling: "(68662639825042::real) / real field_cardinality_192 \<le> 1/2^144"
    using square_128_nonsampling
    by (simp add: field_cardinality_192_def certificate_prime_192_def)
  have sampling: "2305636 * (square_modulo_base field_cardinality_192 54953^640 +
      2*square_modulo_base field_cardinality_192 54954^640) \<le> 1/2^132"
    by (rule square_128_sampling[OF square_128_bases])
  show ?thesis unfolding square_128_ledger
    using nonsampling sampling square_128_total by argo
qed

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso Thm.nprems_of th=0
      andalso null (Thm_Deps.all_oracles [th])
    then () else error "Unexpected closed target dependency")
    @{thms square_128_vertex square_128_common square_128_bases
      square_128_ledger square_128_uniform_target};
\<close>
end
