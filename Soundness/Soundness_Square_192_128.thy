(* Title: Stark/Soundness_Square_192_128.thy
   License: BSD-3-Clause *)

theory Soundness_Square_192_128
  imports Soundness_Square_128_Target
begin

section \<open>Concrete square-workload acceptance target\<close>

text \<open>The field, fixed domain and square-workload locale obligations are
  discharged by existing theorems. The result uses exactly 640 query repetitions
  and covers every wellformed controlled staged allocation with total declared
  allowance at most two-to-the-twentieth. The original three public soundness
  requirements remain; the fourth displayed requirement is the approved
  numerical profile cap, not a new locale or general soundness premise.
  The generator and shift remain the previously proved choices. Compatibility
  and legacy error parameters remain arbitrary. This is a false-statement
  acceptance upper bound in the existing adaptive random-oracle experiment,
  not an unqualified security work factor, quantum-oracle claim, zero-knowledge
  theorem, knowledge extraction result or deployment-ready implementation.\<close>

context
  fixes a z :: field_192
    and combine :: "field_192 \<Rightarrow> field_192 \<Rightarrow> field_192"
    and et ec em :: prob
begin

interpretation square_128: soundness combine field_generator_192 field_generator_192
  64 1024 2 stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
  "square_workload_spec 1024 a z" 640 "square_workload_spec2 1024 a z" et ec em
  by (rule square_192_soundness) simp

theorem square_192_128_soundness:
  assumes false_statement: "\<not> square_128.exists_valid_trace"
    and wf: "square_128.staged_budget_wellformed budgets"
    and controlled: "square_128.staged_adversary_controlled budgets A"
    and cap: "square_128.staged_attacker_query_budget budgets \<le> 2^20"
  shows "nn2real (square_128.ro_absorb_checked_staged_adversary_acceptance_probability A)
    \<le> (1/2^128::real)"
proof -
  have source: "nn2real (square_128.ro_absorb_checked_staged_adversary_acceptance_probability A)
      \<le> square_uniform_ledger field_cardinality_192 640 (2^20)"
    by (rule square_128.square_soundness_at_most_budget[OF _ _ _ _ false_statement wf controlled cap])
      simp_all
  show ?thesis by (rule order_trans[OF source square_128_uniform_target])
qed

corollary square_192_128_incorrect_endpoint:
  assumes incorrect: "z \<noteq> a^(2^1023)"
    and wf: "square_128.staged_budget_wellformed budgets"
    and controlled: "square_128.staged_adversary_controlled budgets A"
    and cap: "square_128.staged_attacker_query_budget budgets \<le> 2^20"
  shows "nn2real (square_128.ro_absorb_checked_staged_adversary_acceptance_probability A)
    \<le> (1/2^128::real)"
proof -
  have false_statement: "\<not> square_128.exists_valid_trace"
    using square_192_semantics(1)[of a z] incorrect by blast
  show ?thesis by (rule square_192_128_soundness[OF false_statement wf controlled cap])
qed

end

ML \<open>
  List.app (fn th =>
    if null (Thm.hyps_of th) andalso Thm.nprems_of th=4
      andalso null (Thm_Deps.all_oracles [th])
    then writeln "Concrete target: four displayed requirements, no hidden dependencies"
    else error "Unexpected concrete soundness dependency")
    @{thms square_192_128_soundness square_192_128_incorrect_endpoint};
\<close>
end
