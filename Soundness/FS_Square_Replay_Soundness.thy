(* Title: Stark/FS_Square_Replay_Soundness.thy
   License: BSD-3-Clause *)

theory FS_Square_Replay_Soundness
  imports FS_Replay_Soundness Soundness_Square_192_128
begin

section \<open>Concrete square soundness for conventional oracle-query caps\<close>

text \<open>The field, workload and locale obligations are discharged by the
  existing concrete interpretation. The only displayed requirements are the
  query cap of the original adaptive producer and a false statement (or an
  incorrect square endpoint). No staged-allowance premise is left to the caller.

  The polynomial identities are HOL equalities for the source ledger, not
  externally computed facts. Numerical evaluations and threshold diagnostics
  are separate and are not Isabelle-certified security instances. In particular,
  the earlier certified staged allowance must not be relabelled conventional Q.
  The sufficient 664Q replay allocation is not a lower bound for all embeddings.
  The verifier, field-valued oracle and exact modulo sampler are unchanged.\<close>

lemma square_fs_replay_common_polynomial:
  "square_mca_common_numerator 640 (2*Q) (22*Q) (640*Q) =
    9766448*Q^2 + 12539305712*Q + 4680748361546"
  by (simp add: square_mca_common_numerator_def Let_def algebra_simps power2_eq_square)

lemma square_fs_replay_ledger_polynomial:
  "square_weighted_ledger F 640 (2*Q) (22*Q) (640*Q) =
    real (21737376*Q^2 + 33425487832*Q + 17262492169912)/(2*real F) +
    (664*real Q+1257060) *
      (square_modulo_base F 54953^640 + 2*square_modulo_base F 54954^640)"
  unfolding square_weighted_ledger_def Let_def square_fs_replay_common_polynomial
  by (simp add: add_divide_distrib algebra_simps power2_eq_square)

context
  fixes a z :: field_192
    and combine :: "field_192 \<Rightarrow> field_192 \<Rightarrow> field_192"
    and et ec em :: prob
begin

interpretation square_fs: soundness combine field_generator_192 field_generator_192
  64 1024 2 stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
  "square_workload_spec 1024 a z" 640 "square_workload_spec2 1024 a z" et ec em
  by (rule square_192_soundness) simp

theorem square_192_fs_replay_soundness:
  assumes false_statement: "\<not>square_fs.exists_valid_trace"
    and bound: "fs_query_bound Q P"
  shows "nn2real (square_fs.fs_acceptance_probability P) \<le>
    square_weighted_ledger field_cardinality_192 640 (2*Q) (22*Q) (640*Q)"
  by (rule square_fs.square_fs_replay_soundness[OF _ _ _ _ false_statement bound])
    simp_all

corollary square_192_fs_replay_incorrect_endpoint:
  assumes incorrect: "z \<noteq> a^(2^1023)" and bound: "fs_query_bound Q P"
  shows "nn2real (square_fs.fs_acceptance_probability P) \<le>
    square_weighted_ledger field_cardinality_192 640 (2*Q) (22*Q) (640*Q)"
proof -
  have false_statement: "\<not>square_fs.exists_valid_trace"
    using square_192_semantics(1)[of a z] incorrect by blast
  show ?thesis by (rule square_192_fs_replay_soundness[OF false_statement bound])
qed

end

ML \<open>
  List.app (fn th =>
    if null(Thm.hyps_of th) andalso null(Thm_Deps.all_oracles [th])
    then () else error "Unexpected concrete FS dependency")
    @{thms square_fs_replay_common_polynomial square_fs_replay_ledger_polynomial
      square_192_fs_replay_soundness square_192_fs_replay_incorrect_endpoint};
  List.app (fn th => if Thm.nprems_of th=2 then ()
    else error "Unexpected concrete FS premise count")
    @{thms square_192_fs_replay_soundness square_192_fs_replay_incorrect_endpoint};
\<close>
end
