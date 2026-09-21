(*  Title: Stark/Square_Sequence_192_Core_Completeness.thy
    License: BSD-3-Clause
*)

theory Square_Sequence_192_Core_Completeness
  imports Square_Sequence_Interpolation Soundness_Square_Sequence_192
    Stark_Completeness.Completeness
begin

section \<open>Concrete square semantics and honest core completeness\<close>

text \<open>The existing field, generator, scale 64, trace length 1024, two shifted
  powers and 640 query repetitions are unchanged. Endpoints and the pure
  compatibility operation remain arbitrary. No locale premise is added:
  trace length, constraint degree and honest algebraic validity are proved
  for the actual prover interpolant. Zero input is included.

  This result concerns verification.exec, whose send/read operations use pure
  concat. It does not establish completeness of the distinct RO-absorbing
  staged experiment used by the certified soundness bound. Its composition
  degree and FRI depth remain the actual variable values of the core prover.\<close>

context
  fixes a z :: field_192
    and combine :: "field_192 \<Rightarrow> field_192 \<Rightarrow> field_192"
begin

interpretation s: soundness combine field_generator_192 field_generator_192 64 1024 2
  stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
  "square_workload_spec 1024 a z" 640 "square_workload_spec2 1024 a z" 0 0 0
  by (rule square_192_soundness) simp

interpretation p: prover combine field_generator_192 field_generator_192 64 1024 2
  stark_mod_ring_decode stark_mod_ring_encode field_cardinality_192
  "square_workload_spec 1024 a z" 640 "square_trace_values 1024 a"
  by unfold_locales simp

interpretation honest: verification combine field_generator_192 field_generator_192 64 1024 2
  stark_mod_ring_encode stark_mod_ring_decode field_cardinality_192
  "square_workload_spec 1024 a z" 640 "square_workload_spec2 1024 a z"
  "square_trace_values 1024 a"
proof unfold_locales
  fix c roots d
  assume entry: "(c,roots,d) \<in> set (square_workload_spec 1024 a z)"
  show "degree (c p.f_powers) \<le> d*(1024-1)"
    using square_workload_constraint_degree[OF p.honest_interpolant_degree entry]
    by (simp add: p.f_powers_def)
qed

text \<open>The trace predicate is equivalent to the intended computation, not
  just a necessary condition or a single constant witness.\<close>

lemma square_192_valid_trace_iff:
  "s.exists_valid_trace \<longleftrightarrow> z=a^(2^1023)"
proof
  assume "s.exists_valid_trace"
  then show "z=a^(2^1023)"
    using s.square_workload_valid_trace_endpoint[OF refl refl] by simp
next
  assume endpoint: "z=a^(2^1023)"
  have constraints: "\<forall>(c,roots,d)\<in>set (square_workload_spec 1024 a z).
    \<forall>r\<in>set roots. poly (c (map (\<lambda>i. p.f \<circ>\<^sub>p XP (s.g^i)) [0..<2])) (s.g^r)=0"
    using p.square_honest_interpolant_constraints[OF refl]
    by (simp add: endpoint)
  show "s.exists_valid_trace"
  proof (rule s.exists_valid_traceI[OF p.honest_interpolant_degree])
    fix c roots d
    assume "(c,roots,d)\<in>set (square_workload_spec 1024 a z)"
    then show "s.trace_satisfies_constraint p.f c roots"
      using constraints
      unfolding s.trace_satisfies_constraint_def s.trace_powers_of_def by auto
  qed
qed

lemma square_192_honest_trace_valid:
  assumes endpoint: "z=a^(2^1023)"
  shows "honest.honest_trace_valid"
  using p.square_honest_interpolant_constraints[OF refl]
  unfolding honest.honest_trace_valid_def honest.honest_trace_algebra_def
    honest.constraint_roots_vanish_def s.g_map_def p.f_powers_def
  by (simp add: endpoint)

lemma square_192_core_failure_zero:
  assumes endpoint: "z=a^(2^1023)"
  shows "wp_event honest.exec Option.is_none honest.init_state = 0"
  by (rule honest.completeness_wp_reduction[OF square_192_honest_trace_valid[OF endpoint]])

text \<open>Use the explicit non-failure event, not @{const success_prob}, whose current
  constant-one integrand also counts failed outcomes.\<close>

lemma square_192_core_acceptance_one:
  assumes endpoint: "z=a^(2^1023)"
  shows "wp_event honest.exec (\<lambda>out. \<not>Option.is_none out) honest.init_state = 1"
proof -
  have nf: "None \<notin> dom (dist (execute honest.exec honest.init_state))"
    using honest.honest_trace_valid_implies_no_failure[OF square_192_honest_trace_valid[OF endpoint]]
    unfolding honest.no_failure_def .
  show ?thesis unfolding wp_event_def wp_def
    by (rule dist_expect_eq_1) (use nf in \<open>metis Option.is_none_def\<close>)
qed
end

ML \<open>
  fun check_square_core expected th =
    if null (Thm.hyps_of th) andalso Thm.nprems_of th = expected
       andalso null (Thm_Deps.all_oracles [th])
    then writeln (Thm.string_of_thm_global @{theory} th)
    else error "Unexpected concrete completeness dependency";
  val _ = check_square_core 0 @{thm square_192_valid_trace_iff};
  val _ = List.app (check_square_core 1)
    @{thms square_192_honest_trace_valid square_192_core_failure_zero
      square_192_core_acceptance_one};
\<close>

end
