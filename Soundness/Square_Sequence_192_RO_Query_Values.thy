(*  Title:      Stark/Square_Sequence_192_RO_Query_Values.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Square_Sequence_192_RO_Query_Values
 imports "Stark.Square_Sequence_192_RO_Composition"
begin

section \<open>Honest Query-Round Initial Values\<close>

text \<open>The trace head and original composition evaluation agree with the canonical starting words. The composition identity uses the proved honest endpoint algebra, not verifier acceptance.\<close>
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

lemma square_ro_initial_trace_value:
  "hd (map (\<lambda>i. square_ro_trace_layer a []!i)
    (s.powers_scaled (s.index raw))) =
    square_ro_trace_layer a []!s.index raw"
  unfolding s.powers_scaled_def
  by (simp add: numeral_2_eq_2)

lemma square_ro_initial_composition_value:
  assumes endpoint: "z=a^(2^1023)"
  shows "s.cp_eval as (map (\<lambda>i. square_ro_trace_layer a []!i)
    (s.powers_scaled (s.index raw))) (s.h^s.index raw*field_generator_192) =
    square_ro_composition_layer a z as []!s.index raw"
proof -
  have valid: "honest.honest_trace_valid"
    by (rule square_192_honest_trace_valid[OF endpoint])
  have tr: "square_ro_trace_layer a []=p.f_eval"
    by (simp add: square_ro_trace_layer_def square_ro_fold_poly_def
      square_ro_fold_domain_def p.f_eval_def)
  have comp: "square_ro_composition_layer a z as []=p.cp_eval as"
    by (simp add: square_ro_composition_layer_def square_ro_fold_poly_def
      square_ro_fold_domain_def p.cp_eval_def)
  show ?thesis
    using honest.honest_initial_fri_accumulator_value[OF valid refl refl comp, where x=raw]
    by (simp add: tr)
qed

end

ML \<open>
  val _ = List.app (fn (name, expected, th) =>
    if Thm.nprems_of th = expected andalso null (Thm.hyps_of th)
       andalso null (Thm_Deps.all_oracles [th])
    then writeln (name ^ ": checked " ^ string_of_int expected ^ " explicit premises")
    else error ("Unexpected query-round dependency: " ^ name))
    [("square_ro_initial_trace_value", 0, @{thm square_ro_initial_trace_value}),
     ("square_ro_initial_composition_value", 1, @{thm square_ro_initial_composition_value})];
\<close>

end
