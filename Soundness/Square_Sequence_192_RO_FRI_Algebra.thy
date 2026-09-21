(*  Title:      Stark/Square_Sequence_192_RO_FRI_Algebra.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Square_Sequence_192_RO_FRI_Algebra
  imports "Stark.Square_Sequence_192_RO_Composition"
begin

section \<open>Honest FRI Prefix Domains and Fold Values\<close>

text \<open>Exact algebra for the existing square-workload domain and folding operation. The polynomial is arbitrary and no challenge is excluded. These lemmas require no successful prover or verifier execution; terminal constancy is derived from degree zero.\<close>

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

lemma square_ro_fold_domain_point:
  assumes idx: "i < length (square_ro_fold_domain s.eval_domain bs)"
  shows "square_ro_fold_domain s.eval_domain bs ! i =
    ((s.h^i)*field_generator_192)^(2^length bs)"
  using idx
proof (induction bs arbitrary: i rule: rev_induct)
  case Nil
  then show ?case
    unfolding square_ro_fold_domain_def
    using honest.eval_domain_nth honest.eval_domain_length
    by simp
next
  case (snoc b bs)
  have step: "square_ro_fold_domain s.eval_domain (bs@[b]) =
    p.next_fri_domain (square_ro_fold_domain s.eval_domain bs)"
    by (simp add: square_ro_fold_domain_def)
  have half: "i < length (square_ro_fold_domain s.eval_domain bs) div 2"
    using snoc.prems step by (simp add: p.next_fri_domain_def)
  have prev: "i < length (square_ro_fold_domain s.eval_domain bs)"
    using half by arith
  show ?case
    using honest.next_fri_domain_nth[OF half] snoc.IH[OF prev]
    by (simp add: step power_add[symmetric] mult_2)
qed

lemma square_ro_fold_domain_power_length:
  assumes "length bs \<le> 16"
  shows "length (square_ro_fold_domain s.eval_domain bs) = (2::nat)^(16-length bs)"
  using power_diff[of "2::nat" "length bs" 16] assms
  by (simp add: square_ro_fold_domain_exact_length s.eval_domain_def s.H_def)

lemma square_ro_fold_domain_round:
  assumes "length bs \<le> 16"
  shows "length (square_ro_fold_domain s.eval_domain bs) * (2::nat)^length bs = 65536"
  using assms
  by (simp add: square_ro_fold_domain_power_length[OF assms]
    power_add[symmetric])

lemma square_ro_fold_next_value:
  fixes q :: "field_192 poly" and b :: field_192
  assumes depth: "length bs < 16"
    and idx: "i < length (square_ro_fold_domain s.eval_domain bs)"
  defines "xs \<equiv> map (poly (square_ro_fold_poly q bs)) (square_ro_fold_domain s.eval_domain bs)"
    and "ys \<equiv> map (poly (square_ro_fold_poly q (bs@[b]))) (square_ro_fold_domain s.eval_domain (bs@[b]))"
  shows "honest.fri_fold_value b xs i (length xs) (2^length bs) =
    ys ! (i mod (length xs div 2))"
proof -
  let ?D = "square_ro_fold_domain s.eval_domain bs"
  let ?E = "square_ro_fold_domain s.eval_domain (bs@[b])"
  let ?len = "length xs"
  let ?v = "((s.h^i)*field_generator_192)^(2^length bs)"
  have depth': "length bs \<le> 16" using depth by simp
  have suc: "length (bs@[b]) \<le> 16" using depth by simp
  have len: "?len = (2::nat)^(16-length bs)"
    using square_ro_fold_domain_power_length[OF depth'] by (simp add: xs_def)
  have diff: "16-length bs = Suc (15-length bs)" using depth by arith
  have pos: "0<?len" and even: "2 dvd ?len" and half: "0<?len div 2"
    by (simp_all add: len diff)
  have round: "?len * (2::nat)^length bs = 1024*64"
    using square_ro_fold_domain_round[OF depth'] by (simp add: xs_def)
  have di: "?D!i=?v" by (rule square_ro_fold_domain_point[OF idx])
  have sib: "(i+?len div 2) mod ?len < length ?D"
    using pos by (simp add: xs_def)
  have ds: "?D!((i+?len div 2) mod ?len) = -?v"
    by (rule honest.fri_sibling_domain_at[OF pos even round refl])
      (rule square_ro_fold_domain_point[OF sib])
  have step: "p.next_fri_layer (square_ro_fold_poly q bs) ?D b =
    (square_ro_fold_poly q (bs@[b]), ?E, ys)"
    by (simp add: ys_def p.next_fri_layer_def square_ro_fold_poly_def square_ro_fold_domain_def Let_def)
  have elen: "length ?E = ?len div 2"
    using honest.next_fri_layer_components(2)[OF step]
    by (simp add: p.next_fri_domain_def xs_def)
  have ni: "i mod (?len div 2) < length ?E" using half elen by simp
  have de: "?E!(i mod (?len div 2))=?v*?v"
    using square_ro_fold_domain_point[OF ni]
      honest.fri_next_domain_round[OF half even round, of i]
    by (simp add: mult_2)
  show ?thesis
    by (rule honest.fri_fold_value_next_layer_value[OF s.two_nonzero
      honest.verifier_domain_point_nonzero step refl _ _ _ refl di ds ni de])
      (use idx in \<open>simp_all add: xs_def\<close>)
qed

lemma square_ro_fold_expression_next_value:
  fixes q :: "field_192 poly" and b :: field_192
  assumes depth: "length bs<16"
    and idx: "i<length (square_ro_fold_domain s.eval_domain bs)"
  defines "xs \<equiv> map (poly (square_ro_fold_poly q bs)) (square_ro_fold_domain s.eval_domain bs)"
    and "ys \<equiv> map (poly (square_ro_fold_poly q (bs@[b]))) (square_ro_fold_domain s.eval_domain (bs@[b]))"
  shows "(xs!i + xs!((i+length xs div 2) mod length xs)) div 2 +
     b * ((xs!i - xs!((i+length xs div 2) mod length xs)) div
       (2*((s.h^i)*field_generator_192)^(2^length bs))) =
     ys!(i mod (length xs div 2))"
  using square_ro_fold_next_value[OF depth idx, where q=q and b=b]
  by (simp add: xs_def ys_def honest.fri_fold_value_def)

lemma square_ro_fold_terminal_constant:
  assumes depth: "length bs\<le>16"
    and deg: "degree (square_ro_fold_poly q bs)=0"
    and idx: "i<length (square_ro_fold_domain s.eval_domain bs)"
  shows "map (poly (square_ro_fold_poly q bs)) (square_ro_fold_domain s.eval_domain bs)!i =
    hd (map (poly (square_ro_fold_poly q bs)) (square_ro_fold_domain s.eval_domain bs))"
proof -
  have ne: "square_ro_fold_domain s.eval_domain bs\<noteq>[]"
    using square_ro_fold_domain_power_length[OF depth] by auto
  show ?thesis using idx
    by (simp add: hd_map[OF ne] honest.poly_degree_zero_const[OF deg])
qed

end

ML \<open>
  val _ = List.app (fn (name, expected, th) =>
    let val oracles = Thm_Deps.all_oracles [th]
    in
      if Thm.nprems_of th = expected andalso null (Thm.hyps_of th) andalso null oracles
      then writeln (name ^ ": checked " ^ string_of_int expected ^ " explicit premises")
      else error ("Unexpected FRI-chain dependency: " ^ name)
    end)
    [("square_ro_fold_domain_point", 1, @{thm square_ro_fold_domain_point}),
     ("square_ro_fold_domain_power_length", 1, @{thm square_ro_fold_domain_power_length}),
     ("square_ro_fold_domain_round", 1, @{thm square_ro_fold_domain_round}),
     ("square_ro_fold_next_value", 2, @{thm square_ro_fold_next_value}),
     ("square_ro_fold_expression_next_value", 2, @{thm square_ro_fold_expression_next_value}),
     ("square_ro_fold_terminal_constant", 3, @{thm square_ro_fold_terminal_constant})];
\<close>

end
