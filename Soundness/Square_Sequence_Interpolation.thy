(*  Title: Stark/Square_Sequence_Interpolation.thy
    License: BSD-3-Clause
*)

theory Square_Sequence_Interpolation
  imports Stark_Examples.Square_Sequence_Workload
begin

section \<open>Actual prover interpolation for square traces\<close>

text \<open>The trace values are explicit repeated squaring, with no restriction on
  the input. The degree and evaluation facts below are proved in the existing
  prover locale, before the additional verification degree obligation is used.
  These are algebraic facts, not a change to the prover or transcript.\<close>

definition square_trace_values :: "nat \<Rightarrow> 'f::monoid_mult \<Rightarrow> 'f list"
  where "square_trace_values L a = map (\<lambda>i. a^(2^i)) [0..<L]"

lemma square_trace_values_length [simp]:
  "length (square_trace_values L a) = L"
  by (simp add: square_trace_values_def)

context prover
begin

lemma honest_interpolant_degree:
  "degree f < clength"
proof -
  have vals_len: "length vals = clength" using trace_length by simp
  have grid_len: "length G = clength" unfolding G_def by simp
  have deg: "degree f \<le> length (zip G vals) - 1"
    unfolding f_def by (rule degree_lagrange_interpolation_poly)
  have zip_len: "length (zip G vals) = clength"
    using vals_len grid_len by simp
  show ?thesis using deg zip_len clength_pos by simp
qed

lemma honest_trace_grid_distinct:
  "distinct G"
  unfolding G_def
  by (auto simp: distinct_map inj_on_def intro: g_power_inj_on_range)

lemma honest_interpolant_nth:
  assumes i: "i < clength"
  shows "poly f (g^i) = vals!i"
proof -
  have grid_len: "length G = clength" unfolding G_def by simp
  have vals_len: "length vals = clength" using trace_length by simp
  note lengths = grid_len vals_len
  have mem: "(G!i, vals!i) \<in> set (zip G vals)"
    using nth_mem[of i "zip G vals"] i lengths by simp
  have distinct: "distinct (map fst (zip G vals))"
    using honest_trace_grid_distinct lengths by simp
  have "poly f (G!i) = vals!i"
    unfolding f_def by (rule lagrange_interpolation_poly[OF distinct refl mem])
  then show ?thesis using i by (simp add: G_def)
qed

lemma square_honest_interpolant_nth:
  assumes vals: "vals = square_trace_values clength a" and i: "i < clength"
  shows "poly f (g^i) = a^(2^i)"
  using honest_interpolant_nth[OF i] vals i
  by (simp add: square_trace_values_def)

lemma square_honest_interpolant_constraints:
  assumes vals: "vals = square_trace_values clength a"
  shows "\<forall>(c,roots,d)\<in>set (square_workload_spec clength a (a^(2^(clength-1)))).
    \<forall>r\<in>set roots. poly (c (map (\<lambda>i. f \<circ>\<^sub>p XP (g^i)) [0..<2])) (g^r)=0"
proof -
  have start: "poly f 1 = a"
    using square_honest_interpolant_nth[OF vals clength_pos] by simp
  have finish: "poly f (g^(clength-1)) = a^(2^(clength-1))"
    by (rule square_honest_interpolant_nth[OF vals]) (use clength_pos in arith)
  have step: "poly f (g^(Suc i)) = (poly f (g^i))^2" if "i < clength-1" for i
  proof -
    have bounds: "i<clength" "Suc i<clength" using that by arith+
    show ?thesis using square_honest_interpolant_nth[OF vals bounds(1)]
      square_honest_interpolant_nth[OF vals bounds(2)]
      by (simp add: power_mult[symmetric] mult.commute)
  qed
  show ?thesis unfolding square_workload_constraints_iff
    using start finish step by blast
qed

end
end
