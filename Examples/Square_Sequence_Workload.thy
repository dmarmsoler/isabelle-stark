(*  Title:      Stark/Square_Sequence_Workload.thy
    License:    BSD-3-Clause
*)

theory Square_Sequence_Workload
  imports Prime_Field_Bridge
begin

section \<open>Scalable square-sequence specification\<close>

text \<open>This schema generalizes the small executable example without modifying
  the verifier. Its endpoints are arbitrary field values; its trace length and
  scale remain parameters. These specification and domain facts do not choose
  a cryptographic field, budget allocation or security target.\<close>

subsection \<open>Polynomial and scalar constraints\<close>

definition square_workload_spec ::
  "nat \<Rightarrow> 'f::field \<Rightarrow> 'f \<Rightarrow> (('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat) list"
where "square_workload_spec L a z =
  [(\<lambda>qs. qs!0 - [:a:], [0], 1),
   (\<lambda>qs. qs!0 - [:z:], [L-1], 1),
   (\<lambda>qs. qs!1 - (qs!0)^2, [0..<L-1], 2)]"

definition square_workload_spec2 ::
  "nat \<Rightarrow> 'f::field \<Rightarrow> 'f \<Rightarrow> (('f list \<Rightarrow> 'f) \<times> nat list) list"
where "square_workload_spec2 L a z =
  [(\<lambda>xs. xs!0 - a, [0]),
   (\<lambda>xs. xs!0 - z, [L-1]),
   (\<lambda>xs. xs!1 - (xs!0)^2, [0..<L-1])]"

subsection \<open>Exact metadata and verifier well-formedness\<close>

text \<open>The sum of root-list lengths is L+1, whereas the union of root indices
  has cardinality L. These are different quantities in the soundness analysis.\<close>

lemma square_workload_spec_length [simp]:
  "length (square_workload_spec L a z) = 3"
  by (simp add: square_workload_spec_def)

lemma square_workload_degrees:
  assumes "2\<le>L"
  shows "degrees L (square_workload_spec L a z) = {0,L-2,L-1}"
proof -
  define n where "n=L-2"
  have L: "L=n+2" using assms unfolding n_def by arith
  show ?thesis unfolding degrees_def square_workload_spec_def L
    by (auto simp: conj_disj_distribL ex_disj_distrib algebra_simps)
qed

lemma square_workload_max_degree:
  assumes "2\<le>L"
  shows "Max (degrees L (square_workload_spec L a z)) = L-1"
  using assms by (simp add: square_workload_degrees)

lemma square_workload_root_sum:
  assumes "2\<le>L"
  shows "sum_list (map (\<lambda>(_,roots,_). length roots) (square_workload_spec L a z)) = L+1"
  using assms by (simp add: square_workload_spec_def)

lemma square_workload_root_indices:
  assumes "2\<le>L"
  shows "\<Union>(set (map (\<lambda>(_,roots,_). set roots) (square_workload_spec L a z))) = {0..<L}"
  using assms unfolding square_workload_spec_def by auto

lemma square_workload_roots_in_range:
  assumes "2\<le>L" "(c,roots,d)\<in>set (square_workload_spec L a z)" "r\<in>set roots"
  shows "r<L"
  using assms by (auto simp: square_workload_spec_def)

lemma square_workload_roots_distinct:
  assumes "(c,roots,d)\<in>set (square_workload_spec L a z)"
  shows "distinct roots"
  using assms by (auto simp: square_workload_spec_def)

lemma square_workload_specs_aligned:
  fixes a z :: "'f::field"
  shows "list_all2
    (\<lambda>(c,roots,d) (c2,roots2). roots2=roots \<and>
      (\<forall>qs x. 2\<le>length qs \<longrightarrow> c2 (map (\<lambda>q. poly q x) qs) = poly (c qs) x))
    (square_workload_spec L a z) (square_workload_spec2 L a z)"
proof -
  have nth0: "map f xs ! 0 = f (xs!0)" if "2\<le>length xs" for f :: "'f poly \<Rightarrow> 'f" and xs
    by (rule nth_map) (use that in arith)
  have nth1: "map f xs ! 1 = f (xs!1)" if "2\<le>length xs" for f :: "'f poly \<Rightarrow> 'f" and xs
    by (rule nth_map) (use that in arith)
  show ?thesis
    by (auto simp: square_workload_spec_def square_workload_spec2_def nth0 nth1)
qed

lemma square_workload_degree_fits:
  assumes L: "2\<le>L" and scale: "0<S"
    and entry: "(c,roots,d)\<in>set (square_workload_spec L a z)"
  shows "d*(L-1)-length roots < L*S"
proof -
  have le: "d*(L-1)-length roots \<le> L-1"
    using entry L by (auto simp: square_workload_spec_def)
  have "L\<le>L*S" using scale by (simp add: leI)
  then show ?thesis using le L by arith
qed

lemma square_workload_constraint_degree:
  fixes f :: "'f::field poly"
  assumes deg: "degree f<L"
    and entry: "(c,roots,d)\<in>set (square_workload_spec L a z)"
  shows "degree (c (map (\<lambda>i. f \<circ>\<^sub>p XP (g^i)) [0..<2])) \<le> d*(L-1)"
proof -
  have bound: "degree f\<le>L-1" using deg by arith
  have linear: "degree (XP x :: 'f poly)\<le>1" for x
    unfolding XP_def by (rule degree_monom_le)
  have comp: "degree (f \<circ>\<^sub>p XP x)\<le>L-1" for x
  proof -
    have "degree (f \<circ>\<^sub>p XP x)\<le>degree f * degree (XP x)"
      by (rule degree_pcompose_le)
    also have "...\<le>(L-1)*1"
      by (rule mult_le_mono[OF bound linear])
    finally show ?thesis by simp
  qed
  let ?qs = "map (\<lambda>i. f \<circ>\<^sub>p XP (g^i)) [0..<2]"
  have d0: "degree (?qs!0)\<le>L-1" using comp[of "g^0"] by simp
  have d1: "degree (?qs!1)\<le>L-1" using comp[of "g^1"] by simp
  have endpoint_bound: "degree (?qs!0 - [:x:])\<le>L-1" for x
    by (rule degree_diff_le[OF d0]) simp
  have square: "degree ((?qs!0)^2)\<le>2*(L-1)"
    using degree_mult_le[of "?qs!0" "?qs!0"] d0
    by (simp add: power2_eq_square)
  have transition: "degree (?qs!1-(?qs!0)^2)\<le>2*(L-1)"
    by (rule degree_diff_le) (use d1 square in auto)
  show ?thesis using entry endpoint_bound[of a] endpoint_bound[of z] transition
    by (auto simp: square_workload_spec_def)
qed

subsection \<open>Computation meaning\<close>

text \<open>Evaluating the shifted polynomial at the i-th trace point gives the
  next trace value. The constraints therefore imply repeated squaring. This
  is a soundness-direction statement, not interpolation completeness or an
  authenticated execution construction. The constant-one witness verifies
  that the schema is not an artificial contradiction.\<close>

lemma square_workload_constraints_iff:
  fixes f :: "'f::field poly"
  shows "(\<forall>(c,roots,d)\<in>set (square_workload_spec L a z).
    \<forall>r\<in>set roots. poly (c (map (\<lambda>i. f \<circ>\<^sub>p XP (g^i)) [0..<2])) (g^r)=0)
    \<longleftrightarrow> poly f 1=a \<and> poly f (g^(L-1))=z \<and>
      (\<forall>i<L-1. poly f (g^(Suc i))=(poly f (g^i))^2)"
  by (auto simp: square_workload_spec_def XP_def poly_pcompose poly_monom mult.commute)

lemma square_workload_endpoint:
  fixes f :: "'f::field poly"
  assumes constraints: "\<forall>(c,roots,d)\<in>set (square_workload_spec L a z).
    \<forall>r\<in>set roots. poly (c (map (\<lambda>i. f \<circ>\<^sub>p XP (g^i)) [0..<2])) (g^r)=0"
  shows "z=a^(2^(L-1))"
proof -
  have start: "poly f 1=a" and finish: "poly f (g^(L-1))=z"
    and step: "\<And>i. i<L-1 \<Longrightarrow> poly f (g^(Suc i))=(poly f (g^i))^2"
    using constraints unfolding square_workload_constraints_iff by auto
  have trace_values: "poly f (g^i)=a^(2^i)" if "i\<le>L-1" for i
    using that
  proof (induction i)
    case 0
    show ?case using start by simp
  next
    case (Suc i)
    have bound: "i<L-1" using Suc.prems by arith
    show ?case using step[OF bound] Suc.IH Suc.prems
      by (simp add: power_mult[symmetric] mult.commute)
  qed
  show ?thesis using finish trace_values[of "L-1"] by simp
qed

lemma square_workload_one_witness:
  fixes g :: "'f::field"
  assumes "0<L"
  shows "degree (1::'f poly)<L \<and>
    (\<forall>(c,roots,d)\<in>set (square_workload_spec L (1::'f) 1).
     \<forall>r\<in>set roots. poly (c (map (\<lambda>i. 1 \<circ>\<^sub>p XP (g^i)) [0..<2])) (g^r)=0)"
  using assms unfolding square_workload_constraints_iff by simp

subsection \<open>Existing verifier obligations over prime residue fields\<close>

text \<open>No locale is added here. The theorem discharges the existing verifier
  predicate from explicit arithmetic conditions. Its unused compatibility
  operation and repetition count are absent from the locale predicate;
  a locale interpretation may choose them freely. The full generator also
  serves as the shift outside the proper evaluation subgroup.\<close>

theorem square_workload_mod_ring_verifier:
  fixes omega a z :: "'a::prime_card mod_ring"
  assumes L: "2\<le>L" "\<exists>k. L=2^k"
    and S: "\<exists>k. S=2^k"
    and order: "exact_order omega (CARD('a)-1)"
    and domain: "L*S dvd CARD('a)-1" "L*S<CARD('a)-1"
  shows "verifier omega omega S L 2
    stark_mod_ring_decode stark_mod_ring_encode CARD('a)
    (square_workload_spec L a z) (square_workload_spec2 L a z)"
proof -
  have spos: "0<S" using S by auto
  have lscale: "L\<le>L*S" using spos by (simp add: leI)
  have nontrivial: "1<L*S" using L lscale by arith
  have two: "(2::'a mod_ring)\<noteq>0"
    by (rule stark_mod_ring_two_nonzero) (use domain lscale L in arith)
  have decode: "stark_mod_ring_decode (stark_mod_ring_encode n :: 'a mod_ring)=n"
    if "n\<le>Max (degrees L (square_workload_spec L a z))" for n
  proof (rule stark_mod_ring_degree_decode[of "L-1"])
    show "L-1<CARD('a)" using domain lscale L by arith
    show "n\<le>L-1" using that by (simp add: square_workload_max_degree[OF L(1)])
  qed
  show ?thesis
  proof (unfold_locales)
    show "CARD('a)=CARD('a mod_ring)" by simp
    show "\<exists>k. L=2^k" by (rule L(2))
    show "\<exists>k. S=2^k" by (rule S)
    show "exact_order omega (CARD('a)-1)" by (rule order)
    show "L*S dvd CARD('a)-1" by (rule domain(1))
    show "1<L*S" by (rule nontrivial)
    show "\<forall>x::'a mod_ring. stark_mod_ring_encode (stark_mod_ring_decode x)=x" by simp
    show "range (stark_mod_ring_decode::'a mod_ring\<Rightarrow>nat)={0..<CARD('a)}"
      by (rule stark_mod_ring_decode_range)
    show "2\<le>L" by (rule L(1))
    show "0<(2::nat)" by simp
    show "omega\<noteq>0" by (rule stark_exact_order_nonzero[OF order])
    show "(2::'a mod_ring)\<noteq>0" by (rule two)
    show "d*(L-1)-length roots<L*S"
      if "(c,roots,d)\<in>set (square_workload_spec L a z)" for c roots d
      by (rule square_workload_degree_fits[OF L(1) spos that])
    show "degree (c (map (\<lambda>p. f \<circ>\<^sub>p XP ((omega^((CARD('a)-1) div L))^p))
          [0..<2])) \<le> d*(L-1)"
      if "degree f<L" "(c,roots,d)\<in>set (square_workload_spec L a z)" for f c roots d
      by (rule square_workload_constraint_degree[OF that])
    show "r<L"
      if "(c,roots,d)\<in>set (square_workload_spec L a z)" "r\<in>set roots" for c roots d r
      by (rule square_workload_roots_in_range[OF L(1) that])
    show "distinct roots" if "(c,roots,d)\<in>set (square_workload_spec L a z)" for c roots d
      by (rule square_workload_roots_distinct[OF that])
    show "omega\<notin>set (map ((^) (omega^((CARD('a)-1) div (L*S)))) [0..<S*L])"
      using stark_full_generator_outside_subgroup[OF order _ domain] L spos
      by (auto simp: mult.commute)
    show "stark_mod_ring_decode (stark_mod_ring_encode n :: 'a mod_ring)=n"
      if "n\<le>Max (degrees L (square_workload_spec L a z))" for n
      by (rule decode[OF that])
    show "list_all2
      (\<lambda>(c,roots,d) (c2,roots2). roots2=roots \<and>
        (\<forall>qs x. 2\<le>length qs \<longrightarrow> c2 (map (\<lambda>q. poly q x) qs)=poly (c qs) x))
      (square_workload_spec L a z) (square_workload_spec2 L a z)"
      by (rule square_workload_specs_aligned)
  qed
qed

corollary square_workload_mod_ring_verifier_exists:
  fixes a z :: "'a::prime_card mod_ring"
  assumes L: "2\<le>L" "\<exists>k. L=2^k" and S: "\<exists>k. S=2^k"
    and domain: "L*S dvd CARD('a)-1" "L*S<CARD('a)-1"
  shows "\<exists>omega::'a mod_ring. verifier omega omega S L 2
    stark_mod_ring_decode stark_mod_ring_encode CARD('a)
    (square_workload_spec L a z) (square_workload_spec2 L a z)"
  using stark_mod_ring_full_generator_exists[where 'a='a]
    square_workload_mod_ring_verifier[OF L S _ domain, where a=a and z=z]
  by blast

text \<open>The reference geometry reproduces workload metadata only. It does not
  certify existence of a selected large prime field or any security level.\<close>

lemma square_workload_reference_metadata:
  "Max (degrees 1024 (square_workload_spec 1024 a z))=1023"
  "sum_list (map (\<lambda>(_,roots,_). length roots) (square_workload_spec 1024 a z))=1025"
  "1024*64-Max (set [0..<2])*64 = (65472::nat)"
  using square_workload_max_degree[of 1024 a z] square_workload_root_sum[of 1024 a z]
  by (simp_all add: numeral_2_eq_2)

end
