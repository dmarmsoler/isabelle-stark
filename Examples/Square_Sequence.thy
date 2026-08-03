(*  Title:      Stark/Square_Sequence.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Square_Sequence
  imports
    Stark_Core.Stark
    "HOL-Number_Theory.Number_Theory"
    Stark_Core.Galois_Field_5
begin

section \<open>Square Sequence Example\<close>

text \<open>
  In the following example we generate a proof for a program which computes the square sequence:
  \<^latex>\<open>$x, x^2,x^4, ...$\<close>
  Since the computation is probabilistic we keep the executable example small: a sequence of size
  \<^latex>\<open>2\<close> with scaling factor \<^latex>\<open>1\<close>.
\<close>

text \<open>
  We use GF(5) - the finite field of order 5 - for our example.
  \<^item> It is a Proth field.
  \<^item> It is large enough for a trace of length 2 with a scaling factor of 1 and a shifted
    evaluation domain disjoint from \<^term>\<open>H\<close>.
  \<^item> It is still feasible to execute probabilistically.
  Larger fields make the executable example substantially more expensive.
\<close>

subsection \<open>Polynomial Constraints\<close>

text \<open>
  The first number in the sequence (at position 0) is \<^latex>\<open>2\<close>
\<close>

definition p0:: "gf5 poly list \<Rightarrow> gf5 poly"
where
  "p0 f \<equiv> f!0 - 2"

definition r0:: "nat list"
where
  "r0 \<equiv> [0]"

text \<open>
  The last number in the sequence (at position 1) is \<^latex>\<open>4\<close>
\<close>

definition p1:: "gf5 poly list \<Rightarrow> gf5 poly"
where
  "p1 f \<equiv> f!0 - 4"

definition r1:: "nat list"
where
  "r1 \<equiv> [1]"

text \<open>
  For all intermediate positions (which is only position \<^latex>\<open>0\<close>)
  the next position is the square of the previous position.
\<close>

definition p2:: "gf5 poly list \<Rightarrow> gf5 poly"
where
  "p2 ps \<equiv> ps ! 1 - (ps ! 0 * ps ! 0)"

definition r2:: "nat list"
where
  "r2 \<equiv> [0..<1]"

text \<open>
  The spec consists of a list containing the above constraints.
  Note that the third parameter in each entry is the degree of the constraint polynomial.
\<close>

definition spec::"((gf5 poly list \<Rightarrow> gf5 poly) \<times> nat list \<times> nat) list"
where
  "spec = [(p0 ,r0, 1), (p1, r1, 1), (p2, r2, 2)]"

text \<open>
  We also need the spec in an other format.
  These need to be equivalent and for the future it should be unified with the other spec.
\<close>

definition p0':: "gf5 list \<Rightarrow> gf5"
where
  "p0' f \<equiv> f!0 - 2"

definition p1':: "gf5 list \<Rightarrow> gf5"
where
  "p1' f \<equiv> f!0 - 4"

definition p2':: "gf5 list \<Rightarrow> gf5"
where
  "p2' ps \<equiv> ps ! 1 - (ps ! 0 * ps ! 0)"

definition spec2::"((gf5 list \<Rightarrow> gf5) \<times> nat list) list"
where
  "spec2 = [(p0', r0), (p1', r1), (p2', r2)]"

subsection \<open>Interpreting the stark locale\<close>

abbreviation tlength::nat where "tlength \<equiv> 2"

lemma of_nat_to_nat:
  fixes n
  assumes "n \<le> Max (degrees tlength spec)"
  shows "Galois_Field_5.to_nat (Galois_Field_5.of_nat n) = n"
proof -
  have "1 * (tlength - 1) - length r0 = 0" unfolding r0_def by simp
  moreover have "1 * (tlength - 1) - length r1 = 0" unfolding r1_def by simp
  moreover have "tlength * (tlength - 1) - length r2 = 1" unfolding r2_def by simp
  ultimately have "degrees tlength spec = {0,1}" unfolding degrees_def spec_def
    apply (auto simp add:r0_def r1_def r2_def)
    by (metis diff_Suc_1' length_Suc_conv list.size(3) numeral_2_eq_2)
  then have "Max (degrees tlength spec) = 1" by simp
  then consider "n = 0" | "n = 1" using assms by linarith
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by (metis nat_zero_as_int of_nat_to_nat to_nat.rep_eq zero_gf5.rep_eq)
  next
    case 2
    then show ?thesis
      by (metis nat_one_as_int of_nat_to_nat one_gf5.rep_eq to_nat.rep_eq)
  qed
qed

lemma exact_order_gf5_2_4:
  "exact_order gf5_2 4"
  unfolding exact_order_def
  apply (intro conjI)
    apply simp
   apply eval
  apply (intro allI impI)
  apply (subgoal_tac "m = 1 \<or> m = 2 \<or> m = 3")
   apply (elim disjE; hypsubst; eval)
  by linarith

lemma gf5_2_nonzero:
  "gf5_2 \<noteq> 0"
  by eval

lemma numeral_2_gf5_nonzero:
  "(2::gf5) \<noteq> 0"
  by eval

lemma square_sequence_spec_degree_fits:
  assumes "(c, roots, d) \<in> set spec"
  shows "d * (tlength - 1) - length roots < tlength * 1"
  using assms
  unfolding spec_def r0_def r1_def r2_def
  by auto

lemma square_sequence_constraint_degree_wellformed:
  assumes deg_f: "degree f < tlength"
    and spec_entry: "(c, roots, d) \<in> set spec"
  shows
    "degree
      (c (map (\<lambda>p. f \<circ>\<^sub>p XP ((gf5_2 ^ ((5 - 1) div tlength)) ^ p))
        [0..<tlength])) \<le> d * (tlength - 1)"
proof -
  let ?fs =
    "map (\<lambda>p. f \<circ>\<^sub>p XP ((gf5_2 ^ ((5 - 1) div tlength)) ^ p))
      [0..<tlength]"
  have deg_XP: "degree (XP a :: gf5 poly) \<le> 1" for a
    unfolding XP_def by (rule degree_monom_le)
  have deg_f_le: "degree f \<le> 1"
    using deg_f by simp
  have compose_le: "degree (f \<circ>\<^sub>p XP a) \<le> 1" for a
  proof -
    have "degree (f \<circ>\<^sub>p XP a) \<le> degree f * degree (XP a)"
      by (rule degree_pcompose_le)
    also have "... \<le> 1"
      using deg_f_le deg_XP[of a] by (cases "degree f"; cases "degree (XP a :: gf5 poly)") auto
    finally show ?thesis .
  qed
  have deg0: "degree (?fs ! 0) \<le> 1"
    using compose_le[of "((gf5_2 ^ ((5 - 1) div tlength)) ^ 0)"] by simp
  have deg1: "degree (?fs ! 1) \<le> 1"
    using compose_le[of "((gf5_2 ^ ((5 - 1) div tlength)) ^ 1)"] by simp
  have deg_square: "degree (?fs ! 0 * ?fs ! 0) \<le> 2"
  proof -
    have "degree (?fs ! 0 * ?fs ! 0) \<le> degree (?fs ! 0) + degree (?fs ! 0)"
      by (rule degree_mult_le)
    also have "... \<le> 2"
      using deg0 by linarith
    finally show ?thesis .
  qed
  show ?thesis
  proof -
    have p0_bound: "degree (?fs ! 0 - 2) \<le> 1"
      using degree_diff_le[OF deg0, of 2] by simp
    have p1_bound: "degree (?fs ! 0 - 4) \<le> 1"
      using degree_diff_le[OF deg0, of 4] by simp
    have p2_bound: "degree (?fs ! 1 - ?fs ! 0 * ?fs ! 0) \<le> 2"
    proof -
      have "degree (?fs ! 1 - ?fs ! 0 * ?fs ! 0) \<le> max (degree (?fs ! 1)) (degree (?fs ! 0 * ?fs ! 0))"
        by (rule degree_diff_le_max)
      also have "... \<le> 2"
        using deg1 deg_square by simp
      finally show ?thesis .
    qed
    show ?thesis
      using spec_entry p0_bound p1_bound p2_bound
      unfolding spec_def p0_def p1_def p2_def
      by auto
  qed
qed

lemma square_sequence_spec_roots_in_range:
  assumes "(c, roots, d) \<in> set spec"
    and "r \<in> set roots"
  shows "r < tlength"
  using assms
  unfolding spec_def r0_def r1_def r2_def
  by auto

lemma square_sequence_spec_roots_distinct:
  assumes "(c, roots, d) \<in> set spec"
  shows "distinct roots"
  using assms
  unfolding spec_def r0_def r1_def r2_def
  by auto

lemma gf5_2_notin_scale1_H_raw:
  "gf5_2 \<notin>
    set (map ((^) (gf5_2 ^ ((5 - 1) div (tlength * 1)))) [0..<1 * tlength])"
  by eval

lemma gf5_to_nat_range:
  "range Galois_Field_5.to_nat = {0..<5}"
proof -
  have vals:
    "Galois_Field_5.to_nat gf5_0 = 0"
    "Galois_Field_5.to_nat gf5_1 = 1"
    "Galois_Field_5.to_nat gf5_2 = 2"
    "Galois_Field_5.to_nat gf5_3 = 3"
    "Galois_Field_5.to_nat gf5_4 = 4"
    by eval+
  have mems:
    "0 \<in> range Galois_Field_5.to_nat"
    "1 \<in> range Galois_Field_5.to_nat"
    "2 \<in> range Galois_Field_5.to_nat"
    "3 \<in> range Galois_Field_5.to_nat"
    "4 \<in> range Galois_Field_5.to_nat"
    using vals by (metis rangeI)+
  have "range Galois_Field_5.to_nat \<subseteq> {0..<5}"
  proof
    fix n :: nat
    assume "n \<in> range Galois_Field_5.to_nat"
    then obtain x where n_eq: "n = Galois_Field_5.to_nat x"
      by blast
    show "n \<in> {0..<5}"
      unfolding n_eq
      by (cases x; simp add: vals)
  qed
  moreover have "{0..<5} \<subseteq> range Galois_Field_5.to_nat"
  proof
    fix n :: nat
    assume "n \<in> {0..<5}"
    then have "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4"
      by auto
    then show "n \<in> range Galois_Field_5.to_nat"
      using mems by auto
  qed
  ultimately show ?thesis
    by blast
qed

lemma square_sequence_query_sample_space_size_dvd:
  "tlength * 1 - Max (set [0..<tlength]) * 1 dvd 5"
  by eval

global_interpretation
  stark:
    stark
      concat_gf5 gf5_2 gf5_2 1 tlength 2 Galois_Field_5.to_nat Galois_Field_5.of_nat 5 spec 1
  defines stark_send = channel.send
      and stark_send2 = channel.send2
      and stark_read = channel.read
      and stark_g = stark.g
      and stark_G = stark.G
      and stark_h = stark.h
      and stark_H = stark.H
      and stark_eval_domain = stark.eval_domain
      and stark_powers_scaled = stark.powers_scaled
      and stark_index = stark.index
      and stark_g_map = stark.g_map
      and stark_maxDegree = stark.maxDegree
      and stark_cp = stark.cp
  apply standard
                 apply simp
                apply (rule exI[where x=1], simp)
               apply (rule exI[where x=0], simp)
              apply (simp add: exact_order_gf5_2_4)
             apply simp
            apply simp
           apply simp
          apply (rule gf5_to_nat_range)
          apply simp
        apply simp
       apply (rule square_sequence_query_sample_space_size_dvd)
      apply (rule gf5_2_nonzero)
     apply (rule numeral_2_gf5_nonzero)
    apply (erule square_sequence_spec_degree_fits)
     apply (erule (1) square_sequence_constraint_degree_wellformed)
    apply (erule (1) square_sequence_spec_roots_in_range)
   apply (erule square_sequence_spec_roots_distinct)
  apply (rule gf5_2_notin_scale1_H_raw)
  using of_nat_to_nat by presburger

subsection \<open>Interpretation of prover locale\<close>

definition trace where "trace = [2,4]"

lemma length_trace: "length trace = tlength" unfolding trace_def by simp

global_interpretation
    prover:
    prover
      concat_gf5 gf5_2 gf5_2 1 tlength 2 Galois_Field_5.to_nat Galois_Field_5.of_nat 5 spec 1 trace
  defines prover_f = prover.f
    and prover_f_eval = prover.f_eval
    and prover_cp_eval = prover.cp_eval
    and prover_next_fri_domain = prover.next_fri_domain
    and prover_next_fri_polynomial = prover.next_fri_polynomial
    and prover_next_fri_layer = prover.next_fri_layer
    and prover_fri_commit = prover.fri_commit
    and prover_decommit_on_fri_layers = prover.decommit_on_fri_layers
    and prover_decommit_on_query = prover.decommit_on_query
    and prover_sproof = prover.sproof
    and prover_prover_monad = prover.prover_monad
    and prover_f_powers = prover.f_powers
  apply (rule prover.intro)
  apply standard
  using length_trace by metis

subsection \<open>Interpretation of verifier locale\<close>

lemma nth_map_tlength_0[simp]:
  assumes "tlength \<le> length xs"
  shows "map f xs ! 0 = f (xs ! 0)"
  by (rule nth_map) (use assms in linarith)

lemma nth_map_tlength_1[simp]:
  assumes "tlength \<le> length xs"
  shows "map f xs ! 1 = f (xs ! 1)"
  by (rule nth_map) (use assms in linarith)

global_interpretation
    verifier:
    verifier
     concat_gf5 gf5_2 gf5_2 1 tlength 2 Galois_Field_5.to_nat Galois_Field_5.of_nat 5 spec 1 spec2
  defines verifier_receive_fri_commits = verifier.receive_fri_commits
      and verifier_receive_query_commits = verifier.receive_query_commits
      and verifier_check_decommit_on_query = verifier.check_decommit_on_query
      and verifier_verify = verifier.verify
      and verifier_cp_eval = verifier.cp_eval
      and verifier_verify_monad = verifier.verify_monad
  apply (rule verifier.intro)
  apply standard
  by (auto simp: spec_def spec2_def p0_def p1_def p2_def p0'_def p1'_def p2'_def)

subsection \<open>Creating and Verifying Proof\<close>

text \<open>
  The executable prover state can be inspected with \<open>value "prover_sproof"\<close>.
  Concrete verifier transcripts are intentionally not hard-coded here: the transcript
  shape changes when protocol checks such as trace FRI are added.
\<close>

end
