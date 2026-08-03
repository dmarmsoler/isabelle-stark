(*  Title:      Stark/Stark.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Stark
  imports
    Main
    Merkle_Tree
    Channel
    "Polynomial_Interpolation.Lagrange_Interpolation"

begin

section \<open>Stark Protocol\<close>

text \<open>
  This theory defines the executable prover and verifier monads for the STARK
  protocol formalized in this entry.  It also fixes the common domain
  parameters, transcript operations, Merkle commitments, query sampler, and
  FRI folding routines used by the completeness and soundness developments.

  The formalization follows the structure of the StarkWare STARK tutorial and
  the algebraic framework described in the STARK literature.  The field class
  uses Proth fields because their multiplicative groups provide the
  power-of-two subgroups used for FFT-style evaluation domains.
\<close>

subsection \<open>Preliminaries\<close>

definition ceil_log :: "nat \<Rightarrow> nat" where
  "ceil_log n = (if n \<le> 1 then 0 else Suc (floor_log (n - 1)))"

subsubsection \<open>Filter list by predicate over length\<close>

text \<open>
  There exists \<^term>\<open>nths\<close> in List which does what we want but it cannot be executed.
  Thus, we introduce a new function with a corresponding code equation which makes it executable.
\<close>

definition nths_pred
where
  "nths_pred xs P \<equiv> nths xs (Collect P)"

lemma nths_pred_nths[code]:
  "nths_pred xs P = map fst (filter (\<lambda>p. P (snd p)) (zip xs ([0..<length xs])))"
  unfolding nths_pred_def nths_def by simp

lemma nths_pred_alt_def[simp]:
  "nths_pred xs P = nths xs (Collect P)"
  unfolding nths_pred_def ..

lemma "nths_pred ([5,6,3,4]::nat list) even = [5,3]" by eval
lemma "nths_pred ([5,6,3]::nat list) even = [5,3]" by eval
lemma "nths_pred ([5,6,3]::nat list) odd = [6]" by eval
lemma "nths_pred ([6,3]::nat list) even = [6]" by eval
lemma "nths_pred ([6,3]::nat list) odd = [3]" by eval

lemma nths_pred_length_leq:
  "length (nths_pred xs P) \<le> length xs"
  unfolding nths_pred_def nths_def
  by (metis length_filter_le length_map map_fst_zip map_nth)

text \<open>
  Many properties can be more easily proven if we use @{term "zip xs (rev [0..<length xs])"}.
  Thus, we introduce the following lemmas which can be used to convert the lemmas back to @{term "nths_pred"}.
\<close>

lemma filter_zip_lcomp:
  assumes "xs \<noteq> []"
  shows
    "filter (\<lambda>p. P (snd p)) (zip xs [0..<length xs]) = [(xs!i,i). i \<leftarrow> filter P [0..<length xs]]"
  using assms
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case
  proof (cases "P (length xs)")
    case True
    then have
      "filter (\<lambda>p. P (snd p)) (zip (xs @ [x]) [0..<length (xs @ [x])])
       = (filter (\<lambda>p. P (snd p)) (zip (xs) [0..< (length xs)])) @ [(x, (length xs))]"
      using snoc.prems by auto
    also from snoc.IH
    have "\<dots> = map (\<lambda>i. (xs ! i, i)) (filter P [0..<length xs]) @ [(x,(length xs))]"
      by fastforce
    also have "\<dots> = map (\<lambda>i. ((xs @ [x]) ! i, i)) (filter P [0..<length (xs @ [x])])"
      using snoc.prems True by (auto simp add: nth_append_left)
    finally show ?thesis .
  next
    case False
    then have
      "filter (\<lambda>p. P (snd p)) (zip (xs @ [x]) [0..<length (xs @ [x])])
       = (filter (\<lambda>p. P (snd p)) (zip (xs) [0..< (length xs)]))"
      using snoc.prems by auto
    also from snoc have "\<dots> = map (\<lambda>i. (xs ! i, i)) (filter P [0..<length xs])" by fastforce
    also have "\<dots> = map (\<lambda>i. ((xs @ [x]) ! i, i)) (filter P [0..<length ((xs @ [x]))])"
      using snoc.prems False by (auto simp add: nth_append_left)
    finally show ?thesis .
  qed
qed

lemma filter_zip_rev_lcomp:
  assumes "xs \<noteq> []"
  shows
    "filter (\<lambda>p. P (snd p)) (zip xs (rev [0..<length xs]))
    = [(xs!(length xs - (Suc i)),i) . i \<leftarrow> filter P (rev [0..<length xs])]"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases "P (length xs)")
    case True
    then have
      "filter (\<lambda>p. P (snd p)) (zip (x # xs) (rev [0..<length (x # xs)]))
       = (x, (length xs)) # (filter (\<lambda>p. P (snd p)) (zip xs (rev [0..< length xs])))"
      using Cons.prems by auto
    also from Cons.IH have
      "\<dots> = (x,(length xs)) #  map (\<lambda>i. (xs ! (length xs - (Suc i)), i)) (filter P (rev [0..<length xs]))"
        by fastforce
    also have
      "\<dots> =  map (\<lambda>i. ((x # xs) ! (length (x # xs) - Suc i), i)) (filter P (rev [0..<length (x # xs)]))"
        using Cons.prems True by simp
    finally show ?thesis .
  next
    case False
    then have
      "filter (\<lambda>p. P (snd p)) (zip (x # xs) (rev [0..<length (x # xs)]))
       = filter (\<lambda>p. P (snd p)) (zip xs (rev [0..< length xs]))"
      using Cons.prems by auto
    also from Cons.IH
    have "\<dots> = map (\<lambda>i. (xs ! (length xs - (Suc i)), i)) (filter P (rev [0..<length xs]))"
      by fastforce
    also have "\<dots> = map (\<lambda>i. ((x # xs) ! (length (x # xs) - Suc i), i)) (filter P (rev [0..<length (x # xs)]))"
      using Cons.prems False by simp
    finally show ?thesis .
  qed
qed

lemma length_filter_zip_length_rev:
  "length (filter (\<lambda>p. P (snd p)) (zip xs ([0..<length xs])))
   = length (filter (\<lambda>p. P (snd p)) (zip xs (rev [0..<length xs])))"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  then have "length (map (\<lambda>i. (xs ! i, i)) (filter P [0..<length xs]))
               = length (map (\<lambda>i. (xs ! (length xs - Suc i), i)) (filter P (rev [0..<length xs])))"
    by (metis length_map length_rev rev_filter)
  then show ?thesis using filter_zip_lcomp[of xs P] filter_zip_rev_lcomp[of xs P]
    by fastforce
qed

text \<open>
  The following two lemmas are example of what can be easily provern if we use @{term "rev [0..<length xs]"}
\<close>

lemma nths_pred_even_length_eq:
  "length (nths_pred xs even) = (Suc (length xs)) div 2"
proof -
  have "length (map fst (filter (\<lambda>p. even (snd p)) (zip xs (rev [0..<length xs])))) = Suc (length xs) div 2"
    by (induction xs, auto)
  then show ?thesis using length_filter_zip_length_rev[of even xs] by (simp add: nths_def)
qed

lemma nths_pred_odd_length_eq:
  "length (nths_pred xs odd) = (length xs) div 2"
proof -
  have "length (map fst (filter (\<lambda>p. odd (snd p)) (zip xs (rev [0..<length xs])))) = length xs div 2"
    by (induction xs, auto)
  then show ?thesis using length_filter_zip_length_rev[of odd xs] by (simp add: nths_def)
qed

lemma nths_pred_even_length_less:
  assumes "length xs > 1"
  shows "length (nths_pred xs even) < length xs"
  using assms nths_pred_even_length_eq[of xs]
  by linarith

lemma nths_pred_odd_length_less:
  assumes "length xs > 1"
  shows "length (nths_pred xs odd) < length xs"
  using assms nths_pred_odd_length_eq[of xs]
  by linarith

subsubsection \<open>Basic polynomial definitions\<close>

definition XP
where
  "XP x \<equiv> monom x 1"

definition CP
where
  "CP x \<equiv> monom x 0"

definition prod
where
  "prod xs \<equiv> fold (\<lambda>s. (*) (XP 1 - CP s)) xs 1"

subsection \<open>Stark Specifications\<close>

definition degrees
  where "degrees clength spec = insert 0 {d * (clength - 1) - length rs | a rs d. (a,rs,d) \<in> set spec}"

definition exact_order :: "'a::monoid_mult \<Rightarrow> nat \<Rightarrow> bool"
  where
    "exact_order a n \<longleftrightarrow>
      0 < n \<and> a ^ n = 1 \<and> (\<forall>m. 0 < m \<and> m < n \<longrightarrow> a ^ m \<noteq> 1)"

locale stark =
  protocol_channel_compat +
  constrains omega::"'f::proth_field"
    and shift::"'f"
    and g::"'f"
    and h::"'f"
    and vals::"'f list"
    and concat :: "'f \<Rightarrow> 'f \<Rightarrow> 'f"
  fixes omega::"'f::proth_field" \<comment> \<open>This is assumed to be a generator of \<^typ>\<open>'f\<close>\<close>
    and shift::"'f" \<comment> \<open>This shifts \<^term>\<open>H\<close> to the evaluation-domain coset.\<close>
    and scale::nat \<comment> \<open>This is the scaling or blow-up factor\<close>
    and clength::"nat"
      \<comment> \<open>The length of the computation, it does need to be a power of two
          or else needs to be padded to the next power of 2\<close>
    and powers::"nat"
      \<comment> \<open>The number of powers of the generator required for the spec \<^term>\<open>[0 ..< powers]\<close>.
          This is basically the size of the list which is passed to the first element of \<^term>\<open>spec\<close>\<close>
    and to_nat::"'f \<Rightarrow> nat"
    and of_nat::"nat \<Rightarrow> 'f"
      \<comment> \<open>Functions to transfer from \<^typ>\<open>'f\<close> to the field and back\<close>
    and size::"nat"
    \<comment> \<open>The size of \<^typ>\<open>'f\<close>\<close>
    and spec:: "(('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat) list"
    \<comment> \<open>The specification consists of a list of three elements:
        A constraint polynomial, i.e., a function which creates a polynomial from a list of polynomials
        (the input here is assumed to be the trace polynomial scaled by powers of the generator);
        A list of roots for a given constraint polynomial;
        The degree of the constraint polynomial (actually this could be computed but for now we give it explicitly)\<close>
    and rounds::nat
  assumes size_card: "size = CARD('f)" \<comment> \<open>This is just there since CARD cannot be computed\<close>
    and clength_pow: "\<exists>k. clength = 2 ^ k"
      \<comment> \<open>We assume the trace has correct length. In reality this is not required since we can just add padding.\<close>
    and scale_pow: "\<exists>k. scale = 2 ^ k" \<comment> \<open>This needs to be a power of two to make definition of h well-defined\<close>
    and omega_order: "exact_order omega (size - 1)"
      \<comment> \<open>\<^term>\<open>omega\<close> is a primitive generator of the multiplicative group.\<close>
    and eval_domain_dvd: "clength * scale dvd size - 1"
    and eval_domain_nontrivial: "1 < clength * scale"
    and of_nat_to_nat: "\<forall>x. of_nat (to_nat x) = x"
    and to_nat_range:
      "range to_nat = {0..<size}"
      \<comment> \<open>
        Exact-uniformity assumption for the current query sampler, which
        samples a field element and maps it through \<^term>\<open>to_nat\<close> and
        modulo reduction.  A direct sampler over the query sample space, or a
        rejection sampler with a proved distribution, would remove this
        divisibility condition from the protocol locale.
      \<close>
    and powers_le_clength: "powers \<le> clength"
    and powers_pos: "0 < powers"
    and query_sample_space_size_dvd:
      "clength * scale - Max (set [0..<powers]) * scale dvd size"
      \<comment> \<open>
        Exact-uniformity assumption for modulo reduction into the current
        query sample space.  It is specific to the current field-element
        encoding based sampler.
      \<close>
    and shift_nonzero: "shift \<noteq> 0"
    and two_nonzero: "(2::'f) \<noteq> 0"
    and spec_degree_fits:
      "\<And>c roots d.
        (c, roots, d) \<in> set spec \<Longrightarrow>
        d * (clength - 1) - length roots < clength * scale"
    and constraint_degree_wellformed_raw:
      "\<And>f c roots d.
        degree f < clength \<Longrightarrow>
        (c, roots, d) \<in> set spec \<Longrightarrow>
        degree
          (c (map
            (\<lambda>p. f \<circ>\<^sub>p XP ((omega ^ ((size - 1) div clength)) ^ p))
            [0..<powers]))
          \<le> d * (clength - 1)"
    and spec_roots_in_range:
      "\<And>c roots d r.
        (c, roots, d) \<in> set spec \<Longrightarrow>
        r \<in> set roots \<Longrightarrow>
        r < clength"
    and spec_roots_distinct:
      "\<And>c roots d.
        (c, roots, d) \<in> set spec \<Longrightarrow>
        distinct roots"
    and shift_notin_H_raw:
      "shift \<notin>
        set (map ((^) (omega ^ ((size - 1) div (clength * scale))))
          [0..<scale * clength])"
    and to_nat_of_nat_bounded: "\<And>n. n \<le> Max (degrees clength spec) \<Longrightarrow> to_nat (of_nat n) = n"
begin

subsubsection \<open>Lemmas\<close>

lemma scale_pos: "0 < scale"
  using scale_pow
  by auto

lemma clength_pos: "0 < clength"
  using clength_pow by auto

lemma eval_domain_size_pos: "0 < clength * scale"
  using eval_domain_nontrivial by linarith

lemma of_nat_to_nat_field:
  "of_nat (to_nat x) = x"
  using of_nat_to_nat by simp

lemma to_nat_inj:
  "inj to_nat"
proof (rule injI)
  fix x y
  assume eq: "to_nat x = to_nat y"
  have "of_nat (to_nat x) = of_nat (to_nat y)"
    using eq by simp
  then show "x = y"
    using of_nat_to_nat_field by simp
qed

lemma finite_range_to_nat[simp]:
  "finite (range to_nat)"
  by simp

lemma card_range_to_nat:
  "card (range to_nat) = size"
proof -
  have range_eq: "range to_nat = to_nat ` (UNIV :: 'f set)"
    by blast
  have inj_univ: "inj_on to_nat (UNIV :: 'f set)"
    using to_nat_inj by (simp add: inj_on_def inj_def)
  have card_img:
      "card (to_nat ` (UNIV :: 'f set)) = card (UNIV :: 'f set)"
    by (rule card_image[OF inj_univ])
  have card_univ: "card (UNIV :: 'f set) = size"
    using size_card by simp
  show ?thesis
    using range_eq card_img card_univ by simp
qed

lemma eval_domain_length_power: "\<exists>n. clength * scale = 2 ^ n"
proof -
  obtain k l where "clength = 2 ^ k" and "scale = 2 ^ l"
    using clength_pow scale_pow by blast
  then have "clength * scale = 2 ^ (k + l)"
    by (simp add: power_add)
  then show ?thesis
    by blast
qed

lemma omega_power_size_minus_one:
  "omega ^ (size - 1) = 1"
  using omega_order unfolding exact_order_def by simp

lemma omega_nonzero_derived:
  "omega \<noteq> 0"
proof
  assume omega_zero: "omega = 0"
  have size_pos: "0 < size - 1"
    using omega_order unfolding exact_order_def by simp
  then obtain n where size_eq: "size - 1 = Suc n"
    by (cases "size - 1") auto
  have "(0::'f) = 1"
    using omega_power_size_minus_one omega_zero size_eq by simp
  then show False
    by simp
qed

subsubsection \<open>Basic definitions\<close>

text \<open>
  \<^term>\<open>G\<close> is a subgroup of \<^latex>\<open>$'f^x$\<close> (the multiplicative group of \<^typ>\<open>'f\<close>).
  It is generated by generator \<^term>\<open>g\<close> and contains exactly as many elements as the length of the (padded) execution trace.
\<close>
definition g
where
  "g \<equiv> omega^((size - 1) div clength)"

definition trace_powers_of :: "'f poly \<Rightarrow> 'f poly list"
  where "trace_powers_of f = map (\<lambda>p. f \<circ>\<^sub>p XP (g ^ p)) [0..<powers]"

lemma trace_powers_of_length[simp]:
  "length (trace_powers_of f) = powers"
  unfolding trace_powers_of_def by simp

lemma constraint_degree_wellformed:
  \<comment> \<open>This locale fact records a syntactic degree side condition for
      \<^term>\<open>spec\<close>.  A stronger syntactic degree-analysis interface could
      derive it in a later refinement of the specification layer.\<close>
  assumes "degree f < clength"
    and "(c, roots, d) \<in> set spec"
  shows "degree (c (trace_powers_of f)) \<le> d * (clength - 1)"
  using constraint_degree_wellformed_raw[OF assms]
  unfolding trace_powers_of_def g_def .

definition G
where
  "G = map ((^) g) [0..<clength]"

text \<open>
  \<^term>\<open>H\<close> is again subgroup of \<^latex>\<open>$'f^x$\<close>.
  Its size is the size of \<^term>\<open>G\<close> scaled by the scaling factor \<^term>\<open>scale\<close>.
  It is generated by generator \<^term>\<open>h\<close>.
\<close>
definition h
where
  "h \<equiv> omega^((size - 1) div (clength * scale))"

definition H
where
  "H = map ((^) h) [0..<scale * clength]"  \<comment> \<open>Since both scale and clength are powers of two their product is a power of two as well\<close>

lemma shift_notin_H:
  "shift \<notin> set H"
  using shift_notin_H_raw
  unfolding H_def h_def .

text \<open>
  We generate a Coset(\<^url>\<open>https://en.wikipedia.org/wiki/Coset\<close>) of \<^term>\<open>H\<close> for our evaluation domain
  by multiplying each element with a nonzero shift.
\<close>

definition eval_domain
where
  "eval_domain = map ((*) shift) H"

text \<open>
  This function creates the indices which need to be evaluated for the de-commitment phase.
  Note that the verifier needs to obtain values of \<^term>\<open>f\<close> for all the powers in powers to compute the constraint polynomial.
  Also, in the flat representation a power actually means that the index is multiplied by the scale factor.
\<close>

definition powers_scaled
where
  "powers_scaled idx \<equiv> map (\<lambda>x. idx + (x * scale)) [0 ..< powers]"

definition index
where
  "index x = x mod ((clength * scale) - ((Max (set [0 ..< powers])) * scale))"

definition g_map
where
  "g_map rs = (map ((^) g) rs)"

lemma domain_alignment:
  "g = h ^ scale"
proof -
  let ?N = "clength * scale"
  obtain q where q_def: "size - 1 = ?N * q"
    using eval_domain_dvd unfolding dvd_def by blast
  have div_mult:
    "(size - 1) div clength = ((size - 1) div (clength * scale)) * scale"
    using q_def scale_pos clength_pos
    by (simp add: mult.assoc)
  have "h ^ scale = omega ^ (((size - 1) div (clength * scale)) * scale)"
    unfolding h_def by (simp add: power_mult)
  also have "... = omega ^ ((size - 1) div clength)"
    using div_mult by simp
  finally show ?thesis
    unfolding g_def by simp
qed

lemma g_exact_order:
  "exact_order g clength"
proof -
  let ?N = "clength"
  let ?M = "size - 1"
  have dvd_clength: "clength dvd ?M"
    using eval_domain_dvd by (meson dvd_mult_left dvd_trans)
  obtain q where q_def: "?M = ?N * q"
    using dvd_clength unfolding dvd_def by blast
  have N_pos: "0 < ?N"
    using clength_pos .
  have q_pos: "0 < q"
    using q_def omega_order unfolding exact_order_def by (cases q) auto
  have gN: "g ^ ?N = 1"
  proof -
    have "g ^ ?N = omega ^ (((size - 1) div ?N) * ?N)"
      unfolding g_def by (simp add: power_mult)
    also have "... = omega ^ (size - 1)"
      using q_def N_pos by (simp add: mult.commute)
    also have "... = 1"
      by (rule omega_power_size_minus_one)
    finally show ?thesis .
  qed
  have no_smaller: "\<And>m. 0 < m \<and> m < ?N \<Longrightarrow> g ^ m \<noteq> 1"
  proof
    fix m
    assume m_bounds: "0 < m \<and> m < ?N"
    assume gm: "g ^ m = 1"
    have exp_lt: "q * m < ?M"
      using m_bounds q_def q_pos by (simp add: mult_less_mono2)
    have exp_pos: "0 < q * m"
      using m_bounds q_pos by simp
    have g_eq: "g = omega ^ q"
      using q_def N_pos unfolding g_def by simp
    have "omega ^ (q * m) = 1"
      using gm g_eq by (simp add: power_mult)
    then show False
      using omega_order exp_pos exp_lt unfolding exact_order_def by blast
  qed
  show ?thesis
    unfolding exact_order_def using N_pos gN no_smaller by blast
qed

lemma g_nonzero:
  "g \<noteq> 0"
  unfolding g_def using omega_nonzero_derived by simp

lemma g_power_inj_on_range:
  assumes i_bound: "i < clength"
    and j_bound: "j < clength"
    and eq: "g ^ i = g ^ j"
  shows "i = j"
proof (rule ccontr)
  assume neq: "i \<noteq> j"
  consider "i < j" | "j < i"
    using neq by linarith
  then show False
  proof cases
    case 1
    have diff_pos: "0 < j - i"
      using 1 by simp
    have diff_lt: "j - i < clength"
      using j_bound by simp
    have gi_nonzero: "g ^ i \<noteq> 0"
      using g_nonzero by simp
    have j_decomp: "j = i + (j - i)"
      using 1 by simp
    have mult_eq: "g ^ j = g ^ i * g ^ (j - i)"
      by (subst j_decomp) (simp add: power_add)
    have cancel_eq: "g ^ i * 1 = g ^ i * g ^ (j - i)"
      using eq mult_eq by simp
    have "g ^ i = 0 \<or> 1 = g ^ (j - i)"
      using cancel_eq by (simp only: mult_cancel_left)
    then have "g ^ (j - i) = 1"
      using g_nonzero by auto
    then show False
      using g_exact_order diff_pos diff_lt unfolding exact_order_def by blast
  next
    case 2
    have diff_pos: "0 < i - j"
      using 2 by simp
    have diff_lt: "i - j < clength"
      using i_bound by simp
    have gj_nonzero: "g ^ j \<noteq> 0"
      using g_nonzero by simp
    have i_decomp: "i = j + (i - j)"
      using 2 by simp
    have mult_eq: "g ^ i = g ^ j * g ^ (i - j)"
      by (subst i_decomp) (simp add: power_add)
    have cancel_eq: "g ^ j * 1 = g ^ j * g ^ (i - j)"
      using eq mult_eq by simp
    have "g ^ j = 0 \<or> 1 = g ^ (i - j)"
      using cancel_eq by (simp only: mult_cancel_left)
    then have "g ^ (i - j) = 1"
      using g_nonzero by auto
    then show False
      using g_exact_order diff_pos diff_lt unfolding exact_order_def by blast
  qed
qed

lemma h_order:
  "h ^ (clength * scale) = 1"
proof -
  let ?N = "clength * scale"
  obtain q where q_def: "size - 1 = ?N * q"
    using eval_domain_dvd unfolding dvd_def by blast
  have "h ^ ?N = omega ^ (((size - 1) div ?N) * ?N)"
    unfolding h_def by (simp add: power_mult)
  also have "... = omega ^ (size - 1)"
    using q_def eval_domain_size_pos by (simp add: mult.commute)
  also have "... = 1"
    by (rule omega_power_size_minus_one)
  finally show ?thesis .
qed

lemma h_exact_order:
  "exact_order h (clength * scale)"
proof -
  let ?N = "clength * scale"
  let ?M = "size - 1"
  obtain q where q_def: "?M = ?N * q"
    using eval_domain_dvd unfolding dvd_def by blast
  have N_pos: "0 < ?N"
    using eval_domain_size_pos .
  have q_pos: "0 < q"
    using q_def omega_order unfolding exact_order_def by (cases q) auto
  have hN: "h ^ ?N = 1"
    by (rule h_order)
  have no_smaller: "\<And>m. 0 < m \<and> m < ?N \<Longrightarrow> h ^ m \<noteq> 1"
  proof
    fix m
    assume m_bounds: "0 < m \<and> m < ?N"
    assume hm: "h ^ m = 1"
    have exp_lt: "q * m < ?M"
      using m_bounds q_def q_pos by (simp add: mult_less_mono2)
    have exp_pos: "0 < q * m"
      using m_bounds q_pos by simp
    have h_eq: "h = omega ^ q"
      using q_def N_pos unfolding h_def by simp
    have "omega ^ (q * m) = 1"
      using hm h_eq by (simp add: power_mult)
    then show False
      using omega_order exp_pos exp_lt unfolding exact_order_def by blast
  qed
  show ?thesis
    unfolding exact_order_def using N_pos hN no_smaller by blast
qed

lemma square_eq_one_imp_eq_one_or_neg_one:
  fixes x :: 'f
  assumes "x * x = 1"
  shows "x = 1 \<or> x = -1"
proof -
  have "(x - 1) * (x + 1) = 0"
    using assms by (simp add: algebra_simps)
  then have "x - 1 = 0 \<or> x + 1 = 0"
    by (simp add: mult_eq_0_iff)
  then show ?thesis
  proof
    assume "x - 1 = 0"
    then show ?thesis by simp
  next
    assume "x + 1 = 0"
    then have "x = -1"
      by (simp add: add_eq_0_iff2)
    then show ?thesis by simp
  qed
qed

lemma h_half_order:
  "h ^ ((clength * scale) div 2) = -1"
proof -
  let ?N = "clength * scale"
  obtain k l where clength_eq: "clength = 2 ^ k" and scale_eq: "scale = 2 ^ l"
    using clength_pow scale_pow by blast
  have N_power: "?N = 2 ^ (k + l)"
    using clength_eq scale_eq by (simp add: power_add)
  have N_gt_one: "1 < ?N"
    using eval_domain_nontrivial .
  then have exp_pos: "0 < ?N div 2"
    by simp
  have exp_lt: "?N div 2 < ?N"
    using N_gt_one by simp
  have h_exp_ne_one: "h ^ (?N div 2) \<noteq> 1"
    using h_exact_order exp_pos exp_lt unfolding exact_order_def by blast
  have square_one: "(h ^ (?N div 2)) * (h ^ (?N div 2)) = 1"
  proof -
    have even_N: "even ?N"
      using N_power N_gt_one by (cases "k + l") simp_all
    have "(h ^ (?N div 2)) * (h ^ (?N div 2)) = h ^ (?N div 2 + ?N div 2)"
      by (simp add: power_add)
    also have "... = h ^ ?N"
    proof -
      have "?N div 2 + ?N div 2 = ?N"
        using even_two_times_div_two[OF even_N] by presburger
      then show ?thesis
        by simp
    qed
    also have "... = 1"
      by (rule h_order)
    finally show ?thesis .
  qed
  show ?thesis
    using square_eq_one_imp_eq_one_or_neg_one[OF square_one] h_exp_ne_one by blast
qed

lemma h_power_mod_domain:
  "h ^ (k mod (clength * scale)) = h ^ k"
proof -
  let ?N = "clength * scale"
  have order: "h ^ ?N = 1"
    using h_order .
  have k_eq: "k = (k div ?N) * ?N + k mod ?N"
    using div_mult_mod_eq[of k ?N] by (simp add: mult.commute)
  have period: "h ^ ((k div ?N) * ?N) = 1"
  proof -
    have "h ^ ((k div ?N) * ?N) = h ^ (?N * (k div ?N))"
      by (simp add: mult.commute)
    also have "... = (h ^ ?N) ^ (k div ?N)"
      by (simp only: power_mult)
    also have "... = 1"
      using order by simp
    finally show ?thesis .
  qed
  have "h ^ k = h ^ ((k div ?N) * ?N + k mod ?N)"
    using k_eq by simp
  also have "... = h ^ ((k div ?N) * ?N) * h ^ (k mod ?N)"
    by (simp add: power_add)
  also have "... = h ^ (k mod ?N)"
    using period by simp
  finally show ?thesis
    by simp
qed

lemma h_power_in_H:
  "h ^ k \<in> set H"
proof -
  let ?N = "clength * scale"
  have mod_bound: "k mod ?N < scale * clength"
    using eval_domain_size_pos
    by (simp add: mult.commute)
  have "h ^ (k mod ?N) \<in> set H"
    unfolding H_def using mod_bound by simp
  then show ?thesis
    using h_power_mod_domain[of k] by simp
qed

lemma eval_coset_disjoint_from_H:
  assumes idx_bound: "i < clength * scale"
  shows "h ^ i * shift \<notin> set H"
proof
  let ?N = "clength * scale"
  assume in_H: "h ^ i * shift \<in> set H"
  then obtain j where j_bound: "j < ?N"
    and eq: "h ^ i * shift = h ^ j"
    unfolding H_def by (auto simp: mult.commute)
  have h_nonzero: "h \<noteq> 0"
    unfolding h_def using omega_nonzero_derived by simp
  have h_i_nonzero: "h ^ i \<noteq> 0"
    using h_nonzero by simp
  have inverse_eq: "inverse (h ^ i) = h ^ (?N - i)"
  proof (rule inverse_unique)
    have "h ^ i * h ^ (?N - i) = h ^ (i + (?N - i))"
      by (simp add: power_add)
    also have "... = h ^ ?N"
      using idx_bound by simp
    also have "... = 1"
      using h_order .
    finally show "h ^ i * h ^ (?N - i) = 1" .
  qed
  have shift_eq: "shift = h ^ j * inverse (h ^ i)"
  proof -
    have eq': "shift * h ^ i = h ^ j"
      using eq by (simp only: mult.commute)
    have "shift = shift * (h ^ i * inverse (h ^ i))"
      using h_i_nonzero by simp
    also have "... = shift * h ^ i * inverse (h ^ i)"
      by (simp add: mult.assoc)
    also have "... = h ^ j * inverse (h ^ i)"
      using eq' by simp
    finally show ?thesis .
  qed
  have "shift = h ^ (j + (?N - i))"
    using shift_eq inverse_eq by (simp add: power_add)
  then have "shift \<in> set H"
    using h_power_in_H[of "j + (?N - i)"] by simp
  then show False
    using shift_notin_H by contradiction
qed

lemma clength_lt_size:
  "clength < size"
proof -
  have size_minus_pos: "0 < size - 1"
    using omega_order unfolding exact_order_def by simp
  have size_minus_ge: "clength * scale \<le> size - 1"
    using eval_domain_dvd eval_domain_size_pos size_minus_pos
    by (meson dvd_imp_le)
  have "clength \<le> clength * scale"
    using scale_pos by simp
  also have "... \<le> size - 1"
    using size_minus_ge .
  finally show ?thesis
    using size_minus_pos by linarith
qed

definition maxDegree
  where "maxDegree = Max (degrees clength spec)"

lemma maxDegree_code[code]:
"maxDegree = foldl (\<lambda>x (_,rs,d). max x (d * (clength - 1) - length rs)) 0 spec"
proof -
  let ?deg = "\<lambda>(_, rs, d). d * (clength - 1) - length rs"
  have Max_insert_max:
    "finite A \<Longrightarrow> Max (insert (max x y) A) = Max (insert x (insert y A))"
    for A :: "nat set" and x y
    by (cases "A = {}") (auto)
  have deg_set: "{d * (clength - 1) - length rs | a rs d. (a,rs,d) \<in> set spec} =
      ?deg ` set spec"
    by force
  have aux: "foldl (\<lambda>x s. max x (?deg s)) n spec = Max (insert n (?deg ` set spec))"
    for n
  proof (induction spec arbitrary: n)
    case Nil
    then show ?case by simp
  next
    case (Cons s spec)
    then show ?case
      by (simp add: Max_insert_max)
  qed
  from aux[of 0] show ?thesis
    unfolding maxDegree_def using deg_set by (simp add: degrees_def split_beta')
qed

lemma maxDegree_less_eval_domain:
  "maxDegree < clength * scale"
proof -
  have finite_degrees: "finite (degrees clength spec)"
  proof -
    have "{d * (clength - 1) - length roots | c roots d. (c, roots, d) \<in> set spec} =
      (\<lambda>(c, roots, d). d * (clength - 1) - length roots) ` set spec"
      by force
    then show ?thesis
      unfolding degrees_def by simp
  qed
  have nonempty_degrees: "degrees clength spec \<noteq> {}"
    unfolding degrees_def by simp
  have all_lt: "\<And>x. x \<in> degrees clength spec \<Longrightarrow> x < clength * scale"
    unfolding degrees_def
    using eval_domain_size_pos spec_degree_fits
    by force
  then show ?thesis
    unfolding maxDegree_def
    using finite_degrees nonempty_degrees
    by (simp add: Max_less_iff)
qed

lemma g_map_distinct:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
  shows "distinct (g_map roots)"
proof -
  have roots_distinct: "distinct roots"
    by (rule spec_roots_distinct[OF spec_entry])
  have roots_in_range: "\<And>r. r \<in> set roots \<Longrightarrow> r < clength"
    by (rule spec_roots_in_range[OF spec_entry])
  have inj: "inj_on ((^) g) (set roots)"
    using roots_in_range by (auto intro!: inj_onI dest!: g_power_inj_on_range)
  show ?thesis
    unfolding g_map_def
    using roots_distinct inj by (simp add: distinct_map)
qed

lemma g_powers_in_H:
  assumes r_bound: "r < clength"
  shows "g ^ r \<in> set H"
proof -
  have idx_bound: "scale * r < scale * clength"
    using r_bound scale_pos by simp
  have "g ^ r = h ^ (scale * r)"
    using domain_alignment by (simp add: power_mult)
  then show ?thesis
    unfolding H_def using idx_bound by simp
qed

lemma g_map_subset_H:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
  shows "set (g_map roots) \<subseteq> set H"
  unfolding g_map_def
  using spec_roots_in_range[OF spec_entry] g_powers_in_H
  by auto

lemma query_domain_disjoint:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
    and idx_bound: "i < clength * scale"
  shows "h ^ i * shift \<notin> set (g_map roots)"
  using eval_coset_disjoint_from_H[OF idx_bound] g_map_subset_H[OF spec_entry]
  by auto

subsubsection \<open>Composition polynomial\<close>

text \<open>
  The composition polynomial is a random linear combination of the constraint polynomials divided by their roots.
  Note that in reality we don't compute the product polynomial as here.
  Instead we use a trick to optimize the computation
  (described here under Succinctness: https://medium.com/starkware/arithmetization-ii-403c3b3f4355)
  Also note that it needs to be parametrized by f since the prover uses it with the real f
  whereas the verifier uses another f.
  Maybe we need different versions for prover and verifier later on.
\<close>

definition cp
where
  "cp as fs \<equiv> fold (\<lambda>(a, (p,rs,_)). (+) ((CP a) * ((p fs) div (prod (g_map rs))))) (zip as spec) 0"

end

subsection \<open>Prover\<close>

text \<open>
  Only the prover knows the actual execution trace.
\<close>

locale prover = stark +
constrains omega::"'f::proth_field"
    and shift::"'f"
    and concat :: "'f \<Rightarrow> 'f \<Rightarrow> 'f"
    and spec :: "(('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat) list"
  fixes vals::"'f list" \<comment> \<open>This is the actual computation trace\<close>

assumes trace_length: "clength = length vals"

(*  assumes "(scale * (Suc (length vals))) dvd (size - 1)"  \<comment> \<open>This is required to guarantee the existence of H\<close>*)
begin

subsubsection \<open>Trace Polynomial\<close>

text \<open>
  The interpolated polynomial from the trace over G.
  We do it using Lagrange interpolation.
  In practice it is usually done using IFFT (inverse FTT -- Fast Fourier) but could not find it in the AFP.
\<close>

definition f
where
  "f \<equiv> lagrange_interpolation_poly (zip G vals)"

text \<open>
  Now we evaluate the trace polynomial on the larger domain, creating a Reed-Solomon error correction code.
\<close>

definition f_eval
where
  "f_eval \<equiv> map (poly f) eval_domain"

text \<open>
  Similar as the trace polynomial we evaluate the composition polynomial on the larger domain.
\<close>

definition f_powers
where
  "f_powers \<equiv> map (\<lambda>p. f \<circ>\<^sub>p XP (g^p)) [0 ..< powers]"


definition cp_eval
where
  "cp_eval as \<equiv> map (poly (cp as f_powers)) eval_domain"

subsubsection \<open>FRI Commitments\<close>

definition next_fri_domain :: "'f list \<Rightarrow> 'f list"
where
  "next_fri_domain fd \<equiv> map (\<lambda>x. x * x) (take ((length fd) div (2::nat)) fd)"

(*
  The definition of the polynomial [a,b] is bx+a
*)
definition next_fri_polynomial :: "'f poly \<Rightarrow> 'f \<Rightarrow> 'f poly"
where
  "next_fri_polynomial p b \<equiv>
    let
      c = coeffs p;
      odd_coefficients = nths_pred c odd;
      even_coefficients = nths_pred c even;
      odd = CP b * poly_of_list odd_coefficients;
      even = poly_of_list even_coefficients
    in odd + even"

lemma degree_Poly_less:
  assumes "degree p > 0"
      and "length xs < length (coeffs p)"
    shows "degree (Poly xs) < degree p"
proof -
  from assms(2) have "length (strip_while (HOL.eq 0) xs) < length (coeffs p)"
    by (meson dual_order.strict_trans1 length_strip_while_le verit_comp_simplify1(3))
  then have "degree (Poly (strip_while (HOL.eq 0) xs)) < degree p"
    using length_coeffs[of "(Poly (nths_pred (coeffs p) even))"]
    by (metis Poly_coeffs add_less_cancel_right assms(1) coeffs_Poly degree_0 length_coeffs not_gr_zero)
  then show "degree (Poly xs) < degree p"
    by (metis Poly_coeffs coeffs_Poly)
qed

lemma degree_less_degree:
  assumes "degree p>0"
    and "next_fri_polynomial p b = p'"
  shows "degree p' < degree p"
proof -
  have *: "length (coeffs p) > 1" using assms length_coeffs
    by (simp add: degree_eq_length_coeffs)

  define odd_coefficients where "odd_coefficients \<equiv> nths_pred (coeffs p) odd"
  define oddp where "oddp \<equiv> CP b * Poly odd_coefficients"
  define even_coefficients where "even_coefficients \<equiv> nths_pred (coeffs p) even"
  define evenp where "evenp \<equiv> Poly even_coefficients"

  from * have "length odd_coefficients < length (coeffs p)"
    using nths_pred_odd_length_less odd_coefficients_def by simp
  then have "degree (Poly (odd_coefficients)) < degree p"
    using assms(1) degree_Poly_less by metis

  moreover have "degree (CP b) = 0" unfolding CP_def by (simp add: monom_0)
  ultimately have "degree oddp < degree p"
    unfolding oddp_def using degree_mult_le[of "CP b" "(Poly odd_coefficients)"] by simp

  moreover from * have "length even_coefficients < length (coeffs p)"
    using nths_pred_even_length_less even_coefficients_def by simp
  then have "degree (Poly (even_coefficients)) < degree p"
    using assms(1) degree_Poly_less by metis
  then have "degree evenp < degree p" unfolding evenp_def by satx

  moreover have "p' = oddp + evenp"
    using assms
    unfolding oddp_def evenp_def odd_coefficients_def even_coefficients_def next_fri_polynomial_def
    by (auto simp add:Let_def)
  ultimately show ?thesis by (simp add: degree_add_less)
qed

definition next_fri_layer:: "'f poly \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f poly \<times> 'f list \<times> 'f list"
where
  "next_fri_layer p d b \<equiv>
    let
      next_poly = next_fri_polynomial p b;
      next_domain = next_fri_domain d;
      next_layer = map (poly next_poly) next_domain
    in (next_poly, next_domain, next_layer)"

primrec fri_commit_with ::
    "('f, 'f, unit) protocol_c_monad
     \<Rightarrow> nat
     \<Rightarrow> 'f poly list
     \<Rightarrow> 'f list list
     \<Rightarrow> 'f list list
     \<Rightarrow> 'f tree list
     \<Rightarrow> ('f, 'f poly list \<times> 'f list list \<times> 'f list list \<times> 'f tree list, unit) protocol_c_monad"
where
  "fri_commit_with receive_challenge 0 ps ds ls ms =
    return (ps, ds, ls, ms)"
| "fri_commit_with receive_challenge (Suc n) ps ds ls ms =
    do {
      send (value (last ms));
      b \<leftarrow> receive_challenge;
      let (next_poly, next_domain, next_layer) =
        next_fri_layer (last ps) (last ds) b;
      m \<leftarrow> create next_layer;
      fri_commit_with receive_challenge n
        (ps @ [next_poly])
        (ds @ [next_domain])
        (ls @ [next_layer])
        (ms @ [m])
    }"

primrec fri_commit ::
    "nat
     \<Rightarrow> 'f poly list
     \<Rightarrow> 'f list list
     \<Rightarrow> 'f list list
     \<Rightarrow> 'f tree list
     \<Rightarrow> ('f, 'f poly list \<times> 'f list list \<times> 'f list list \<times> 'f tree list, unit) protocol_c_monad"
where
  "fri_commit 0 ps ds ls ms = return (ps, ds, ls, ms)"
| "fri_commit (Suc n) ps ds ls ms =
    do {
      send (value (last ms));
      b \<leftarrow> receive_random_field_element;
      let (next_poly, next_domain, next_layer) = next_fri_layer (last ps) (last ds) b;
      m \<leftarrow> create next_layer;
      fri_commit n
        (ps @ [next_poly])
        (ds @ [next_domain])
        (ls @ [next_layer])
        (ms @ [m])
    }"

definition trace_fri_commit
where
  "trace_fri_commit =
    fri_commit_with receive_trace_fri_challenge"

definition composition_fri_commit
where
  "composition_fri_commit =
    fri_commit_with receive_composition_fri_challenge"

lemma fri_commit_with_receive_random_field_element:
  "fri_commit_with receive_random_field_element n ps ds ls ms =
    fri_commit n ps ds ls ms"
  by (induction n arbitrary: ps ds ls ms) simp_all

lemma fri_commit_lengths:
  assumes "Some ((ps', ds', ls', ms'), t) \<in>
    set_dist (execute (fri_commit n ps ds ls ms) s)"
  shows
    "length ps' = length ps + n \<and>
     length ds' = length ds + n \<and>
     length ls' = length ls + n \<and>
     length ms' = length ms + n"
  using assms
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute receive_random_field_element s1)"
    and next_layer_eq: "next_fri_layer (last ps) (last ds) b = (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (create next_layer) s2)"
    and rest: "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute
        (fri_commit n
          (ps @ [next_poly])
          (ds @ [next_domain])
          (ls @ [next_layer])
          (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  show ?case
    using Suc.IH[OF rest] by simp
qed

lemma fri_commit_extends:
  assumes "Some ((ps', ds', ls', ms'), t) \<in>
    set_dist (execute (fri_commit n ps ds ls ms) s)"
  shows "s \<le> t"
  using assms
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case
    using hash_ext_refl by simp
next
  case (Suc n)
  from Suc.prems obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute receive_random_field_element s1)"
    and next_layer_eq: "next_fri_layer (last ps) (last ds) b = (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (create next_layer) s2)"
    and rest: "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute
        (fri_commit n
          (ps @ [next_poly])
          (ds @ [next_domain])
          (ls @ [next_layer])
          (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have s_s1: "s \<le> s1"
    using send_outcome[OF send_root]
    unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s1_s2: "s1 \<le> s2"
    using receive_random_field_element_extends[OF rand] .
  have s2_s3: "s2 \<le> s3"
    using create_outcome[OF create_m] by simp
  have s3_t: "s3 \<le> t"
    using Suc.IH[OF rest] .
  show ?case
    using s_s1 s1_s2 s2_s3 s3_t by (meson hash_ext_trans)
qed

lemma fri_commit_preserves_prefix:
  assumes outcome:
    "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute (fri_commit n ps ds ls ms) s)"
  shows
    "take (length ps) ps' = ps \<and>
     take (length ds) ds' = ds \<and>
     take (length ls) ls' = ls \<and>
     take (length ms) ms' = ms"
  using outcome
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute receive_random_field_element s1)"
    and next_layer_eq: "next_fri_layer (last ps) (last ds) b = (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (create next_layer) s2)"
    and rest: "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute
        (fri_commit n
          (ps @ [next_poly])
          (ds @ [next_domain])
          (ls @ [next_layer])
          (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have ih: "take (length (ps @ [next_poly])) ps' = ps @ [next_poly] \<and>
      take (length (ds @ [next_domain])) ds' = ds @ [next_domain] \<and>
      take (length (ls @ [next_layer])) ls' = ls @ [next_layer] \<and>
      take (length (ms @ [m])) ms' = ms @ [m]"
    using Suc.IH[OF rest] .
  have "take (length ps) ps' = ps"
  proof -
    have "take (length ps) ps' =
        take (length ps) (take (length (ps @ [next_poly])) ps')"
      by (simp add: take_take)
    also have "... = ps"
      using ih by simp
    finally show ?thesis .
  qed
  moreover have "take (length ds) ds' = ds"
  proof -
    have "take (length ds) ds' =
        take (length ds) (take (length (ds @ [next_domain])) ds')"
      by (simp add: take_take)
    also have "... = ds"
      using ih by simp
    finally show ?thesis .
  qed
  moreover have "take (length ls) ls' = ls"
  proof -
    have "take (length ls) ls' =
        take (length ls) (take (length (ls @ [next_layer])) ls')"
      by (simp add: take_take)
    also have "... = ls"
      using ih by simp
    finally show ?thesis .
  qed
  moreover have "take (length ms) ms' = ms"
  proof -
    have "take (length ms) ms' =
        take (length ms) (take (length (ms @ [m])) ms')"
      by (simp add: take_take)
    also have "... = ms"
      using ih by simp
    finally show ?thesis .
  qed
  ultimately show ?case
    by simp
qed

lemma fri_commit_layers_are_evaluations:
  assumes init:
    "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
      ls ! i = map (poly (ps ! i)) (ds ! i)"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute (fri_commit n ps ds ls ms) s)"
    and lens: "length ps = length ds" "length ds = length ls"
  shows
    "\<And>i. i < length ps' \<Longrightarrow> i < length ds' \<Longrightarrow> i < length ls' \<Longrightarrow>
      ls' ! i = map (poly (ps' ! i)) (ds' ! i)"
  using init outcome lens
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(5) obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute receive_random_field_element s1)"
    and next_layer_eq: "next_fri_layer (last ps) (last ds) b = (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (create next_layer) s2)"
    and rest: "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute
        (fri_commit n
          (ps @ [next_poly])
          (ds @ [next_domain])
          (ls @ [next_layer])
          (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have next_eval: "next_layer = map (poly next_poly) next_domain"
    using next_layer_eq unfolding next_fri_layer_def by (auto simp: Let_def split: prod.splits)
  have init':
    "\<And>i. i < length (ps @ [next_poly]) \<Longrightarrow>
      i < length (ds @ [next_domain]) \<Longrightarrow>
      i < length (ls @ [next_layer]) \<Longrightarrow>
      (ls @ [next_layer]) ! i =
        map (poly ((ps @ [next_poly]) ! i)) ((ds @ [next_domain]) ! i)"
  proof -
    fix i
    assume i_ps: "i < length (ps @ [next_poly])"
      and i_ds: "i < length (ds @ [next_domain])"
      and i_ls: "i < length (ls @ [next_layer])"
    show "(ls @ [next_layer]) ! i =
        map (poly ((ps @ [next_poly]) ! i)) ((ds @ [next_domain]) ! i)"
    proof (cases "i < length ps")
      case True
      then show ?thesis
        using Suc.prems(4)[of i] Suc.prems(6,7)
        by (simp add: nth_append)
    next
      case False
      then have i_eq: "i = length ps"
        using i_ps by simp
      then show ?thesis
        using Suc.prems(6,7) next_eval by (simp add: nth_append)
    qed
  qed
  show ?case
    using Suc.IH[OF _ _ _ init' rest] Suc.prems(1-3,6,7) by simp
qed

lemma fri_commit_created_trees:
  assumes init:
    "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
      created_tree (ls ! i) (ms ! i) (s::'f protocol_channel)"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute (fri_commit n ps ds ls ms) s)"
    and lens: "length ls = length ms"
  shows "\<And>i. i < length ls' \<Longrightarrow> i < length ms' \<Longrightarrow>
    created_tree (ls' ! i) (ms' ! i) t"
  using init outcome lens
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(4) obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute receive_random_field_element s1)"
    and next_layer_eq: "next_fri_layer (last ps) (last ds) b = (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (create next_layer) s2)"
    and rest: "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute
        (fri_commit n
          (ps @ [next_poly])
          (ds @ [next_domain])
          (ls @ [next_layer])
          (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have s_s1: "s \<le> s1"
    using send_outcome[OF send_root]
    unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s1_s2: "s1 \<le> s2"
    using receive_random_field_element_extends[OF rand] .
  have s2_s3: "s2 \<le> s3"
    using create_outcome[OF create_m] by simp
  have s_s3: "s \<le> s3"
    using s_s1 s1_s2 s2_s3 by (meson hash_ext_trans)
  have created_m: "created_tree next_layer m s3"
    using create_outcome[OF create_m] by simp
  have init':
    "\<And>i. i < length (ls @ [next_layer]) \<Longrightarrow>
      i < length (ms @ [m]) \<Longrightarrow>
      created_tree ((ls @ [next_layer]) ! i) ((ms @ [m]) ! i) s3"
  proof -
    fix i
    assume i_ls: "i < length (ls @ [next_layer])"
      and i_ms: "i < length (ms @ [m])"
    show "created_tree ((ls @ [next_layer]) ! i) ((ms @ [m]) ! i) s3"
    proof (cases "i < length ls")
	      case True
	      then have "created_tree (ls ! i) (ms ! i) s"
	        using Suc.prems(3)[of i] Suc.prems(5) by simp
	      then show ?thesis
	        using True Suc.prems(5) s_s3
	        by (simp add: nth_append created_tree_mono)
    next
      case False
      then have "i = length ls"
        using i_ls by simp
	      then show ?thesis
	        using Suc.prems(5) created_m by (simp add: nth_append)
    qed
  qed
	  show ?case
	    using Suc.IH[OF Suc.prems(1,2) init' rest] Suc.prems(5) by simp
qed

lemma fri_commit_with_lengths:
  assumes "Some ((ps', ds', ls', ms'), t) \<in>
    set_dist (execute (fri_commit_with receive_challenge n ps ds ls ms) s)"
  shows
    "length ps' = length ps + n \<and>
     length ds' = length ds + n \<and>
     length ls' = length ls + n \<and>
     length ms' = length ms + n"
  using assms
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute receive_challenge s1)"
    and next_layer_eq:
      "next_fri_layer (last ps) (last ds) b =
        (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (create next_layer) s2)"
    and rest: "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute
        (fri_commit_with receive_challenge n
          (ps @ [next_poly])
          (ds @ [next_domain])
          (ls @ [next_layer])
          (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  show ?case
    using Suc.IH[OF rest] by simp
qed

lemma fri_commit_with_extends:
  assumes receiver_extends:
      "\<And>b s t. Some (b, t) \<in> set_dist (execute receive_challenge s) \<Longrightarrow>
        s \<le> t"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute (fri_commit_with receive_challenge n ps ds ls ms) s)"
  shows "s \<le> t"
  using outcome
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case
    using hash_ext_refl by simp
next
  case (Suc n)
  from Suc.prems obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute receive_challenge s1)"
    and next_layer_eq:
      "next_fri_layer (last ps) (last ds) b =
        (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (create next_layer) s2)"
    and rest: "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute
        (fri_commit_with receive_challenge n
          (ps @ [next_poly])
          (ds @ [next_domain])
          (ls @ [next_layer])
          (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have s_s1: "s \<le> s1"
    using send_outcome[OF send_root]
    unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s1_s2: "s1 \<le> s2"
    using receiver_extends[OF rand] .
  have s2_s3: "s2 \<le> s3"
    using create_outcome[OF create_m] by simp
  have s3_t: "s3 \<le> t"
    using Suc.IH[OF rest] .
  show ?case
    using s_s1 s1_s2 s2_s3 s3_t by (meson hash_ext_trans)
qed

lemma fri_commit_with_preserves_prefix:
  assumes outcome:
    "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute (fri_commit_with receive_challenge n ps ds ls ms) s)"
  shows
    "take (length ps) ps' = ps \<and>
     take (length ds) ds' = ds \<and>
     take (length ls) ls' = ls \<and>
     take (length ms) ms' = ms"
  using outcome
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute receive_challenge s1)"
    and next_layer_eq:
      "next_fri_layer (last ps) (last ds) b =
        (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (create next_layer) s2)"
    and rest: "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute
        (fri_commit_with receive_challenge n
          (ps @ [next_poly])
          (ds @ [next_domain])
          (ls @ [next_layer])
          (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have ih: "take (length (ps @ [next_poly])) ps' = ps @ [next_poly] \<and>
      take (length (ds @ [next_domain])) ds' = ds @ [next_domain] \<and>
      take (length (ls @ [next_layer])) ls' = ls @ [next_layer] \<and>
      take (length (ms @ [m])) ms' = ms @ [m]"
    using Suc.IH[OF rest] .
  have "take (length ps) ps' = ps"
  proof -
    have "take (length ps) ps' =
        take (length ps) (take (length (ps @ [next_poly])) ps')"
      by (simp add: take_take)
    also have "... = ps"
      using ih by simp
    finally show ?thesis .
  qed
  moreover have "take (length ds) ds' = ds"
  proof -
    have "take (length ds) ds' =
        take (length ds) (take (length (ds @ [next_domain])) ds')"
      by (simp add: take_take)
    also have "... = ds"
      using ih by simp
    finally show ?thesis .
  qed
  moreover have "take (length ls) ls' = ls"
  proof -
    have "take (length ls) ls' =
        take (length ls) (take (length (ls @ [next_layer])) ls')"
      by (simp add: take_take)
    also have "... = ls"
      using ih by simp
    finally show ?thesis .
  qed
  moreover have "take (length ms) ms' = ms"
  proof -
    have "take (length ms) ms' =
        take (length ms) (take (length (ms @ [m])) ms')"
      by (simp add: take_take)
    also have "... = ms"
      using ih by simp
    finally show ?thesis .
  qed
  ultimately show ?case
    by simp
qed

lemma fri_commit_with_layers_are_evaluations:
  assumes init:
    "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
      ls ! i = map (poly (ps ! i)) (ds ! i)"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute (fri_commit_with receive_challenge n ps ds ls ms) s)"
    and lens: "length ps = length ds" "length ds = length ls"
  shows
    "\<And>i. i < length ps' \<Longrightarrow> i < length ds' \<Longrightarrow> i < length ls' \<Longrightarrow>
      ls' ! i = map (poly (ps' ! i)) (ds' ! i)"
  using init outcome lens
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(5) obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute receive_challenge s1)"
    and next_layer_eq:
      "next_fri_layer (last ps) (last ds) b =
        (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (create next_layer) s2)"
    and rest: "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute
        (fri_commit_with receive_challenge n
          (ps @ [next_poly])
          (ds @ [next_domain])
          (ls @ [next_layer])
          (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have next_eval: "next_layer = map (poly next_poly) next_domain"
    using next_layer_eq unfolding next_fri_layer_def
    by (auto simp: Let_def split: prod.splits)
  have init':
    "\<And>i. i < length (ps @ [next_poly]) \<Longrightarrow>
      i < length (ds @ [next_domain]) \<Longrightarrow>
      i < length (ls @ [next_layer]) \<Longrightarrow>
      (ls @ [next_layer]) ! i =
        map (poly ((ps @ [next_poly]) ! i)) ((ds @ [next_domain]) ! i)"
  proof -
    fix i
    assume i_ps: "i < length (ps @ [next_poly])"
      and i_ds: "i < length (ds @ [next_domain])"
      and i_ls: "i < length (ls @ [next_layer])"
    show "(ls @ [next_layer]) ! i =
        map (poly ((ps @ [next_poly]) ! i)) ((ds @ [next_domain]) ! i)"
    proof (cases "i < length ps")
      case True
      then show ?thesis
        using Suc.prems(4)[of i] Suc.prems(6,7)
        by (simp add: nth_append)
    next
      case False
      then have i_eq: "i = length ps"
        using i_ps by simp
      then show ?thesis
        using Suc.prems(6,7) next_eval by (simp add: nth_append)
    qed
  qed
  show ?case
    using Suc.IH[OF _ _ _ init' rest] Suc.prems(1-3,6,7) by simp
qed

lemma fri_commit_with_created_trees:
  assumes receiver_extends:
      "\<And>b s t. Some (b, t) \<in> set_dist (execute receive_challenge s) \<Longrightarrow>
        s \<le> t"
    and init:
      "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
        created_tree (ls ! i) (ms ! i) (s::'f protocol_channel)"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute (fri_commit_with receive_challenge n ps ds ls ms) s)"
    and lens: "length ls = length ms"
  shows "\<And>i. i < length ls' \<Longrightarrow> i < length ms' \<Longrightarrow>
    created_tree (ls' ! i) (ms' ! i) t"
  using init outcome lens
proof (induction n arbitrary: ps ds ls ms s ps' ds' ls' ms' t i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(4) obtain s1 b s2 next_poly next_domain next_layer m s3 where
    send_root: "Some ((), s1) \<in> set_dist (execute (send (value (last ms))) s)"
    and rand: "Some (b, s2) \<in> set_dist (execute receive_challenge s1)"
    and next_layer_eq:
      "next_fri_layer (last ps) (last ds) b =
        (next_poly, next_domain, next_layer)"
    and create_m: "Some (m, s3) \<in> set_dist (execute (create next_layer) s2)"
    and rest: "Some ((ps', ds', ls', ms'), t) \<in>
      set_dist (execute
        (fri_commit_with receive_challenge n
          (ps @ [next_poly])
          (ds @ [next_domain])
          (ls @ [next_layer])
          (ms @ [m])) s3)"
    by (auto simp: Let_def split: prod.splits elim!: set_dist_bindE)
  have s_s1: "s \<le> s1"
    using send_outcome[OF send_root]
    unfolding less_eq_hash_ext_def less_eq_fmap_def by simp
  have s1_s2: "s1 \<le> s2"
    using receiver_extends[OF rand] .
  have s2_s3: "s2 \<le> s3"
    using create_outcome[OF create_m] by simp
  have s_s3: "s \<le> s3"
    using s_s1 s1_s2 s2_s3 by (meson hash_ext_trans)
  have created_m: "created_tree next_layer m s3"
    using create_outcome[OF create_m] by simp
  have init':
    "\<And>i. i < length (ls @ [next_layer]) \<Longrightarrow>
      i < length (ms @ [m]) \<Longrightarrow>
      created_tree ((ls @ [next_layer]) ! i) ((ms @ [m]) ! i) s3"
  proof -
    fix i
    assume i_ls: "i < length (ls @ [next_layer])"
      and i_ms: "i < length (ms @ [m])"
    show "created_tree ((ls @ [next_layer]) ! i) ((ms @ [m]) ! i) s3"
    proof (cases "i < length ls")
      case True
      then have "created_tree (ls ! i) (ms ! i) s"
        using Suc.prems(3)[of i] Suc.prems(5) by simp
      then show ?thesis
        using True Suc.prems(5) s_s3
        by (simp add: nth_append created_tree_mono)
    next
      case False
      then have "i = length ls"
        using i_ls by simp
      then show ?thesis
        using Suc.prems(5) created_m by (simp add: nth_append)
    qed
  qed
  show ?case
    using Suc.IH[OF Suc.prems(1,2) init' rest] Suc.prems(5) by simp
qed

lemma trace_fri_commit_extends:
  assumes "Some ((ps', ds', ls', ms'), t) \<in>
    set_dist (execute (trace_fri_commit n ps ds ls ms) s)"
  shows "s \<le> t"
  unfolding trace_fri_commit_def
  by (rule fri_commit_with_extends
      [OF receive_trace_fri_challenge_extends assms[unfolded trace_fri_commit_def]])

lemma trace_fri_commit_lengths:
  assumes "Some ((ps', ds', ls', ms'), t) \<in>
    set_dist (execute (trace_fri_commit n ps ds ls ms) s)"
  shows
    "length ps' = length ps + n \<and>
     length ds' = length ds + n \<and>
     length ls' = length ls + n \<and>
     length ms' = length ms + n"
  by (rule fri_commit_with_lengths[OF assms[unfolded trace_fri_commit_def]])

lemma trace_fri_commit_preserves_prefix:
  assumes "Some ((ps', ds', ls', ms'), t) \<in>
    set_dist (execute (trace_fri_commit n ps ds ls ms) s)"
  shows
    "take (length ps) ps' = ps \<and>
     take (length ds) ds' = ds \<and>
     take (length ls) ls' = ls \<and>
     take (length ms) ms' = ms"
  by (rule fri_commit_with_preserves_prefix
      [OF assms[unfolded trace_fri_commit_def]])

lemma trace_fri_commit_layers_are_evaluations:
  assumes init:
    "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
      ls ! i = map (poly (ps ! i)) (ds ! i)"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute (trace_fri_commit n ps ds ls ms) s)"
    and lens: "length ps = length ds" "length ds = length ls"
  shows
    "\<And>i. i < length ps' \<Longrightarrow> i < length ds' \<Longrightarrow> i < length ls' \<Longrightarrow>
      ls' ! i = map (poly (ps' ! i)) (ds' ! i)"
  by (rule fri_commit_with_layers_are_evaluations
      [OF init outcome[unfolded trace_fri_commit_def] lens])

lemma trace_fri_commit_created_trees:
  assumes init:
    "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
      created_tree (ls ! i) (ms ! i) (s::'f protocol_channel)"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute (trace_fri_commit n ps ds ls ms) s)"
    and lens: "length ls = length ms"
  shows "\<And>i. i < length ls' \<Longrightarrow> i < length ms' \<Longrightarrow>
    created_tree (ls' ! i) (ms' ! i) t"
  by (rule fri_commit_with_created_trees
      [OF receive_trace_fri_challenge_extends init
        outcome[unfolded trace_fri_commit_def] lens])

lemma composition_fri_commit_extends:
  assumes "Some ((ps', ds', ls', ms'), t) \<in>
    set_dist (execute (composition_fri_commit n ps ds ls ms) s)"
  shows "s \<le> t"
  unfolding composition_fri_commit_def
  by (rule fri_commit_with_extends
      [OF receive_composition_fri_challenge_extends
        assms[unfolded composition_fri_commit_def]])

lemma composition_fri_commit_lengths:
  assumes "Some ((ps', ds', ls', ms'), t) \<in>
    set_dist (execute (composition_fri_commit n ps ds ls ms) s)"
  shows
    "length ps' = length ps + n \<and>
     length ds' = length ds + n \<and>
     length ls' = length ls + n \<and>
     length ms' = length ms + n"
  by (rule fri_commit_with_lengths
      [OF assms[unfolded composition_fri_commit_def]])

lemma composition_fri_commit_preserves_prefix:
  assumes "Some ((ps', ds', ls', ms'), t) \<in>
    set_dist (execute (composition_fri_commit n ps ds ls ms) s)"
  shows
    "take (length ps) ps' = ps \<and>
     take (length ds) ds' = ds \<and>
     take (length ls) ls' = ls \<and>
     take (length ms) ms' = ms"
  by (rule fri_commit_with_preserves_prefix
      [OF assms[unfolded composition_fri_commit_def]])

lemma composition_fri_commit_layers_are_evaluations:
  assumes init:
    "\<And>i. i < length ps \<Longrightarrow> i < length ds \<Longrightarrow> i < length ls \<Longrightarrow>
      ls ! i = map (poly (ps ! i)) (ds ! i)"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute (composition_fri_commit n ps ds ls ms) s)"
    and lens: "length ps = length ds" "length ds = length ls"
  shows
    "\<And>i. i < length ps' \<Longrightarrow> i < length ds' \<Longrightarrow> i < length ls' \<Longrightarrow>
      ls' ! i = map (poly (ps' ! i)) (ds' ! i)"
  by (rule fri_commit_with_layers_are_evaluations
      [OF init outcome[unfolded composition_fri_commit_def] lens])

lemma composition_fri_commit_created_trees:
  assumes init:
    "\<And>i. i < length ls \<Longrightarrow> i < length ms \<Longrightarrow>
      created_tree (ls ! i) (ms ! i) (s::'f protocol_channel)"
    and outcome:
      "Some ((ps', ds', ls', ms'), t) \<in>
        set_dist (execute (composition_fri_commit n ps ds ls ms) s)"
    and lens: "length ls = length ms"
  shows "\<And>i. i < length ls' \<Longrightarrow> i < length ms' \<Longrightarrow>
    created_tree (ls' ! i) (ms' ! i) t"
  by (rule fri_commit_with_created_trees
      [OF receive_composition_fri_challenge_extends init
        outcome[unfolded composition_fri_commit_def] lens])

subsubsection \<open>Decommitments\<close>

definition decommit_on_fri_layers
where
  "decommit_on_fri_layers fs =
    map
      (\<lambda>(l, m) idx. do {
        let len = length l;
        let idx' = idx mod len;
        let sidx = (idx' + (len div 2)) mod len;
        send (l ! idx');
        mfold2 send (get_authentication_path len idx' m);
        send (l ! sidx);
        mfold2 send (get_authentication_path len sidx m);
        return idx'
      }) fs"

definition decommit_on_query
where
  "decommit_on_query idx f_merkle \<equiv>
    map
      (\<lambda>i. do {
        send (f_eval ! i);
        mfold2 send (get_authentication_path (length (f_eval)) i f_merkle)
      })
      (powers_scaled idx)"

subsubsection \<open>Stark Proof\<close>

text \<open>
  The following is a STARK proof for vals.
\<close>

definition prover_monad
where
  "prover_monad \<equiv> (do {
    f_merkle \<leftarrow> create f_eval;
    send (value f_merkle); \<comment> \<open>Send the root of a Merkle tree which contains the evaluations over the larger domain.\<close>
    let f_nrounds = ceil_log clength;
    (f_ps, f_ds, f_ls, f_ms) \<leftarrow>
      trace_fri_commit f_nrounds [f] [eval_domain] [f_eval] [f_merkle];
    send (hd (last f_ls)); \<comment> \<open>Send the final constant for the trace FRI proof.\<close>
    as \<leftarrow> mmap (replicate (length spec) (
      do {
        a \<leftarrow> receive_alpha_challenge;
        send a;
        return a
      })); \<comment> \<open>Send the random factors (alphas) for the composition polynomial.\<close>
    let cp' = cp as f_powers;
    send (of_nat (degree cp')); \<comment> \<open>Send the degree of the composition polynomial.\<close>
    cp_merkle \<leftarrow> create (cp_eval as);
    let nrounds = ceil_log (degree cp' + 1);
    (ps, ds, ls, ms) \<leftarrow>
      composition_fri_commit nrounds [cp'] [eval_domain] [cp_eval as] [cp_merkle];
     \<comment>\<open>Again, we create a Merkle tree which contains the evaluations over the larger domain.\<close>
    send (hd (last ls)); \<comment> \<open>Send the final constant before the verifier samples the query index.\<close>
    ntimes (do {
      idx \<leftarrow> receive_query_index_challenge; \<comment> \<open>Check the validity for a random index. This should be repeated multiple times.\<close>
      let idx' = index (to_nat idx); \<comment> \<open>Make sure index is not out of bounds\<close>
      mmap (decommit_on_query idx' f_merkle);
      mfold idx' (decommit_on_fri_layers (butlast (zip f_ls f_ms))); \<comment> \<open>Check that the trace commitment is low-degree.\<close>
      mfold idx' (decommit_on_fri_layers (butlast (zip ls ms))); \<comment> \<open>We don't de-commit on the constant polynomial\<close>
      return ()
    }) rounds
  })"

definition sproof
where
  "sproof \<equiv>
    execute prover_monad
      \<lparr>HashMap = fmempty, PState = 0, PTranscript = [],
       PTraceFriCounter = 0, PCompositionFriCounter = 0,
       PAlphaCounter = 0, PQueryCounter = 0\<rparr>"

(*Note: We need to extract the transcript and reverse it*)

end

subsection \<open>Verifier\<close>

locale verifier = stark +
  constrains omega::"'f::proth_field"
      and shift::"'f"
      and concat :: "'f \<Rightarrow> 'f \<Rightarrow> 'f"
      and spec :: "(('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat) list"
    fixes spec2:: "(('f list \<Rightarrow> 'f) \<times> nat list) list"
  assumes specs_aligned:
    "list_all2
      (\<lambda>(c, roots, d) (c2, roots2).
        roots2 = roots \<and>
        (\<forall>qs x.
          powers \<le> length qs \<longrightarrow>
          c2 (map (\<lambda>q. poly q x) qs) = poly (c qs) x))
      spec spec2"

begin

lemma spec2_length:
  "length spec2 = length spec"
  using list_all2_lengthD[OF specs_aligned] by simp

lemma specs_agree:
  assumes pair:
      "((c, roots, d), (c2, roots2)) \<in> set (zip spec spec2)"
    and qs_len: "powers \<le> length qs"
  shows
    "roots2 = roots \<and>
      c2 (map (\<lambda>q. poly q x) qs) = poly (c qs) x"
proof -
  obtain i where i_bound: "i < length spec" "i < length spec2"
    and spec_i: "spec ! i = (c, roots, d)"
    and spec2_i: "spec2 ! i = (c2, roots2)"
    using pair by (auto simp: set_zip)
  have aligned:
    "(\<lambda>(c, roots, d) (c2, roots2).
        roots2 = roots \<and>
        (\<forall>qs x.
          powers \<le> length qs \<longrightarrow>
          c2 (map (\<lambda>q. poly q x) qs) = poly (c qs) x))
      (spec ! i) (spec2 ! i)"
    by (rule list_all2_nthD[OF specs_aligned i_bound(1)])
  show ?thesis
    using aligned spec_i spec2_i qs_len by simp
qed

definition cp_eval
where
  "cp_eval as fs x \<equiv> fold (\<lambda>(a, (p, rs)). (+) (a * ((p fs) div poly (prod (g_map rs)) x))) (zip as spec2) 0"

subsubsection \<open>Validate Committments\<close>

definition receive_fri_commits
where
  "receive_fri_commits =
    do {
      r \<leftarrow> read;
      b \<leftarrow> receive_random_field_element;
      return (b,r)
    }"

definition receive_fri_commits_with
where
  "receive_fri_commits_with receive_challenge =
    do {
      r \<leftarrow> read;
      b \<leftarrow> receive_challenge;
      return (b,r)
    }"

definition receive_trace_fri_commits
where
  "receive_trace_fri_commits =
    receive_fri_commits_with receive_trace_fri_challenge"

definition receive_composition_fri_commits
where
  "receive_composition_fri_commits =
    receive_fri_commits_with receive_composition_fri_challenge"

lemma receive_fri_commits_with_receive_random_field_element:
  "receive_fri_commits_with receive_random_field_element = receive_fri_commits"
  unfolding receive_fri_commits_with_def receive_fri_commits_def by simp

lemma receive_fri_commits_with_no_failure:
  assumes receiver_nf:
    "\<And>s. None \<notin> dom (dist (execute receive_challenge s))"
    and tr: "PTranscript s \<noteq> []"
  shows
    "None \<notin> dom (dist
      (execute (receive_fri_commits_with receive_challenge) s))"
  using tr
  unfolding receive_fri_commits_with_def
  by (intro no_failure_bindI)
    (simp_all add: read_no_failure receiver_nf)

lemma receive_trace_fri_commits_no_failure:
  assumes "PTranscript s \<noteq> []"
  shows "None \<notin> dom (dist (execute receive_trace_fri_commits s))"
  unfolding receive_trace_fri_commits_def
  by (rule receive_fri_commits_with_no_failure)
    (rule receive_trace_fri_challenge_no_failure, rule assms)

lemma receive_composition_fri_commits_no_failure:
  assumes "PTranscript s \<noteq> []"
  shows "None \<notin> dom (dist (execute receive_composition_fri_commits s))"
  unfolding receive_composition_fri_commits_def
  by (rule receive_fri_commits_with_no_failure)
    (rule receive_composition_fri_challenge_no_failure, rule assms)

subsubsection \<open>Validate Decommittments\<close>

definition validate
where
  "validate lgth idx leaf_data l rv \<equiv> check_authentication_path lgth idx leaf_data l = rv"

definition check_decommit_on_query
where
  "check_decommit_on_query fr idx \<equiv>
    map
      (\<lambda>i. do {
        qh \<leftarrow> read;
        let len = scale * clength; \<comment> \<open>\<^term>\<open>scale * clength\<close> is length of \<^term>\<open>f_eval\<close>\<close>
        qh_path \<leftarrow> ntimes read (floor_log len);
        ap \<leftarrow> check_authentication_path len i qh qh_path;
        assert (ap = fr);
        return qh
      })
      (powers_scaled idx)"

definition receive_query_commits
where
  "receive_query_commits fl =
    map (\<lambda>(b,f) (i,x,len,pow).
    do {
      xp \<leftarrow> read;
      xp' \<leftarrow> ntimes read (floor_log len);
      xn \<leftarrow> read;
      xn' \<leftarrow> ntimes read (floor_log len);
      assert (xp = x);
      ap \<leftarrow> check_authentication_path len i xp xp';
      assert (ap = f);
      let sidx = (i + len div 2) mod len;
      ap \<leftarrow> check_authentication_path len sidx xn xn';
      assert (ap = f);
      let gp = (xp + xn) div 2;
      let hp = (xp - xn) div (2*((h^i) * shift)^pow);
      let x = gp + b * hp;
      return (i mod (len div 2), x, len div 2,pow+pow)
    }) fl"

definition verify_monad
where
  "verify_monad \<equiv> (do {
    fr \<leftarrow> read;
    f_fl \<leftarrow> ntimes receive_trace_fri_commits (ceil_log clength);
    f_final \<leftarrow> read;
    as \<leftarrow> mmap (replicate (length spec) (
      do {
        a0 \<leftarrow> receive_alpha_challenge;
        let a0' = a0;
        a1 \<leftarrow> read;
        let a1' = a1;
        assert (a0' = a1');
        return a1'
      }));
    dg \<leftarrow> read;
    assert (to_nat dg \<le> maxDegree); \<comment> \<open>Degree check\<close>
    fl \<leftarrow> ntimes receive_composition_fri_commits (ceil_log (to_nat dg + 1));
    final \<leftarrow> read;
    ntimes (do {
      idx \<leftarrow> receive_query_index_challenge;
      let idx' = index (to_nat idx); \<comment> \<open>Make sure index is not out of bounds\<close>
      fv \<leftarrow> mmap (check_decommit_on_query fr idx');

      (f_i, f_x, f_len, f_pow) \<leftarrow> mfold (idx', hd fv, clength * scale, 1) (receive_query_commits f_fl);
      assert (f_x = f_final);

      (i,x,len,pow)  \<leftarrow> mfold (idx', cp_eval as fv (h^idx' * shift), clength * scale, 1) (receive_query_commits fl);

      assert (x = final) \<comment> \<open>Check that the final FRI value is the committed constant polynomial\<close>
    }) rounds
  })"

definition verify
where
  "verify p \<equiv> execute verify_monad (p\<lparr>PState := 0\<rparr>)"

end

end
