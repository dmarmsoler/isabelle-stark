theory Soundness_FRI_Binary_Correlated_Agreement
  imports Soundness_FRI_Robust_One_Round
begin

section \<open>Binary mutual correlated agreement\<close>

text \<open>
  This is a derived binary, bounded-radius substitute for the mutual
  correlated-agreement hypothesis used by simple-rbr-fri. It is not the
  all-arity hypothesis or its full advertised proximity range. All component
  words, eligible agreement subsets and field challenges (including zero)
  are retained. No new public soundness premise is introduced.
\<close>

context soundness
begin

definition fri_binary_mca_bad_challenges ::
  "'f list \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'f) \<Rightarrow> (nat \<Rightarrow> 'f) \<Rightarrow> nat \<Rightarrow> 'f set"
where
  "fri_binary_mca_bad_challenges xs k a c t =
   {b. \<exists>S. S \<subseteq> {..<length xs} \<and> length xs \<le> card S + t \<and>
     (\<exists>q. degree q \<le> k \<and> (\<forall>i\<in>S. a i + b * c i = poly q (xs ! i))) \<and>
     \<not>(\<exists>p0 p1. degree p0 \<le> k \<and> degree p1 \<le> k \<and>
       (\<forall>i\<in>S. a i = poly p0 (xs ! i) \<and> c i = poly p1 (xs ! i)))}"

lemma fri_mca_affine_two_points:
  fixes a c a' c' b0 b1 :: "'f"
  assumes different: "b0 \<noteq> b1"
    and eq0: "a + b0 * c = a' + b0 * c'"
    and eq1: "a + b1 * c = a' + b1 * c'"
  shows "(a,c) = (a',c')"
proof -
  have d0: "a - a' = b0 * (c' - c)"
    using eq0 by (simp add: algebra_simps)
  have d1: "a - a' = b1 * (c' - c)"
    using eq1 by (simp add: algebra_simps)
  have scaled: "b0 * (c' - c) = b1 * (c' - c)"
    by (rule trans[OF sym[OF d0] d1])
  have prod: "(b0 - b1) * (c - c') = 0"
    using scaled by (simp add: algebra_simps)
  have ceq: "c = c'" using prod different by auto
  show ?thesis using eq0 ceq by simp
qed

lemma fri_mca_two_large_sets:
  assumes fin: "finite I" and S0: "S0 \<subseteq> I" and S1: "S1 \<subseteq> I"
    and large0: "card I \<le> card S0 + t"
    and large1: "card I \<le> card S1 + t"
    and sub: "E \<subseteq> I - S0 \<union> (I - S1)"
  shows "card E \<le> 2 * t"
proof -
  have f0: "finite S0" using fin S0 finite_subset by blast
  have f1: "finite S1" using fin S1 finite_subset by blast
  have c0: "card (I - S0) \<le> t"
    using large0 card_Diff_subset[OF f0 S0] by arith
  have c1: "card (I - S1) \<le> t"
    using large1 card_Diff_subset[OF f1 S1] by arith
  have "card E \<le> card (I - S0 \<union> (I - S1))"
    by (rule card_mono) (use fin sub in auto)
  also have "... \<le> card (I - S0) + card (I - S1)"
    by (rule card_Un_le)
  also have "... \<le> 2 * t" using c0 c1 by arith
  finally show ?thesis .
qed

lemma fri_mca_poly_eq_on_large:
  fixes xs :: "'f list"
  assumes distinct: "distinct xs" and sub: "S \<subseteq> {..<length xs}"
    and large: "k < card S"
    and dp: "degree p \<le> k" and dq: "degree q \<le> k"
    and agree: "\<And>i. i \<in> S \<Longrightarrow> poly p (xs ! i) = poly q (xs ! i)"
  shows "p = q"
proof (rule ccontr)
  assume ne: "p \<noteq> q"
  have subA: "S \<subseteq> fri_polynomial_agreement_indices p q xs"
    using sub agree unfolding fri_polynomial_agreement_indices_def by auto
  have "card S \<le> card (fri_polynomial_agreement_indices p q xs)"
    by (rule card_mono) (use subA in \<open>auto simp: fri_polynomial_agreement_indices_def\<close>)
  also have "... \<le> max (degree p) (degree q)"
    by (rule fri_polynomial_agreement_indices_card_bound[OF distinct ne])
  also have "... \<le> k" using dp dq by simp
  finally show False using large by arith
qed

lemma fri_mca_two_anchor_bad_bound:
  assumes distinct: "distinct xs" and radius: "3 * t + k < length xs"
    and b0bad: "b0 \<in> fri_binary_mca_bad_challenges xs k a c t"
    and b1bad: "b1 \<in> fri_binary_mca_bad_challenges xs k a c t"
    and different: "b0 \<noteq> b1"
  shows "card (fri_binary_mca_bad_challenges xs k a c t) \<le> 2 * t"
proof -
  let ?I = "{..<length xs}"
  obtain S0 q0 where S0: "S0 \<subseteq> ?I" and large0: "length xs \<le> card S0 + t"
    and dq0: "degree q0 \<le> k"
    and aq0: "\<And>i. i \<in> S0 \<Longrightarrow> a i + b0 * c i = poly q0 (xs ! i)"
    using b0bad unfolding fri_binary_mca_bad_challenges_def by blast
  obtain S1 q1 where S1: "S1 \<subseteq> ?I" and large1: "length xs \<le> card S1 + t"
    and dq1: "degree q1 \<le> k"
    and aq1: "\<And>i. i \<in> S1 \<Longrightarrow> a i + b1 * c i = poly q1 (xs ! i)"
    using b1bad unfolding fri_binary_mca_bad_challenges_def by blast
  let ?A = "fri_two_fold_even_part b0 b1 q0 q1"
  let ?C = "fri_two_fold_odd_part b0 b1 q0 q1"
  have dA: "degree ?A \<le> k"
    by (rule fri_two_fold_even_part_degree[OF dq0 dq1])
  have dC: "degree ?C \<le> k"
    by (rule fri_two_fold_odd_part_degree[OF dq0 dq1])
  let ?E = "{i \<in> ?I. (a i,c i) \<noteq> (poly ?A (xs ! i),poly ?C (xs ! i))}"
  have Esub: "?E \<subseteq> ?I - S0 \<union> (?I - S1)"
  proof
    fix i assume ei: "i \<in> ?E"
    have ni: "i \<in> ?I" using ei by simp
    have "\<not>(i \<in> S0 \<and> i \<in> S1)"
    proof
      assume both: "i \<in> S0 \<and> i \<in> S1"
      have eq0: "a i + b0 * c i = poly ?A (xs ! i) + b0 * poly ?C (xs ! i)"
        using aq0[OF both[THEN conjunct1]] fri_two_fold_even_at_anchor by simp
      have eq1: "a i + b1 * c i = poly ?A (xs ! i) + b1 * poly ?C (xs ! i)"
        using aq1[OF both[THEN conjunct2]]
          fri_two_fold_at_other[of b1 b0 q0 q1 "xs ! i"] different by simp
      have "(a i,c i) = (poly ?A (xs ! i),poly ?C (xs ! i))"
        by (rule fri_mca_affine_two_points[OF different eq0 eq1])
      then show False using ei by simp
    qed
    then show "i \<in> ?I - S0 \<union> (?I - S1)" using ni by blast
  qed
  have ecard: "card ?E \<le> 2 * t"
    by (rule fri_mca_two_large_sets[OF _ S0 S1 _ _ Esub])
      (use large0 large1 in auto)
  let ?H = "\<lambda>i. {b. poly ?A (xs ! i) + b * poly ?C (xs ! i) = a i + b * c i}"
  have hcard: "\<And>i. i \<in> ?E \<Longrightarrow> card (?H i) \<le> 1"
    by (rule fri_affine_collision_challenges_card_le_one) auto
  have cover: "fri_binary_mca_bad_challenges xs k a c t \<subseteq> (\<Union>i\<in>?E. ?H i)"
  proof
    fix b assume bad: "b \<in> fri_binary_mca_bad_challenges xs k a c t"
    obtain S q where S: "S \<subseteq> ?I" and large: "length xs \<le> card S + t"
      and dq: "degree q \<le> k"
      and agree: "\<And>i. i \<in> S \<Longrightarrow> a i + b * c i = poly q (xs ! i)"
      and no_pair: "\<not>(\<exists>p0 p1. degree p0 \<le> k \<and> degree p1 \<le> k \<and>
        (\<forall>i\<in>S. a i = poly p0 (xs ! i) \<and> c i = poly p1 (xs ! i)))"
      using bad unfolding fri_binary_mca_bad_challenges_def by blast
    let ?Q = "?A + CP b * ?C"
    have dQ: "degree ?Q \<le> k"
    proof -
      have mul: "degree (CP b * ?C) \<le> k"
        using degree_mult_le[of "CP b" ?C] dC
        by (simp add: CP_def monom_0)
      show ?thesis using degree_add_le_max[of ?A "CP b * ?C"] dA mul by linarith
    qed
    have evalQ: "\<And>x. poly ?Q x = poly ?A x + b * poly ?C x"
      by (simp add: CP_def poly_monom)
    have finiteS: "finite S" using S finite_subset by blast
    have cardS: "card S \<le> card (S - ?E) + card ?E"
      using card_Un_le[of "S - ?E" "S \<inter> ?E"]
        card_mono[of ?E "S \<inter> ?E"]
      by (simp add: Un_Diff_Int)
    have large_diff: "k < card (S - ?E)"
      using cardS large ecard radius by arith
    have qeq: "q = ?Q"
    proof (rule fri_mca_poly_eq_on_large[OF distinct _ large_diff dq dQ])
      show "S - ?E \<subseteq> ?I" using S by blast
      fix i assume i: "i \<in> S - ?E"
      have pair: "a i = poly ?A (xs ! i) \<and> c i = poly ?C (xs ! i)"
        using i S by auto
      show "poly q (xs ! i) = poly ?Q (xs ! i)"
        using agree[of i] i pair by (simp add: CP_def poly_monom)
    qed
    obtain i where iS: "i \<in> S"
      and idiff: "a i \<noteq> poly ?A (xs ! i) \<or> c i \<noteq> poly ?C (xs ! i)"
      using no_pair dA dC by blast
    have iE: "i \<in> ?E" using iS S idiff by auto
    have bH: "b \<in> ?H i" using agree[OF iS] by (simp add: qeq CP_def poly_monom)
    show "b \<in> (\<Union>i\<in>?E. ?H i)" using iE bH by blast
  qed
  have "card (fri_binary_mca_bad_challenges xs k a c t) \<le> card (\<Union>i\<in>?E. ?H i)"
    by (rule card_mono) (use cover in auto)
  also have "... \<le> (\<Sum>i\<in>?E. card (?H i))" by (rule card_UN_le) simp
  also have "... \<le> (\<Sum>i\<in>?E. 1)" by (rule sum_mono) (rule hcard)
  also have "... = card ?E" by simp
  also have "... \<le> 2 * t" by (rule ecard)
  finally show ?thesis .
qed

lemma fri_binary_mca_bad_challenges_card:
  assumes distinct: "distinct xs" and radius: "3 * t + k < length xs"
  shows "card (fri_binary_mca_bad_challenges xs k a c t) \<le> max 1 (2 * t)"
proof (cases "\<exists>b0\<in>fri_binary_mca_bad_challenges xs k a c t.
    \<exists>b1\<in>fri_binary_mca_bad_challenges xs k a c t. b0 \<noteq> b1")
  case True
  then obtain b0 b1 where
    "b0 \<in> fri_binary_mca_bad_challenges xs k a c t"
    "b1 \<in> fri_binary_mca_bad_challenges xs k a c t" "b0 \<noteq> b1" by blast
  then have "card (fri_binary_mca_bad_challenges xs k a c t) \<le> 2 * t"
    by (rule fri_mca_two_anchor_bad_bound[OF distinct radius])
  then show ?thesis by simp
next
  case False
  have "card (fri_binary_mca_bad_challenges xs k a c t) \<le> 1"
    using False by (simp add: card_le_Suc0_iff_eq)
  then show ?thesis by simp
qed

lemma fri_mca_sparse_zero_is_mca_bad:
  assumes distinct: "distinct xs" and room: "k + 1 < length xs"
  shows "(0 :: 'f) \<in> fri_binary_mca_bad_challenges xs k (\<lambda>_. 0) (\<lambda>i. if i = 0 then 1 else 0) t"
proof -
  let ?I = "{..<length xs}"
  have pos: "0 < length xs" using room by arith
  have no_pair: "\<not>(\<exists>p0 p1 :: 'f poly. degree p0 \<le> k \<and> degree p1 \<le> k \<and>
     (\<forall>i\<in>?I. 0 = poly p0 (xs ! i) \<and> (if i = 0 then 1 else 0) = poly p1 (xs ! i)))"
  proof
    assume pair: "\<exists>p0 p1 :: 'f poly. degree p0 \<le> k \<and> degree p1 \<le> k \<and>
     (\<forall>i\<in>?I. 0 = poly p0 (xs ! i) \<and> (if i = 0 then 1 else 0) = poly p1 (xs ! i))"
    then obtain p1 :: "'f poly" where dp: "degree p1 \<le> k"
      and agree: "\<And>i. i < length xs \<Longrightarrow> (if i = 0 then 1 else 0) = poly p1 (xs ! i)"
      by auto
    have zero: "p1 = 0"
    proof (rule fri_mca_poly_eq_on_large[OF distinct _ _ dp])
      show "?I - {0} \<subseteq> ?I" by blast
      show "k < card (?I - {0})" using room pos by simp
      show "degree (0 :: 'f poly) \<le> k" by simp
      fix i assume "i \<in> ?I - {0}"
      then show "poly p1 (xs ! i) = poly 0 (xs ! i)" using agree[of i] by simp
    qed
    show False using agree[OF pos] zero by simp
  qed
  show ?thesis unfolding fri_binary_mca_bad_challenges_def
  proof (intro CollectI exI[where x="?I"] conjI)
    show "?I \<subseteq> ?I" by simp
    show "length xs \<le> card ?I + t" by simp
    show "\<exists>q :: 'f poly. degree q \<le> k \<and> (\<forall>i\<in>?I. 0 + 0 * (if i = 0 then 1 else 0) = poly q (xs ! i))"
      by (rule exI[where x=0]) simp
    show "\<not>(\<exists>p0 p1 :: 'f poly. degree p0 \<le> k \<and> degree p1 \<le> k \<and>
      (\<forall>i\<in>?I. 0 = poly p0 (xs ! i) \<and> (if i = 0 then 1 else 0) = poly p1 (xs ! i)))"
      by (rule no_pair)
  qed
qed

lemma fri_mca_binary_component_failure_iff:
  "((\<forall>p0 :: 'f poly. degree p0 \<le> k \<longrightarrow> (\<exists>i\<in>S. a i \<noteq> poly p0 (xs ! i))) \<or>
    (\<forall>p1 :: 'f poly. degree p1 \<le> k \<longrightarrow> (\<exists>i\<in>S. c i \<noteq> poly p1 (xs ! i)))) \<longleftrightarrow>
    \<not>(\<exists>p0 p1 :: 'f poly. degree p0 \<le> k \<and> degree p1 \<le> k \<and>
       (\<forall>i\<in>S. a i = poly p0 (xs ! i) \<and> c i = poly p1 (xs ! i)))"
  by blast

end
end
