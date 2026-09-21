theory Soundness_FRI_Robust_Code_Distance
  imports Stark.Soundness_FRI_Conditioned_Multiround
begin

section \<open>Finite agreement counting\<close>

definition code_agreement_indices ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'i set"
where
  "code_agreement_indices I received word =
    {i \<in> I. received i = word i}"

definition code_agreement_multiplicity ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'a) set \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'i \<Rightarrow> nat"
where
  "code_agreement_multiplicity I C received i =
    card {word \<in> C. received i = word i}"

lemma finite_code_agreement_indices:
  assumes "finite I"
  shows "finite (code_agreement_indices I received word)"
  using assms unfolding code_agreement_indices_def by simp

lemma code_agreement_multiplicity_le:
  assumes "finite C"
  shows "code_agreement_multiplicity I C received i \<le> card C"
  unfolding code_agreement_multiplicity_def
  by (rule card_mono[OF assms]) auto

lemma card_filter_eq_sum_indicator:
  assumes "finite A"
  shows "card {x \<in> A. P x} = (\<Sum>x\<in>A. if P x then 1 else 0)"
proof -
  have "card {x \<in> A. P x} = (\<Sum>x\<in>{x \<in> A. P x}. 1)"
    by (rule card_eq_sum)
  also have "... = (\<Sum>x\<in>A. if P x then 1 else 0)"
    by (rule sum.mono_neutral_cong_left[OF assms]) auto
  finally show ?thesis .
qed

lemma sum_code_agreement_multiplicity:
  assumes "finite I" "finite C"
  shows
    "(\<Sum>i\<in>I. code_agreement_multiplicity I C received i) =
      (\<Sum>word\<in>C. card (code_agreement_indices I received word))"
proof -
  have
    "(\<Sum>i\<in>I. code_agreement_multiplicity I C received i) =
      (\<Sum>i\<in>I. \<Sum>word\<in>C. if received i = word i then 1 else 0)"
    unfolding code_agreement_multiplicity_def
    by (intro sum.cong refl card_filter_eq_sum_indicator assms)
  also have "... =
      (\<Sum>word\<in>C. \<Sum>i\<in>I. if received i = word i then 1 else 0)"
    by (rule sum.swap)
  also have "... =
      (\<Sum>word\<in>C. card (code_agreement_indices I received word))"
    unfolding code_agreement_indices_def
    by (intro sum.cong refl sym[OF card_filter_eq_sum_indicator] assms)
  finally show ?thesis .
qed

lemma finite_sum_squared_le_card_sum_squares:
  fixes f :: "'i \<Rightarrow> real"
  assumes "finite I"
  shows "(\<Sum>i\<in>I. f i)^2 \<le> real (card I) * (\<Sum>i\<in>I. (f i)^2)"
  using assms
proof (induction I rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x I)
  let ?S = "\<Sum>i\<in>I. f i"
  let ?Q = "\<Sum>i\<in>I. (f i)^2"
  have nonneg:
      "0 \<le> (\<Sum>i\<in>I. (f i - f x)^2)"
    by (rule sum_nonneg) simp
  have identity:
      "(\<Sum>i\<in>I. (f i - f x)^2) =
        ?Q - 2 * f x * ?S + real (card I) * (f x)^2"
    using insert.hyps
    by (simp add: power2_diff sum_subtractf sum.distrib
        flip: sum_distrib_left sum_distrib_right)
  have ih: "?S^2 \<le> real (card I) * ?Q"
    by (rule insert.IH)
  have old_nonneg: "0 \<le> real (card I) * ?Q - ?S^2"
    using ih by linarith
  have diff_identity:
      "real (card (insert x I)) *
          (\<Sum>i\<in>insert x I. (f i)^2) -
        (\<Sum>i\<in>insert x I. f i)^2 =
      (real (card I) * ?Q - ?S^2) +
        (\<Sum>i\<in>I. (f i - f x)^2)"
    using insert.hyps identity
    by (simp add: power2_sum power2_eq_square algebra_simps)
  show ?case
    using old_nonneg nonneg diff_identity by linarith
qed

lemma finite_sum_squared_le_card_sum_squares_nat:
  fixes f :: "'i \<Rightarrow> nat"
  assumes "finite I"
  shows "(\<Sum>i\<in>I. f i)^2 \<le> card I * (\<Sum>i\<in>I. (f i)^2)"
proof -
  have real_bound:
      "(\<Sum>i\<in>I. real (f i))^2 \<le>
        real (card I) * (\<Sum>i\<in>I. (real (f i))^2)"
    by (rule finite_sum_squared_le_card_sum_squares[OF assms])
  have casted:
      "real ((\<Sum>i\<in>I. f i)^2) \<le>
        real (card I * (\<Sum>i\<in>I. (f i)^2))"
    using assms real_bound by simp
  show ?thesis
    by (rule of_nat_le_iff[where 'a=real, THEN iffD1, OF casted])
qed

lemma robust_list_size_from_square_sum:
  assumes finite_I: "finite I"
    and finite_C: "finite C"
    and agreements:
      "\<And>word. word \<in> C \<Longrightarrow>
        a \<le> card (code_agreement_indices I received word)"
    and square_upper:
      "(\<Sum>i\<in>I. (code_agreement_multiplicity I C received i)^2) \<le>
        card C * card I + card C * (card C - 1) * k"
  shows
    "card C * a^2 \<le>
      card I * (card I + (card C - 1) * k)"
proof (cases "C = {}")
  case True
  then show ?thesis by simp
next
  case False
  let ?L = "card C"
  let ?n = "card I"
  let ?m = "code_agreement_multiplicity I C received"
  let ?S = "\<Sum>i\<in>I. ?m i"
  have L_pos: "0 < ?L"
    using finite_C False by (simp add: card_gt_0_iff)
  have total_lower: "?L * a \<le> ?S"
  proof -
    have "?L * a = (\<Sum>word\<in>C. a)"
      using finite_C by simp
    also have "... \<le>
        (\<Sum>word\<in>C. card (code_agreement_indices I received word))"
      by (rule sum_mono) (use agreements in auto)
    also have "... = ?S"
      by (rule sym[OF sum_code_agreement_multiplicity[OF finite_I finite_C]])
    finally show ?thesis .
  qed
  have lower_square: "(?L * a)^2 \<le> ?S^2"
    using total_lower by (rule power_mono) simp
  have cauchy:
      "?S^2 \<le> ?n * (\<Sum>i\<in>I. (?m i)^2)"
    by (rule finite_sum_squared_le_card_sum_squares_nat[OF finite_I])
  have upper:
      "?n * (\<Sum>i\<in>I. (?m i)^2) \<le>
        ?n * (?L * ?n + ?L * (?L - 1) * k)"
    using square_upper by simp
  have chain:
      "(?L * a)^2 \<le> ?n * (?L * ?n + ?L * (?L - 1) * k)"
    using lower_square cauchy upper by linarith
  have factored:
      "?L * (?L * a^2) \<le>
        ?L * (?n * (?n + (?L - 1) * k))"
    using chain by (simp add: power2_eq_square algebra_simps)
  show ?thesis
    using factored L_pos by simp
qed

definition simultaneous_agreement_indices ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'i set"
where
  "simultaneous_agreement_indices I received word other =
    {i \<in> I. received i = word i \<and> received i = other i}"

definition code_pair_agreement_indices ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'i set"
where
  "code_pair_agreement_indices I word other =
    {i \<in> I. word i = other i}"

lemma finite_code_pair_agreement_indices:
  assumes "finite I"
  shows "finite (code_pair_agreement_indices I word other)"
  using assms unfolding code_pair_agreement_indices_def by simp

lemma finite_simultaneous_agreement_indices:
  assumes "finite I"
  shows "finite (simultaneous_agreement_indices I received word other)"
  using assms unfolding simultaneous_agreement_indices_def by simp

lemma simultaneous_agreement_indices_subset_pair:
  "simultaneous_agreement_indices I received word other \<subseteq>
    code_pair_agreement_indices I word other"
  unfolding simultaneous_agreement_indices_def
    code_pair_agreement_indices_def by auto

lemma code_agreement_multiplicity_square:
  assumes "finite C"
  shows
    "(code_agreement_multiplicity I C received i)^2 =
      (\<Sum>word\<in>C. \<Sum>other\<in>C.
        if received i = word i \<and> received i = other i then 1 else 0)"
proof -
  have multiplicity:
      "code_agreement_multiplicity I C received i =
        (\<Sum>word\<in>C. if received i = word i then 1 else 0)"
    unfolding code_agreement_multiplicity_def
    by (rule card_filter_eq_sum_indicator[OF assms])
  show ?thesis
    unfolding multiplicity power2_eq_square sum_product
    by (intro sum.cong refl) auto
qed

lemma sum_code_agreement_multiplicity_squares:
  assumes finite_I: "finite I" and finite_C: "finite C"
  shows
    "(\<Sum>i\<in>I. (code_agreement_multiplicity I C received i)^2) =
      (\<Sum>word\<in>C. \<Sum>other\<in>C.
        card (simultaneous_agreement_indices I received word other))"
proof -
  have
    "(\<Sum>i\<in>I. (code_agreement_multiplicity I C received i)^2) =
      (\<Sum>i\<in>I. \<Sum>word\<in>C. \<Sum>other\<in>C.
        if received i = word i \<and> received i = other i then 1 else 0)"
    by (intro sum.cong refl code_agreement_multiplicity_square finite_C)
  also have "... =
      (\<Sum>word\<in>C. \<Sum>i\<in>I. \<Sum>other\<in>C.
        if received i = word i \<and> received i = other i then 1 else 0)"
    by (rule sum.swap)
  also have "... =
      (\<Sum>word\<in>C. \<Sum>other\<in>C. \<Sum>i\<in>I.
        if received i = word i \<and> received i = other i then 1 else 0)"
    by (intro sum.cong refl sum.swap)
  also have "... =
      (\<Sum>word\<in>C. \<Sum>other\<in>C.
        card (simultaneous_agreement_indices I received word other))"
    unfolding simultaneous_agreement_indices_def
    by (intro sum.cong refl sym[OF card_filter_eq_sum_indicator] finite_I)
  finally show ?thesis .
qed

lemma simultaneous_agreement_indices_card_le_pair:
  assumes finite_I: "finite I"
    and pair_bound:
      "card (code_pair_agreement_indices I word other) \<le> k"
  shows
    "card (simultaneous_agreement_indices I received word other) \<le> k"
proof -
  have
    "card (simultaneous_agreement_indices I received word other) \<le>
      card (code_pair_agreement_indices I word other)"
    by (rule card_mono[
      OF finite_code_pair_agreement_indices[OF finite_I]
        simultaneous_agreement_indices_subset_pair])
  also have "... \<le> k"
    by (rule pair_bound)
  finally show ?thesis .
qed


lemma sum_simultaneous_agreements_le_pairwise_cap:
  assumes finite_I: "finite I"
    and finite_C: "finite C"
    and pairwise:
      "\<And>word other. word \<in> C \<Longrightarrow> other \<in> C \<Longrightarrow> word \<noteq> other \<Longrightarrow>
        card (code_pair_agreement_indices I word other) \<le> k"
  shows
    "(\<Sum>word\<in>C. \<Sum>other\<in>C.
        card (simultaneous_agreement_indices I received word other)) \<le>
      card C * card I + card C * (card C - 1) * k"
proof -
  let ?L = "card C"
  let ?n = "card I"
  have individual:
      "\<And>word other. word \<in> C \<Longrightarrow> other \<in> C \<Longrightarrow>
        card (simultaneous_agreement_indices I received word other) \<le>
          (if word = other then ?n else k)"
  proof -
    fix word other
    assume word_mem: "word \<in> C" and other_mem: "other \<in> C"
    show
      "card (simultaneous_agreement_indices I received word other) \<le>
        (if word = other then ?n else k)"
    proof (cases "word = other")
      case True
      have subset:
          "simultaneous_agreement_indices I received word other \<subseteq> I"
        unfolding simultaneous_agreement_indices_def by auto
      have bound:
          "card (simultaneous_agreement_indices I received word other) \<le> ?n"
        by (rule card_mono[OF finite_I subset])
      show ?thesis using True bound by simp
    next
      case False
      have bound:
          "card (simultaneous_agreement_indices I received word other) \<le> k"
        by (rule simultaneous_agreement_indices_card_le_pair[OF finite_I])
          (rule pairwise[OF word_mem other_mem False])
      show ?thesis using False bound by simp
    qed
  qed
  have inner_cap:
      "\<And>word. word \<in> C \<Longrightarrow>
        (\<Sum>other\<in>C. if word = other then ?n else k) =
          ?n + (?L - 1) * k"
  proof -
    fix word
    assume word_mem: "word \<in> C"
    have complement_set:
        "C \<inter> - {other. word = other} = C - {word}"
      by auto
    have complement_card:
        "card (C \<inter> - {other. word = other}) = ?L - 1"
      unfolding complement_set
      by (rule card_Diff_singleton[OF word_mem])
    have
      "(\<Sum>other\<in>C. if word = other then ?n else k) =
        (\<Sum>other\<in>C \<inter> {other. word = other}. ?n) +
        (\<Sum>other\<in>C \<inter> - {other. word = other}. k)"
      by (rule sum.If_cases[OF finite_C])
    also have "... = ?n + (?L - 1) * k"
      using finite_C word_mem complement_card by simp
    finally show
      "(\<Sum>other\<in>C. if word = other then ?n else k) =
        ?n + (?L - 1) * k" .
  qed
  have
    "(\<Sum>word\<in>C. \<Sum>other\<in>C.
        card (simultaneous_agreement_indices I received word other)) \<le>
      (\<Sum>word\<in>C. \<Sum>other\<in>C. if word = other then ?n else k)"
    by (intro sum_mono individual)
  also have "... = (\<Sum>word\<in>C. ?n + (?L - 1) * k)"
    by (intro sum.cong refl inner_cap)
  also have "... = ?L * ?n + ?L * (?L - 1) * k"
    using finite_C by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma robust_list_size_bound:
  assumes finite_I: "finite I"
    and finite_C: "finite C"
    and agreements:
      "\<And>word. word \<in> C \<Longrightarrow>
        a \<le> card (code_agreement_indices I received word)"
    and pairwise:
      "\<And>word other. word \<in> C \<Longrightarrow> other \<in> C \<Longrightarrow> word \<noteq> other \<Longrightarrow>
        card (code_pair_agreement_indices I word other) \<le> k"
  shows
    "card C * a^2 \<le>
      card I * (card I + (card C - 1) * k)"
proof (rule robust_list_size_from_square_sum[OF finite_I finite_C agreements])
  have exact:
      "(\<Sum>i\<in>I. (code_agreement_multiplicity I C received i)^2) =
        (\<Sum>word\<in>C. \<Sum>other\<in>C.
          card (simultaneous_agreement_indices I received word other))"
    by (rule sum_code_agreement_multiplicity_squares[OF finite_I finite_C])
  show
    "(\<Sum>i\<in>I. (code_agreement_multiplicity I C received i)^2) \<le>
      card C * card I + card C * (card C - 1) * k"
    unfolding exact
    by (rule sum_simultaneous_agreements_le_pairwise_cap[
      OF finite_I finite_C pairwise])
qed

lemma robust_list_size_cross_mult:
  fixes L a n d :: nat
  assumes bound:
      "L * a^2 \<le> n * (n + (L - 1) * d)"
    and d_le_n: "d \<le> n"
    and nd_le_a2: "n * d \<le> a^2"
  shows "L * (a^2 - n * d) \<le> n * (n - d)"
proof (cases L)
  case 0
  then show ?thesis by simp
next
  case (Suc l)
  have left_split:
      "L * (a^2 - n * d) + L * (n * d) = L * a^2"
    using nd_le_a2
    by (simp only: add_mult_distrib2[symmetric] le_add_diff_inverse2)
  have base_split:
      "n * (n - d) + n * d = n * n"
    using d_le_n
    by (simp only: add_mult_distrib2[symmetric] le_add_diff_inverse2)
  have rhs_split:
      "n * (n + (L - 1) * d) =
        n * (n - d) + L * (n * d)"
  proof -
    have
      "n * (n + (Suc l - 1) * d) =
        n * n + l * (n * d)"
      by (simp add: algebra_simps)
    also have "... =
        (n * (n - d) + n * d) + l * (n * d)"
      using base_split by simp
    also have "... =
        n * (n - d) + Suc l * (n * d)"
      by (simp add: add.assoc)
    finally have unfolded:
      "n * (n + (Suc l - 1) * d) =
        n * (n - d) + Suc l * (n * d)" .
    show ?thesis
      using unfolded Suc by simp
  qed
  have augmented:
      "L * (a^2 - n * d) + L * (n * d) \<le>
        n * (n - d) + L * (n * d)"
    unfolding left_split rhs_split[symmetric]
    by (rule bound)
  then show ?thesis by simp
qed


lemma robust_list_size_div_bound:
  fixes L a n d :: nat
  assumes bound:
      "L * a^2 \<le> n * (n + (L - 1) * d)"
    and d_le_n: "d \<le> n"
    and nd_lt_a2: "n * d < a^2"
  shows
    "L \<le> n * (n - d) div (a^2 - n * d)"
proof (rule less_eq_div_iff_mult_less_eq[THEN iffD2])
  show "0 < a^2 - n * d"
    using nd_lt_a2 by simp
  show "L * (a^2 - n * d) \<le> n * (n - d)"
    by (rule robust_list_size_cross_mult[OF bound d_le_n])
      (use nd_lt_a2 in simp)
qed

definition code_disagreement_indices ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'i set"
where
  "code_disagreement_indices I received word =
    {i \<in> I. received i \<noteq> word i}"

lemma finite_code_disagreement_indices:
  assumes "finite I"
  shows "finite (code_disagreement_indices I received word)"
  using assms unfolding code_disagreement_indices_def by simp

lemma code_agreement_disagreement_card:
  assumes finite_I: "finite I"
  shows
    "card (code_agreement_indices I received word) +
      card (code_disagreement_indices I received word) = card I"
proof -
  have complement:
      "code_disagreement_indices I received word =
        I - code_agreement_indices I received word"
    unfolding code_disagreement_indices_def code_agreement_indices_def
    by auto
  have agreement_subset:
      "code_agreement_indices I received word \<subseteq> I"
    unfolding code_agreement_indices_def by auto
  have agreement_le:
      "card (code_agreement_indices I received word) \<le> card I"
    by (rule card_mono[OF finite_I agreement_subset])
  have disagreement_card:
      "card (code_disagreement_indices I received word) =
        card I - card (code_agreement_indices I received word)"
    unfolding complement
    by (rule card_Diff_subset[
      OF finite_code_agreement_indices[OF finite_I] agreement_subset])
  show ?thesis
    unfolding disagreement_card
    by (rule le_add_diff_inverse[OF agreement_le])
qed

lemma code_close_imp_agreement:
  assumes finite_I: "finite I"
    and radius: "t \<le> card I"
    and close:
      "card (code_disagreement_indices I received word) \<le> t"
  shows
    "card I - t \<le> card (code_agreement_indices I received word)"
  using code_agreement_disagreement_card[OF finite_I,
      of received word] radius close
  by linarith

lemma code_agreement_imp_close:
  assumes finite_I: "finite I"
    and radius: "t \<le> card I"
    and agreement:
      "card I - t \<le> card (code_agreement_indices I received word)"
  shows
    "card (code_disagreement_indices I received word) \<le> t"
  using code_agreement_disagreement_card[OF finite_I,
      of received word] radius agreement
  by linarith

end
