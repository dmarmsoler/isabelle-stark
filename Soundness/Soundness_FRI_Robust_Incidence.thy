theory Soundness_FRI_Robust_Incidence
  imports Soundness_FRI_Robust_RS_List
begin

section \<open>Finite hiding-incidence bounds\<close>

definition hiding_indices ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'b set) \<Rightarrow> 'b \<Rightarrow> 'i set"
where
  "hiding_indices I hidden b = {i \<in> I. b \<in> hidden i}"

lemma finite_hiding_indices:
  assumes "finite I"
  shows "finite (hiding_indices I hidden b)"
  using assms unfolding hiding_indices_def by simp

lemma sum_hiding_indices_card:
  assumes finite_I: "finite I"
    and finite_B: "finite B"
  shows
    "(\<Sum>b\<in>B. card (hiding_indices I hidden b)) =
      (\<Sum>i\<in>I. card (B \<inter> hidden i))"
proof -
  have
    "(\<Sum>b\<in>B. card (hiding_indices I hidden b)) =
      (\<Sum>b\<in>B. \<Sum>i\<in>I. if b \<in> hidden i then 1 else 0)"
    unfolding hiding_indices_def
    by (intro sum.cong refl card_filter_eq_sum_indicator finite_I)
  also have "... =
      (\<Sum>i\<in>I. \<Sum>b\<in>B. if b \<in> hidden i then 1 else 0)"
    by (rule sum.swap)
  also have "... = (\<Sum>i\<in>I. card (B \<inter> hidden i))"
  proof (intro sum.cong refl)
    fix i
    assume "i \<in> I"
    have "card (B \<inter> hidden i) =
        (\<Sum>b\<in>B. if b \<in> hidden i then 1 else 0)"
      using card_filter_eq_sum_indicator[OF finite_B,
          where P="\<lambda>b. b \<in> hidden i"]
      by (simp add: Int_def)
    then show
      "(\<Sum>b\<in>B. if b \<in> hidden i then 1 else 0) =
        card (B \<inter> hidden i)"
      by simp
  qed
  finally show ?thesis .
qed

lemma hiding_incidence_cross_mult:
  assumes finite_I: "finite I"
    and finite_B: "finite B"
    and finite_hidden: "\<And>i. i \<in> I \<Longrightarrow> finite (hidden i)"
    and hidden_card: "\<And>i. i \<in> I \<Longrightarrow> card (hidden i) \<le> 1"
    and per_challenge:
      "\<And>b. b \<in> B \<Longrightarrow> card I - t \<le> card (hiding_indices I hidden b)"
  shows "card B * (card I - t) \<le> card I"
proof -
  have lower:
      "card B * (card I - t) \<le>
        (\<Sum>b\<in>B. card (hiding_indices I hidden b))"
  proof -
    have
      "(\<Sum>b\<in>B. card I - t) \<le>
        (\<Sum>b\<in>B. card (hiding_indices I hidden b))"
      by (rule sum_mono) (rule per_challenge)
    then show ?thesis
      using finite_B by simp
  qed
  have exact:
      "(\<Sum>b\<in>B. card (hiding_indices I hidden b)) =
        (\<Sum>i\<in>I. card (B \<inter> hidden i))"
    by (rule sum_hiding_indices_card[OF finite_I finite_B])
  have upper:
      "(\<Sum>i\<in>I. card (B \<inter> hidden i)) \<le> (\<Sum>i\<in>I. 1)"
  proof (rule sum_mono)
    fix i
    assume i_mem: "i \<in> I"
    have finite_hidden_i: "finite (hidden i)"
      by (rule finite_hidden[OF i_mem])
    have "card (B \<inter> hidden i) \<le> card (hidden i)"
      by (rule card_mono[OF finite_hidden_i]) auto
    also have "... \<le> 1"
      by (rule hidden_card[OF i_mem])
    finally show "card (B \<inter> hidden i) \<le> 1" .
  qed
  have "card B * (card I - t) \<le>
      (\<Sum>b\<in>B. card (hiding_indices I hidden b))"
    by (rule lower)
  also have "... = (\<Sum>i\<in>I. card (B \<inter> hidden i))"
    by (rule exact)
  also have "... \<le> (\<Sum>i\<in>I. 1)"
    by (rule upper)
  also have "... = card I"
    using finite_I by simp
  finally show ?thesis .
qed

lemma hiding_incidence_card_div_bound:
  assumes finite_I: "finite I"
    and finite_B: "finite B"
    and finite_hidden: "\<And>i. i \<in> I \<Longrightarrow> finite (hidden i)"
    and hidden_card: "\<And>i. i \<in> I \<Longrightarrow> card (hidden i) \<le> 1"
    and per_challenge:
      "\<And>b. b \<in> B \<Longrightarrow> card I - t \<le> card (hiding_indices I hidden b)"
    and radius: "t < card I"
  shows "card B \<le> card I div (card I - t)"
proof (rule less_eq_div_iff_mult_less_eq[THEN iffD2])
  show "0 < card I - t"
    using radius by simp
  show "card B * (card I - t) \<le> card I"
    by (rule hiding_incidence_cross_mult[
          OF finite_I finite_B finite_hidden hidden_card per_challenge])
qed

lemma hiding_incidence_quotient_le:
  fixes M t :: nat
  assumes radius: "t < M"
  shows "M div (M - t) \<le> Suc t"
proof -
  have denominator_pos: "0 < M - t"
    using radius by simp
  have M_split: "M = (M - t) + t"
    using radius by linarith
  have "M div (M - t) = ((M - t) + t) div (M - t)"
    by (rule arg_cong[OF M_split])
  also have "... = t div (M - t) + 1"
    by (rule div_add_self1) (use denominator_pos in simp)
  also have "... \<le> t + 1"
    by simp
  also have "... = Suc t"
    by simp
  finally show ?thesis .
qed

lemma hiding_incidence_card_le_Suc:
  assumes finite_I: "finite I"
    and finite_B: "finite B"
    and finite_hidden: "\<And>i. i \<in> I \<Longrightarrow> finite (hidden i)"
    and hidden_card: "\<And>i. i \<in> I \<Longrightarrow> card (hidden i) \<le> 1"
    and per_challenge:
      "\<And>b. b \<in> B \<Longrightarrow> card I - t \<le> card (hiding_indices I hidden b)"
    and radius: "t < card I"
  shows "card B \<le> Suc t"
proof -
  have exact:
      "card B \<le> card I div (card I - t)"
    by (rule hiding_incidence_card_div_bound[
          OF finite_I finite_B finite_hidden hidden_card per_challenge radius])
  have quotient:
      "card I div (card I - t) \<le> Suc t"
    by (rule hiding_incidence_quotient_le[OF radius])
  show ?thesis
    using exact quotient by linarith
qed

lemma finite_fibers_card_bound:
  assumes finite_G: "finite G"
    and finite_C: "finite C"
    and anchor: "anchor \<in> G"
    and image: "candidate ` (G - {anchor}) \<subseteq> C"
    and fiber:
      "\<And>p. p \<in> C \<Longrightarrow>
        card {b \<in> G - {anchor}. candidate b = p} \<le> K"
  shows "card G \<le> 1 + card C * K"
proof -
  let ?G' = "G - {anchor}"
  let ?fiber = "\<lambda>p. {b \<in> ?G'. candidate b = p}"
  have finite_G': "finite ?G'"
    by (rule finite_Diff[OF finite_G])
  have fiber_cover: "?G' = (\<Union>p\<in>C. ?fiber p)"
  proof (rule equalityI)
    show "?G' \<subseteq> (\<Union>p\<in>C. ?fiber p)"
      using image by auto
    show "(\<Union>p\<in>C. ?fiber p) \<subseteq> ?G'"
      by auto
  qed
  have raw_union_bound:
      "card (\<Union>p\<in>C. ?fiber p) \<le> (\<Sum>p\<in>C. card (?fiber p))"
    by (rule card_UN_le[OF finite_C])
  have fiber_card:
      "card ?G' = card (\<Union>p\<in>C. ?fiber p)"
    by (rule arg_cong[OF fiber_cover])
  have union_bound:
      "card ?G' \<le> (\<Sum>p\<in>C. card (?fiber p))"
    using fiber_card raw_union_bound by simp
  have sum_bound:
      "(\<Sum>p\<in>C. card (?fiber p)) \<le> (\<Sum>p\<in>C. K)"
    by (rule sum_mono) (rule fiber)
  have G'_bound: "card ?G' \<le> card C * K"
  proof -
    have "card ?G' \<le> (\<Sum>p\<in>C. card (?fiber p))"
      by (rule union_bound)
    also have "... \<le> (\<Sum>p\<in>C. K)"
      by (rule sum_bound)
    also have "... = card C * K"
      using finite_C by simp
    finally show ?thesis .
  qed
  have diff_card: "card ?G' = card G - 1"
    by (rule card_Diff_singleton[OF anchor])
  have nonempty_G: "G \<noteq> {}"
    using anchor by blast
  have card_pos: "0 < card G"
    using finite_G nonempty_G by (simp add: card_gt_0_iff)
  have card_split: "card G = Suc (card ?G')"
    unfolding diff_card using card_pos by linarith
  show ?thesis
    unfolding card_split using G'_bound by simp
qed

end
