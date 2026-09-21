theory Soundness_FRI_Robust_RS_List
  imports Soundness_FRI_Robust_Code_Distance
begin

section \<open>Reed--Solomon evaluation functions\<close>

context soundness
begin

definition fri_rs_code_tables :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list set"
where
  "fri_rs_code_tables d fri_dom =
    {map (poly p) fri_dom | p. degree p \<le> d}"

definition fri_rs_code_functions ::
  "nat \<Rightarrow> 'f list \<Rightarrow> (nat \<Rightarrow> 'f) set"
where
  "fri_rs_code_functions d fri_dom =
    (\<lambda>table. nth table) ` fri_rs_code_tables d fri_dom"

lemma fri_rs_code_tables_length:
  assumes "table \<in> fri_rs_code_tables d fri_dom"
  shows "length table = length fri_dom"
  using assms unfolding fri_rs_code_tables_def by auto

lemma finite_fri_rs_code_tables:
  "finite (fri_rs_code_tables d fri_dom)"
proof -
  have subset:
      "fri_rs_code_tables d fri_dom \<subseteq>
        {table :: 'f list. length table = length fri_dom}"
    using fri_rs_code_tables_length by blast
  have finite_length:
      "finite {table :: 'f list. length table = length fri_dom}"
    using finite_lists_length_eq[
      where A="UNIV :: 'f set" and n="length fri_dom"]
    by simp
  show ?thesis
    by (rule finite_subset[OF subset finite_length])
qed

lemma finite_fri_rs_code_functions:
  "finite (fri_rs_code_functions d fri_dom)"
  unfolding fri_rs_code_functions_def
  by (rule finite_imageI[OF finite_fri_rs_code_tables])

lemma fri_rs_code_tables_nonempty:
  "fri_rs_code_tables d fri_dom \<noteq> {}"
proof -
  have
    "map (poly (0 :: 'f poly)) fri_dom \<in>
      fri_rs_code_tables d fri_dom"
    unfolding fri_rs_code_tables_def setcompr_eq_image
    by (rule image_eqI[where x="0 :: 'f poly"]) simp_all
  then show ?thesis by blast
qed

lemma fri_rs_code_functions_nonempty:
  "fri_rs_code_functions d fri_dom \<noteq> {}"
  unfolding fri_rs_code_functions_def
  using fri_rs_code_tables_nonempty by blast

definition fri_rs_distance_to_code ::
  "nat \<Rightarrow> 'f list \<Rightarrow> (nat \<Rightarrow> 'f) \<Rightarrow> nat"
where
  "fri_rs_distance_to_code d fri_dom received =
    (LEAST n. \<exists>word \<in> fri_rs_code_functions d fri_dom.
      card (code_disagreement_indices
        {..<length fri_dom} received word) = n)"

lemma fri_rs_distance_to_code_attained:
  obtains word where
    "word \<in> fri_rs_code_functions d fri_dom"
    "card (code_disagreement_indices
      {..<length fri_dom} received word) =
        fri_rs_distance_to_code d fri_dom received"
proof -
  have ex:
      "\<exists>n. \<exists>word \<in> fri_rs_code_functions d fri_dom.
        card (code_disagreement_indices
          {..<length fri_dom} received word) = n"
    using fri_rs_code_functions_nonempty by blast
  have least:
      "\<exists>word \<in> fri_rs_code_functions d fri_dom.
        card (code_disagreement_indices
          {..<length fri_dom} received word) =
          (LEAST n. \<exists>word \<in> fri_rs_code_functions d fri_dom.
            card (code_disagreement_indices
              {..<length fri_dom} received word) = n)"
    by (rule LeastI_ex[OF ex])
  then obtain word where word:
      "word \<in> fri_rs_code_functions d fri_dom"
      "card (code_disagreement_indices
        {..<length fri_dom} received word) =
        (LEAST n. \<exists>word \<in> fri_rs_code_functions d fri_dom.
          card (code_disagreement_indices
            {..<length fri_dom} received word) = n)"
    by blast
  show ?thesis
    by (rule that[OF word(1)])
      (use word(2) in
        \<open>simp add: fri_rs_distance_to_code_def\<close>)
qed

lemma fri_rs_distance_to_code_le:
  assumes word: "word \<in> fri_rs_code_functions d fri_dom"
  shows
    "fri_rs_distance_to_code d fri_dom received \<le>
      card (code_disagreement_indices
        {..<length fri_dom} received word)"
  unfolding fri_rs_distance_to_code_def
  by (rule Least_le) (use word in blast)

definition fri_rs_canonical_decoder ::
  "nat \<Rightarrow> 'f list \<Rightarrow> (nat \<Rightarrow> 'f) \<Rightarrow> (nat \<Rightarrow> 'f)"
where
  "fri_rs_canonical_decoder d fri_dom received =
    (SOME word. word \<in> fri_rs_code_functions d fri_dom \<and>
      card (code_disagreement_indices
        {..<length fri_dom} received word) =
        fri_rs_distance_to_code d fri_dom received)"

lemma fri_rs_canonical_decoder_spec:
  "fri_rs_canonical_decoder d fri_dom received \<in>
      fri_rs_code_functions d fri_dom \<and>
    card (code_disagreement_indices {..<length fri_dom} received
      (fri_rs_canonical_decoder d fri_dom received)) =
      fri_rs_distance_to_code d fri_dom received"
proof -
  obtain word where word:
      "word \<in> fri_rs_code_functions d fri_dom"
      "card (code_disagreement_indices
        {..<length fri_dom} received word) =
        fri_rs_distance_to_code d fri_dom received"
    by (rule fri_rs_distance_to_code_attained)
  show ?thesis
    unfolding fri_rs_canonical_decoder_def
    by (rule someI2[where a=word]) (use word in auto)
qed

lemma fri_rs_canonical_decoder_code:
  "fri_rs_canonical_decoder d fri_dom received \<in>
    fri_rs_code_functions d fri_dom"
  using fri_rs_canonical_decoder_spec by blast

lemma fri_rs_canonical_decoder_distance:
  "card (code_disagreement_indices {..<length fri_dom} received
      (fri_rs_canonical_decoder d fri_dom received)) =
    fri_rs_distance_to_code d fri_dom received"
  using fri_rs_canonical_decoder_spec by blast


lemma fri_rs_code_functions_pair_agreement_bound:
  assumes distinct_dom: "distinct fri_dom"
    and word_mem: "word \<in> fri_rs_code_functions d fri_dom"
    and other_mem: "other \<in> fri_rs_code_functions d fri_dom"
    and different: "word \<noteq> other"
  shows
    "card (code_pair_agreement_indices
      {..<length fri_dom} word other) \<le> d"
proof -
  obtain p where p_degree: "degree p \<le> d"
    and word_eq: "word = nth (map (poly p) fri_dom)"
    using word_mem unfolding fri_rs_code_functions_def
      fri_rs_code_tables_def by auto
  obtain q where q_degree: "degree q \<le> d"
    and other_eq: "other = nth (map (poly q) fri_dom)"
    using other_mem unfolding fri_rs_code_functions_def
      fri_rs_code_tables_def by auto
  have polynomials_different: "p \<noteq> q"
  proof
    assume "p = q"
    then have "word = other"
      using word_eq other_eq by simp
    then show False using different by contradiction
  qed
  have sets_equal:
      "code_pair_agreement_indices {..<length fri_dom} word other =
        fri_polynomial_agreement_indices p q fri_dom"
    unfolding code_pair_agreement_indices_def
      fri_polynomial_agreement_indices_def word_eq other_eq
    by auto
  have
    "card (code_pair_agreement_indices
      {..<length fri_dom} word other) \<le> max (degree p) (degree q)"
    unfolding sets_equal
    by (rule fri_polynomial_agreement_indices_card_bound[
      OF distinct_dom polynomials_different])
  also have "... \<le> d"
    using p_degree q_degree by simp
  finally show ?thesis .
qed

definition fri_rs_agreement_list ::
  "nat \<Rightarrow> 'f list \<Rightarrow> (nat \<Rightarrow> 'f) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'f) set"
where
  "fri_rs_agreement_list d fri_dom received a =
    {word \<in> fri_rs_code_functions d fri_dom.
      a \<le> card (code_agreement_indices
        {..<length fri_dom} received word)}"

lemma finite_fri_rs_agreement_list:
  "finite (fri_rs_agreement_list d fri_dom received a)"
  unfolding fri_rs_agreement_list_def
  by (rule finite_subset[OF _ finite_fri_rs_code_functions]) auto

lemma fri_rs_agreement_list_card_bound:
  assumes distinct_dom: "distinct fri_dom"
  shows
    "card (fri_rs_agreement_list d fri_dom received a) * a^2 \<le>
      length fri_dom *
        (length fri_dom +
          (card (fri_rs_agreement_list d fri_dom received a) - 1) * d)"
proof -
  have generic:
    "card (fri_rs_agreement_list d fri_dom received a) * a^2 \<le>
      card {..<length fri_dom} *
        (card {..<length fri_dom} +
          (card (fri_rs_agreement_list d fri_dom received a) - 1) * d)"
  proof (rule robust_list_size_bound)
    show "finite {..<length fri_dom}"
      by simp
    show "finite (fri_rs_agreement_list d fri_dom received a)"
      by (rule finite_fri_rs_agreement_list)
    show
      "\<And>word. word \<in> fri_rs_agreement_list d fri_dom received a \<Longrightarrow>
        a \<le> card (code_agreement_indices
          {..<length fri_dom} received word)"
      unfolding fri_rs_agreement_list_def by simp
    show
      "\<And>word other.
        word \<in> fri_rs_agreement_list d fri_dom received a \<Longrightarrow>
        other \<in> fri_rs_agreement_list d fri_dom received a \<Longrightarrow>
        word \<noteq> other \<Longrightarrow>
        card (code_pair_agreement_indices
          {..<length fri_dom} word other) \<le> d"
      unfolding fri_rs_agreement_list_def
      by (rule fri_rs_code_functions_pair_agreement_bound[OF distinct_dom])
        simp_all
  qed
  show ?thesis
    using generic by simp
qed

definition fri_rs_close_list ::
  "nat \<Rightarrow> 'f list \<Rightarrow> (nat \<Rightarrow> 'f) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'f) set"
where
  "fri_rs_close_list d fri_dom received t =
    {word \<in> fri_rs_code_functions d fri_dom.
      card (code_disagreement_indices
        {..<length fri_dom} received word) \<le> t}"

lemma finite_fri_rs_close_list:
  "finite (fri_rs_close_list d fri_dom received t)"
  unfolding fri_rs_close_list_def
  by (rule finite_subset[OF _ finite_fri_rs_code_functions]) auto

lemma fri_rs_close_list_eq_agreement_list:
  assumes radius: "t \<le> length fri_dom"
  shows
    "fri_rs_close_list d fri_dom received t =
      fri_rs_agreement_list d fri_dom received (length fri_dom - t)"
proof (rule equalityI)
  show
    "fri_rs_close_list d fri_dom received t \<subseteq>
      fri_rs_agreement_list d fri_dom received (length fri_dom - t)"
  proof
    fix word
    assume close_mem:
      "word \<in> fri_rs_close_list d fri_dom received t"
    then have word_code: "word \<in> fri_rs_code_functions d fri_dom"
      and close:
        "card (code_disagreement_indices
          {..<length fri_dom} received word) \<le> t"
      unfolding fri_rs_close_list_def by simp_all
    have raw_agreement:
        "card {..<length fri_dom} - t \<le>
          card (code_agreement_indices
            {..<length fri_dom} received word)"
      by (rule code_close_imp_agreement[
          where I="{..<length fri_dom}" and t=t])
        (use radius close in simp_all)
    have agreement:
        "length fri_dom - t \<le>
          card (code_agreement_indices
            {..<length fri_dom} received word)"
      using raw_agreement by simp
    show
      "word \<in> fri_rs_agreement_list d fri_dom received
        (length fri_dom - t)"
      using word_code agreement
      unfolding fri_rs_agreement_list_def by simp
  qed
  show
    "fri_rs_agreement_list d fri_dom received (length fri_dom - t) \<subseteq>
      fri_rs_close_list d fri_dom received t"
  proof
    fix word
    assume agreement_mem:
      "word \<in> fri_rs_agreement_list d fri_dom received
        (length fri_dom - t)"
    then have word_code: "word \<in> fri_rs_code_functions d fri_dom"
      and agreement:
        "length fri_dom - t \<le>
          card (code_agreement_indices
            {..<length fri_dom} received word)"
      unfolding fri_rs_agreement_list_def by simp_all
    have raw_agreement:
        "card {..<length fri_dom} - t \<le>
          card (code_agreement_indices
            {..<length fri_dom} received word)"
      using agreement by simp
    have close:
        "card (code_disagreement_indices
          {..<length fri_dom} received word) \<le> t"
      by (rule code_agreement_imp_close[
          where I="{..<length fri_dom}" and t=t])
        (use radius raw_agreement in simp_all)
    show "word \<in> fri_rs_close_list d fri_dom received t"
      using word_code close unfolding fri_rs_close_list_def by simp
  qed
qed

lemma fri_rs_close_list_card_bound:
  assumes distinct_dom: "distinct fri_dom"
    and radius: "t \<le> length fri_dom"
  shows
    "card (fri_rs_close_list d fri_dom received t) *
        (length fri_dom - t)^2 \<le>
      length fri_dom *
        (length fri_dom +
          (card (fri_rs_close_list d fri_dom received t) - 1) * d)"
  unfolding fri_rs_close_list_eq_agreement_list[OF radius]
  by (rule fri_rs_agreement_list_card_bound[OF distinct_dom])

lemma fri_rs_close_list_card_div_bound:
  assumes distinct_dom: "distinct fri_dom"
    and radius: "t \<le> length fri_dom"
    and degree: "d \<le> length fri_dom"
    and johnson:
      "length fri_dom * d < (length fri_dom - t)^2"
  shows
    "card (fri_rs_close_list d fri_dom received t) \<le>
      length fri_dom * (length fri_dom - d) div
        ((length fri_dom - t)^2 - length fri_dom * d)"
proof (rule robust_list_size_div_bound)
  show
    "card (fri_rs_close_list d fri_dom received t) *
        (length fri_dom - t)^2 \<le>
      length fri_dom *
        (length fri_dom +
          (card (fri_rs_close_list d fri_dom received t) - 1) * d)"
    by (rule fri_rs_close_list_card_bound[OF distinct_dom radius])
  show "d \<le> length fri_dom"
    by (rule degree)
  show "length fri_dom * d < (length fri_dom - t)^2"
    by (rule johnson)
qed


lemma quarter_radius_johnson_arithmetic:
  fixes m d :: nat
  assumes m_pos: "0 < m"
    and d_le: "d \<le> m"
  shows "(4 * m) * d < (4 * m - m)^2"
proof -
  have md_le: "m * d \<le> m * m"
    by (rule mult_left_mono[OF d_le]) simp
  have mm_pos: "0 < m * m"
    using m_pos by simp
  have four_le: "4 * (m * d) \<le> 4 * (m * m)"
    using md_le by simp
  have nine_gt: "4 * (m * m) < 9 * (m * m)"
    using mm_pos by linarith
  have "4 * (m * d) < 9 * (m * m)"
    using four_le nine_gt by linarith
  then show ?thesis
    by (simp add: power2_eq_square algebra_simps)
qed

lemma quarter_radius_div_arithmetic:
  fixes m d :: nat
  assumes m_pos: "0 < m"
    and d_le: "d \<le> m"
  shows
    "(4 * m) * (4 * m - d) div
      ((4 * m - m)^2 - (4 * m) * d) \<le> 2"
proof -
  let ?num = "(4 * m) * (4 * m - d)"
  let ?den = "(4 * m - m)^2 - (4 * m) * d"
  have johnson: "(4 * m) * d < (4 * m - m)^2"
    by (rule quarter_radius_johnson_arithmetic[OF m_pos d_le])
  have den_pos: "0 < ?den"
    using johnson by simp
  have md_le: "m * d \<le> m * m"
    by (rule mult_left_mono[OF d_le]) simp
  have mm_pos: "0 < m * m"
    using m_pos by simp
  have d_le_4m: "d \<le> 4 * m"
    using d_le m_pos by linarith
  have four_md_le_nine_mm:
      "4 * (m * d) \<le> 9 * (m * m)"
    using md_le by (simp add: mult_le_mono)
  have cast_num:
      "int ?num =
        16 * int (m * m) - 4 * int (m * d)"
    using d_le_4m
    by (simp add: power2_eq_square algebra_simps)
  have cast_den:
      "int ?den =
        9 * int (m * m) - 4 * int (m * d)"
    using johnson
    by (simp add: power2_eq_square algebra_simps)
  have cast_md_le:
      "int (m * d) \<le> int (m * m)"
    by (rule of_nat_le_iff[where 'a=int, THEN iffD2])
      (rule md_le)
  have cast_mm_pos: "0 < int (m * m)"
    using mm_pos by simp
  have normalized:
      "16 * int (m * m) - 4 * int (m * d) <
        3 * (9 * int (m * m) - 4 * int (m * d))"
    using cast_md_le cast_mm_pos
    by (simp add: algebra_simps; linarith)
  have cast_num_lt: "int ?num < int (3 * ?den)"
  proof -
    have "int ?num =
        16 * int (m * m) - 4 * int (m * d)"
      by (rule cast_num)
    also have "... <
        3 * (9 * int (m * m) - 4 * int (m * d))"
      by (rule normalized)
    also have "... = int (3 * ?den)"
      using cast_den by simp
    finally show ?thesis .
  qed
  have num_lt: "?num < 3 * ?den"
    by (rule of_nat_less_iff[where 'a=int, THEN iffD1, OF cast_num_lt])
  have quotient_lt: "?num div ?den < 3"
    using div_less_iff_less_mult[OF den_pos, of ?num 3] num_lt
    by (simp add: mult.commute)
  then show ?thesis by linarith
qed

lemma fri_rs_quarter_radius_list_cap:
  fixes m d :: nat
  assumes distinct_dom: "distinct fri_dom"
    and length_eq: "length fri_dom = 4 * m"
    and m_pos: "0 < m"
    and degree: "d \<le> m"
  shows "card (fri_rs_close_list d fri_dom received m) \<le> 2"
proof -
  have radius: "m \<le> length fri_dom"
    using length_eq m_pos by linarith
  have degree_length: "d \<le> length fri_dom"
    using degree length_eq m_pos by linarith
  have johnson:
      "length fri_dom * d < (length fri_dom - m)^2"
    unfolding length_eq
    by (rule quarter_radius_johnson_arithmetic[OF m_pos degree])
  have exact:
      "card (fri_rs_close_list d fri_dom received m) \<le>
        length fri_dom * (length fri_dom - d) div
          ((length fri_dom - m)^2 - length fri_dom * d)"
    by (rule fri_rs_close_list_card_div_bound[
          OF distinct_dom radius degree_length johnson])
  have arithmetic:
      "length fri_dom * (length fri_dom - d) div
          ((length fri_dom - m)^2 - length fri_dom * d) \<le> 2"
    unfolding length_eq
    by (rule quarter_radius_div_arithmetic[OF m_pos degree])
  show ?thesis
    using exact arithmetic by linarith
qed

lemma scaled_div_rate_mono:
  fixes c D n q :: nat
  assumes rate: "c * D \<le> n"
    and q_pos: "0 < q"
  shows "c * (D div q) \<le> n div q"
proof (rule less_eq_div_iff_mult_less_eq[OF q_pos, THEN iffD2])
  have "c * (D div q) * q = c * ((D div q) * q)"
    by (simp add: algebra_simps)
  also have "... \<le> c * D"
    by (simp add: mult_le_mono)
  also have "... \<le> n"
    by (rule rate)
  finally show "c * (D div q) * q \<le> n" .
qed

lemma fri_degree_after_rate_preserved:
  assumes rate: "c * d \<le> clength * scale"
  shows
    "c * fri_degree_after i d \<le>
      length (fri_canonical_domain_at i)"
  unfolding fri_degree_after_closed_form fri_canonical_domain_at_length
  by (rule scaled_div_rate_mono[OF rate]) simp

lemma power_length_quarter:
  fixes i N :: nat
  assumes "i + 2 \<le> N"
  shows "(2::nat) ^ (N - i) = 4 * 2 ^ (N - i - 2)"
proof -
  have exponent_split: "N - i = 2 + (N - i - 2)"
    using assms by linarith
  have "(2::nat) ^ (N - i) = 2 ^ (2 + (N - i - 2))"
    by (rule arg_cong[OF exponent_split])
  also have "... = 2 ^ 2 * 2 ^ (N - i - 2)"
    by (rule power_add)
  also have "... = 4 * 2 ^ (N - i - 2)"
    by simp
  finally show ?thesis .
qed


lemma fri_rs_canonical_quarter_radius_list_cap:
  fixes d i N :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and two_rounds: "i + 2 \<le> N"
    and initial_rate: "4 * d \<le> clength * scale"
  shows
    "card (fri_rs_close_list
        (fri_degree_after i d)
        (fri_canonical_domain_at i)
        received
        (length (fri_canonical_domain_at i) div 4)) \<le> 2"
proof -
  let ?m = "(2::nat) ^ (N - i - 2)"
  have i_le: "i \<le> N"
    using two_rounds by linarith
  have domain_power:
      "length (fri_canonical_domain_at i) = 2 ^ (N - i)"
    by (rule fri_canonical_domain_at_length_power[OF eval_power i_le])
  have domain_length:
      "length (fri_canonical_domain_at i) = 4 * ?m"
    unfolding domain_power
    by (rule power_length_quarter[OF two_rounds])
  have m_pos: "0 < ?m"
    by simp
  have layer_rate:
      "4 * fri_degree_after i d \<le>
        length (fri_canonical_domain_at i)"
    by (rule fri_degree_after_rate_preserved[OF initial_rate])
  have layer_degree:
      "fri_degree_after i d \<le> ?m"
    using layer_rate unfolding domain_length by simp
  have distinct_domain: "distinct (fri_canonical_domain_at i)"
    by (rule distinct_fri_canonical_domain_at[OF eval_power i_le])
  have cap:
      "card (fri_rs_close_list
          (fri_degree_after i d)
          (fri_canonical_domain_at i)
          received ?m) \<le> 2"
    by (rule fri_rs_quarter_radius_list_cap[
          OF distinct_domain domain_length m_pos layer_degree])
  have radius_eq:
      "length (fri_canonical_domain_at i) div 4 = ?m"
    unfolding domain_length by simp
  show ?thesis
    unfolding radius_eq by (rule cap)
qed

lemma fri_rs_active_layer_quarter_radius_list_cap:
  fixes d i N :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and active_round: "i < ceil_log (Suc d)"
    and rounds_fit: "Suc (ceil_log (Suc d)) \<le> N"
    and initial_rate:
      "4 * fri_padded_degree_bound d \<le> clength * scale"
  shows
    "card (fri_rs_close_list
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        received
        (length (fri_canonical_domain_at i) div 4)) \<le> 2"
proof -
  have two_rounds: "i + 2 \<le> N"
    using active_round rounds_fit by linarith
  show ?thesis
    by (rule fri_rs_canonical_quarter_radius_list_cap[
          OF eval_power two_rounds initial_rate])
qed

lemma fri_rs_close_list_mono:
  assumes radius_mono: "t \<le> u"
  shows
    "fri_rs_close_list d fri_dom received t \<subseteq>
      fri_rs_close_list d fri_dom received u"
  using radius_mono unfolding fri_rs_close_list_def by auto

lemma fri_rs_close_list_card_mono:
  assumes radius_mono: "t \<le> u"
  shows
    "card (fri_rs_close_list d fri_dom received t) \<le>
      card (fri_rs_close_list d fri_dom received u)"
  by (rule card_mono[OF finite_fri_rs_close_list])
    (rule fri_rs_close_list_mono[OF radius_mono])

lemma fri_rs_active_layer_small_radius_list_cap:
  fixes d i N t :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and active_round: "i < ceil_log (Suc d)"
    and rounds_fit: "Suc (ceil_log (Suc d)) \<le> N"
    and initial_rate:
      "4 * fri_padded_degree_bound d \<le> clength * scale"
    and radius:
      "t \<le> length (fri_canonical_domain_at i) div 4"
  shows
    "card (fri_rs_close_list
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        received t) \<le> 2"
proof -
  have card_mono:
      "card (fri_rs_close_list
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i)
          received t) \<le>
        card (fri_rs_close_list
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i)
          received
          (length (fri_canonical_domain_at i) div 4))"
    by (rule fri_rs_close_list_card_mono[OF radius])
  have quarter_cap:
      "card (fri_rs_close_list
          (fri_degree_after i (fri_padded_degree_bound d))
          (fri_canonical_domain_at i)
          received
          (length (fri_canonical_domain_at i) div 4)) \<le> 2"
    by (rule fri_rs_active_layer_quarter_radius_list_cap[
          OF eval_power active_round rounds_fit initial_rate])
  show ?thesis
    using card_mono quarter_cap by linarith
qed

lemma sixteenth_radius_le_quarter_radius:
  fixes n :: nat
  shows "n div 16 \<le> n div 4"
proof (rule less_eq_div_iff_mult_less_eq[
    OF zero_less_numeral, THEN iffD2])
  have "n div 16 * 4 \<le> n div 16 * 16"
    by simp
  also have "... \<le> n"
    by simp
  finally show "n div 16 * 4 \<le> n" .
qed

lemma fri_rs_active_layer_sixteenth_radius_list_cap:
  fixes d i N :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and active_round: "i < ceil_log (Suc d)"
    and rounds_fit: "Suc (ceil_log (Suc d)) \<le> N"
    and initial_rate:
      "4 * fri_padded_degree_bound d \<le> clength * scale"
  shows
    "card (fri_rs_close_list
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        received
        (length (fri_canonical_domain_at i) div 16)) \<le> 2"
  by (rule fri_rs_active_layer_small_radius_list_cap[
        OF eval_power active_round rounds_fit initial_rate
          sixteenth_radius_le_quarter_radius])

end

end
