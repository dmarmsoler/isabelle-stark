theory Soundness_FRI_Robust_One_Round
  imports Soundness_FRI_Robust_One_Round_Algebra
begin

context soundness
begin

section \<open>Exact successor proximity and reconstruction candidates\<close>

definition fri_folded_received ::
  "'f \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f"
where
  "fri_folded_received b len fri_dom current =
    (\<lambda>i. fri_table_fold_value b current fri_dom len 1 i)"

definition fri_fold_decoder ::
  "nat \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> 'f"
where
  "fri_fold_decoder k next_dom len fri_dom current b =
    fri_rs_canonical_decoder k next_dom
      (fri_folded_received b len fri_dom current)"

definition fri_fold_decoder_errors ::
  "nat \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat set"
where
  "fri_fold_decoder_errors k next_dom len fri_dom current b =
    code_disagreement_indices {..<length next_dom}
      (fri_folded_received b len fri_dom current)
      (fri_fold_decoder k next_dom len fri_dom current b)"

definition fri_fold_good_challenges ::
  "nat \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f set"
where
  "fri_fold_good_challenges k next_dom len fri_dom current t =
    {b. card (fri_fold_decoder_errors
      k next_dom len fri_dom current b) \<le> t}"

definition fri_fold_decoder_polynomial ::
  "nat \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f poly"
where
  "fri_fold_decoder_polynomial k next_dom len fri_dom current b =
    fri_rs_code_polynomial k next_dom
      (fri_fold_decoder k next_dom len fri_dom current b)"

definition fri_two_fold_reconstruction_for ::
  "nat \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
    'f \<Rightarrow> 'f \<Rightarrow> 'f poly"
where
  "fri_two_fold_reconstruction_for k next_dom len fri_dom current b0 b =
    fri_two_fold_reconstruction b0 b
      (fri_fold_decoder_polynomial
        k next_dom len fri_dom current b0)
      (fri_fold_decoder_polynomial
        k next_dom len fri_dom current b)"

definition fri_two_fold_reconstruction_table ::
  "nat \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
    'f \<Rightarrow> 'f \<Rightarrow> 'f list"
where
  "fri_two_fold_reconstruction_table k next_dom len fri_dom current b0 b =
    map (poly (fri_two_fold_reconstruction_for
      k next_dom len fri_dom current b0 b)) fri_dom"

definition fri_two_fold_reconstruction_word ::
  "nat \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow>
    'f \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> 'f"
where
  "fri_two_fold_reconstruction_word k next_dom len fri_dom current b0 b =
    nth (fri_two_fold_reconstruction_table
      k next_dom len fri_dom current b0 b)"

lemma finite_fri_fold_decoder_errors:
  "finite (fri_fold_decoder_errors
    k next_dom len fri_dom current b)"
  unfolding fri_fold_decoder_errors_def
    code_disagreement_indices_def by simp

lemma finite_fri_fold_good_challenges:
  "finite (fri_fold_good_challenges
    k next_dom len fri_dom current t)"
  by simp

lemma fri_fold_decoder_code:
  "fri_fold_decoder k next_dom len fri_dom current b \<in>
    fri_rs_code_functions k next_dom"
  unfolding fri_fold_decoder_def
  by (rule fri_rs_canonical_decoder_code)

lemma fri_fold_decoder_polynomial_degree:
  "degree (fri_fold_decoder_polynomial
      k next_dom len fri_dom current b) \<le> k"
  unfolding fri_fold_decoder_polynomial_def
  by (rule fri_rs_code_polynomial_degree[OF fri_fold_decoder_code])

lemma fri_fold_decoder_polynomial_represents:
  "fri_fold_decoder k next_dom len fri_dom current b =
    nth (map
      (poly (fri_fold_decoder_polynomial
        k next_dom len fri_dom current b)) next_dom)"
  unfolding fri_fold_decoder_polynomial_def
  by (rule fri_rs_code_polynomial_represents[OF fri_fold_decoder_code])

lemma fri_fold_good_challenge_errors:
  assumes good:
      "b \<in> fri_fold_good_challenges
        k next_dom len fri_dom current t"
  shows
    "card (fri_fold_decoder_errors
      k next_dom len fri_dom current b) \<le> t"
  using good unfolding fri_fold_good_challenges_def by simp

lemma fri_two_fold_reconstruction_for_degree:
  "degree (fri_two_fold_reconstruction_for
      k next_dom len fri_dom current b0 b) \<le> 2 * k + 1"
  unfolding fri_two_fold_reconstruction_for_def
  by (rule fri_two_fold_reconstruction_degree)
    (rule fri_fold_decoder_polynomial_degree)+

lemma fri_two_fold_reconstruction_word_code:
  "fri_two_fold_reconstruction_word
      k next_dom len fri_dom current b0 b \<in>
    fri_rs_code_functions (2 * k + 1) fri_dom"
  unfolding fri_two_fold_reconstruction_word_def
    fri_two_fold_reconstruction_table_def
    fri_rs_code_functions_def fri_rs_code_tables_def
  using fri_two_fold_reconstruction_for_degree[
    of k next_dom len fri_dom current b0 b]
  by auto

lemma length_fri_two_fold_reconstruction_table:
  "length (fri_two_fold_reconstruction_table
      k next_dom len fri_dom current b0 b) = length fri_dom"
  unfolding fri_two_fold_reconstruction_table_def by simp

lemma fri_two_fold_reconstruction_table_fold_anchor:
  assumes len_pos: "0 < len"
    and len_eq: "len = length fri_dom"
    and next_length: "length next_dom = len div 2"
    and i_bound: "i < len div 2"
    and successor_point: "next_dom ! i = (fri_dom ! i) ^ 2"
    and sibling_point:
      "fri_dom ! fri_sibling_index len i = - (fri_dom ! i)"
    and point_nonzero: "fri_dom ! i \<noteq> 0"
  shows
    "fri_table_fold_value b0
        (fri_two_fold_reconstruction_table
          k next_dom len fri_dom current b0 b)
        fri_dom len 1 i =
      fri_fold_decoder k next_dom len fri_dom current b0 i"
proof -
  let ?p = "fri_two_fold_reconstruction_for
    k next_dom len fri_dom current b0 b"
  let ?q0 = "fri_fold_decoder_polynomial
    k next_dom len fri_dom current b0"
  let ?table = "fri_two_fold_reconstruction_table
    k next_dom len fri_dom current b0 b"
  have i_len: "i < length fri_dom"
    using i_bound len_eq by simp
  have sibling_len:
      "fri_sibling_index len i < length fri_dom"
    using len_pos len_eq unfolding fri_sibling_index_def by simp
  have table_i: "?table ! i = poly ?p (fri_dom ! i)"
    unfolding fri_two_fold_reconstruction_table_def
    using i_len by simp
  have table_sibling:
      "?table ! fri_sibling_index len i = poly ?p (- (fri_dom ! i))"
    unfolding fri_two_fold_reconstruction_table_def
    using sibling_len sibling_point by simp
  have polynomial_fold:
      "fri_fold_value b0 (poly ?p (fri_dom ! i))
          (poly ?p (- (fri_dom ! i)))
          (fri_fold_denominator (fri_dom ! i) 1) =
        poly ?q0 ((fri_dom ! i) ^ 2)"
    unfolding fri_two_fold_reconstruction_for_def
    by (rule fri_two_fold_reconstruction_fold_anchor[OF point_nonzero])
  have table_fold:
      "fri_table_fold_value b0 ?table fri_dom len 1 i =
        poly ?q0 ((fri_dom ! i) ^ 2)"
    unfolding fri_table_fold_value_def
    using table_i table_sibling polynomial_fold by simp
  have decoder_represents:
      "fri_fold_decoder k next_dom len fri_dom current b0 =
        nth (map (poly ?q0) next_dom)"
    by (rule fri_fold_decoder_polynomial_represents)
  have decoder_value:
      "fri_fold_decoder k next_dom len fri_dom current b0 i =
        poly ?q0 (next_dom ! i)"
    using arg_cong[OF decoder_represents, where f="\<lambda>f. f i"]
      i_bound next_length by simp
  show ?thesis
    using table_fold decoder_value successor_point by simp
qed

lemma fri_two_fold_reconstruction_table_fold_other:
  assumes challenges_distinct: "b \<noteq> b0"
    and len_pos: "0 < len"
    and len_eq: "len = length fri_dom"
    and next_length: "length next_dom = len div 2"
    and i_bound: "i < len div 2"
    and successor_point: "next_dom ! i = (fri_dom ! i) ^ 2"
    and sibling_point:
      "fri_dom ! fri_sibling_index len i = - (fri_dom ! i)"
    and point_nonzero: "fri_dom ! i \<noteq> 0"
  shows
    "fri_table_fold_value b
        (fri_two_fold_reconstruction_table
          k next_dom len fri_dom current b0 b)
        fri_dom len 1 i =
      fri_fold_decoder k next_dom len fri_dom current b i"
proof -
  let ?p = "fri_two_fold_reconstruction_for
    k next_dom len fri_dom current b0 b"
  let ?q = "fri_fold_decoder_polynomial
    k next_dom len fri_dom current b"
  let ?table = "fri_two_fold_reconstruction_table
    k next_dom len fri_dom current b0 b"
  have i_len: "i < length fri_dom"
    using i_bound len_eq by simp
  have sibling_len:
      "fri_sibling_index len i < length fri_dom"
    using len_pos len_eq unfolding fri_sibling_index_def by simp
  have table_i: "?table ! i = poly ?p (fri_dom ! i)"
    unfolding fri_two_fold_reconstruction_table_def
    using i_len by simp
  have table_sibling:
      "?table ! fri_sibling_index len i = poly ?p (- (fri_dom ! i))"
    unfolding fri_two_fold_reconstruction_table_def
    using sibling_len sibling_point by simp
  have polynomial_fold:
      "fri_fold_value b (poly ?p (fri_dom ! i))
          (poly ?p (- (fri_dom ! i)))
          (fri_fold_denominator (fri_dom ! i) 1) =
        poly ?q ((fri_dom ! i) ^ 2)"
    unfolding fri_two_fold_reconstruction_for_def
    by (rule fri_two_fold_reconstruction_fold_other[
          OF challenges_distinct point_nonzero])
  have table_fold:
      "fri_table_fold_value b ?table fri_dom len 1 i =
        poly ?q ((fri_dom ! i) ^ 2)"
    unfolding fri_table_fold_value_def
    using table_i table_sibling polynomial_fold by simp
  have decoder_represents:
      "fri_fold_decoder k next_dom len fri_dom current b =
        nth (map (poly ?q) next_dom)"
    by (rule fri_fold_decoder_polynomial_represents)
  have decoder_value:
      "fri_fold_decoder k next_dom len fri_dom current b i =
        poly ?q (next_dom ! i)"
    using arg_cong[OF decoder_represents, where f="\<lambda>f. f i"]
      i_bound next_length by simp
  show ?thesis
    using table_fold decoder_value successor_point by simp
qed

lemma fri_two_good_folds_reconstruction_close:
  assumes challenges_distinct: "b \<noteq> b0"
    and anchor_good:
      "b0 \<in> fri_fold_good_challenges
        k next_dom len fri_dom current t"
    and other_good:
      "b \<in> fri_fold_good_challenges
        k next_dom len fri_dom current t"
    and len_pos: "0 < len"
    and even_len: "2 dvd len"
    and len_eq: "len = length fri_dom"
    and next_length: "length next_dom = len div 2"
    and successor_point:
      "\<And>i. i < len div 2 \<Longrightarrow>
        next_dom ! i = (fri_dom ! i) ^ 2"
    and sibling_point:
      "\<And>i. i < len div 2 \<Longrightarrow>
        fri_dom ! fri_sibling_index len i = - (fri_dom ! i)"
    and point_nonzero:
      "\<And>i. i < len div 2 \<Longrightarrow> fri_dom ! i \<noteq> 0"
  shows
    "card (code_disagreement_indices {..<length fri_dom}
        (nth current)
        (fri_two_fold_reconstruction_word
          k next_dom len fri_dom current b0 b)) \<le>
      4 * t"
proof -
  let ?table = "fri_two_fold_reconstruction_table
    k next_dom len fri_dom current b0 b"
  let ?word = "fri_two_fold_reconstruction_word
    k next_dom len fri_dom current b0 b"
  let ?P = "fri_coeff_pair_disagreement_indices
    len fri_dom current ?table"
  let ?AnchorErrors = "fri_fold_decoder_errors
    k next_dom len fri_dom current b0"
  let ?OtherErrors = "fri_fold_decoder_errors
    k next_dom len fri_dom current b"
  have denominator_nonzero:
      "\<And>i. i < len div 2 \<Longrightarrow>
        fri_fold_denominator (fri_dom ! i) 1 \<noteq> 0"
    using point_nonzero two_nonzero
    unfolding fri_fold_denominator_def by simp
  have P_subset: "?P \<subseteq> ?AnchorErrors \<union> ?OtherErrors"
  proof
    fix i
    assume pair: "i \<in> ?P"
    then have i_bound: "i < len div 2"
      unfolding fri_coeff_pair_disagreement_indices_def by simp
    show "i \<in> ?AnchorErrors \<union> ?OtherErrors"
    proof (rule ccontr)
      assume not_union: "i \<notin> ?AnchorErrors \<union> ?OtherErrors"
      then have not_anchor: "i \<notin> ?AnchorErrors"
        and not_other: "i \<notin> ?OtherErrors"
        by simp_all
      have i_next: "i < length next_dom"
        using i_bound next_length by simp
      have current_anchor:
          "fri_table_fold_value b0 current fri_dom len 1 i =
            fri_fold_decoder k next_dom len fri_dom current b0 i"
        using not_anchor i_next
        unfolding fri_fold_decoder_errors_def
          code_disagreement_indices_def fri_folded_received_def
        by simp
      have current_other:
          "fri_table_fold_value b current fri_dom len 1 i =
            fri_fold_decoder k next_dom len fri_dom current b i"
        using not_other i_next
        unfolding fri_fold_decoder_errors_def
          code_disagreement_indices_def fri_folded_received_def
        by simp
      have candidate_anchor:
          "fri_table_fold_value b0 ?table fri_dom len 1 i =
            fri_fold_decoder k next_dom len fri_dom current b0 i"
        by (rule fri_two_fold_reconstruction_table_fold_anchor[
              OF len_pos len_eq next_length i_bound
                successor_point[OF i_bound]
                sibling_point[OF i_bound]
                point_nonzero[OF i_bound]])
      have candidate_other:
          "fri_table_fold_value b ?table fri_dom len 1 i =
            fri_fold_decoder k next_dom len fri_dom current b i"
        by (rule fri_two_fold_reconstruction_table_fold_other[
              OF challenges_distinct len_pos len_eq next_length i_bound
                successor_point[OF i_bound]
                sibling_point[OF i_bound]
                point_nonzero[OF i_bound]])
      have anchor_eq:
          "fri_fold_value b0
              (current ! i) (current ! fri_sibling_index len i)
              (fri_fold_denominator (fri_dom ! i) 1) =
            fri_fold_value b0
              (?table ! i) (?table ! fri_sibling_index len i)
              (fri_fold_denominator (fri_dom ! i) 1)"
        using current_anchor candidate_anchor
        unfolding fri_table_fold_value_def by simp
      have other_eq:
          "fri_fold_value b
              (current ! i) (current ! fri_sibling_index len i)
              (fri_fold_denominator (fri_dom ! i) 1) =
            fri_fold_value b
              (?table ! i) (?table ! fri_sibling_index len i)
              (fri_fold_denominator (fri_dom ! i) 1)"
        using current_other candidate_other
        unfolding fri_table_fold_value_def by simp
      have values_equal:
          "current ! i = ?table ! i \<and>
            current ! fri_sibling_index len i =
              ?table ! fri_sibling_index len i"
        by (rule fri_two_challenge_fold_values_injective[
              OF challenges_distinct denominator_nonzero[OF i_bound]
                anchor_eq other_eq])
      have "i \<notin> ?P"
        using i_bound values_equal
        unfolding fri_coeff_pair_disagreement_indices_def by simp
      then show False using pair by contradiction
    qed
  qed
  have finite_union: "finite (?AnchorErrors \<union> ?OtherErrors)"
    using finite_fri_fold_decoder_errors by simp
  have pair_card: "card ?P \<le> card (?AnchorErrors \<union> ?OtherErrors)"
    by (rule card_mono[OF finite_union P_subset])
  have union_card: "card (?AnchorErrors \<union> ?OtherErrors) \<le> card ?AnchorErrors + card ?OtherErrors"
    by (rule card_Un_le)
  have anchor_card: "card ?AnchorErrors \<le> t"
    by (rule fri_fold_good_challenge_errors[OF anchor_good])
  have other_card: "card ?OtherErrors \<le> t"
    by (rule fri_fold_good_challenge_errors[OF other_good])
  have pair_bound: "card ?P \<le> 2 * t"
    using pair_card union_card anchor_card other_card by linarith
  have raw_pair:
      "card (code_disagreement_indices {..<len}
          (nth current) (nth ?table)) \<le> 2 * card ?P"
    by (rule fri_raw_disagreements_le_twice_pair_disagreements[
          OF len_pos even_len denominator_nonzero])
  have raw_bound:
      "card (code_disagreement_indices {..<len}
          (nth current) (nth ?table)) \<le> 4 * t"
    using raw_pair pair_bound by linarith
  have word_eq: "?word = nth ?table"
    unfolding fri_two_fold_reconstruction_word_def by simp
  show ?thesis
    using raw_bound len_eq word_eq by simp
qed

lemma fri_reconstruction_folded_errors_eq:
  assumes challenges_distinct: "b \<noteq> b0"
    and len_pos: "0 < len"
    and len_eq: "len = length fri_dom"
    and next_length: "length next_dom = len div 2"
    and successor_point:
      "\<And>i. i < len div 2 \<Longrightarrow>
        next_dom ! i = (fri_dom ! i) ^ 2"
    and sibling_point:
      "\<And>i. i < len div 2 \<Longrightarrow>
        fri_dom ! fri_sibling_index len i = - (fri_dom ! i)"
    and point_nonzero:
      "\<And>i. i < len div 2 \<Longrightarrow> fri_dom ! i \<noteq> 0"
  shows
    "fri_folded_disagreement_indices b len fri_dom current
        (fri_two_fold_reconstruction_table
          k next_dom len fri_dom current b0 b) =
      fri_fold_decoder_errors
        k next_dom len fri_dom current b"
proof (rule equalityI)
  show
    "fri_folded_disagreement_indices b len fri_dom current
        (fri_two_fold_reconstruction_table
          k next_dom len fri_dom current b0 b) \<subseteq>
      fri_fold_decoder_errors
        k next_dom len fri_dom current b"
  proof
    fix i
    assume membership:
      "i \<in> fri_folded_disagreement_indices b len fri_dom current
        (fri_two_fold_reconstruction_table
          k next_dom len fri_dom current b0 b)"
    then have i_bound: "i < len div 2"
      and current_diff:
        "fri_table_fold_value b current fri_dom len 1 i \<noteq>
          fri_table_fold_value b
            (fri_two_fold_reconstruction_table
              k next_dom len fri_dom current b0 b)
            fri_dom len 1 i"
      unfolding fri_folded_disagreement_indices_def by simp_all
    have candidate_fold:
        "fri_table_fold_value b
            (fri_two_fold_reconstruction_table
              k next_dom len fri_dom current b0 b)
            fri_dom len 1 i =
          fri_fold_decoder k next_dom len fri_dom current b i"
      by (rule fri_two_fold_reconstruction_table_fold_other[
            OF challenges_distinct len_pos len_eq next_length i_bound
              successor_point[OF i_bound]
              sibling_point[OF i_bound]
              point_nonzero[OF i_bound]])
    show "i \<in> fri_fold_decoder_errors
      k next_dom len fri_dom current b"
      using i_bound next_length current_diff candidate_fold
      unfolding fri_fold_decoder_errors_def
        code_disagreement_indices_def fri_folded_received_def
      by simp
  qed
  show
    "fri_fold_decoder_errors
        k next_dom len fri_dom current b \<subseteq>
      fri_folded_disagreement_indices b len fri_dom current
        (fri_two_fold_reconstruction_table
          k next_dom len fri_dom current b0 b)"
  proof
    fix i
    assume membership:
      "i \<in> fri_fold_decoder_errors
        k next_dom len fri_dom current b"
    then have i_next: "i < length next_dom"
      and current_diff:
        "fri_table_fold_value b current fri_dom len 1 i \<noteq>
          fri_fold_decoder k next_dom len fri_dom current b i"
      unfolding fri_fold_decoder_errors_def
        code_disagreement_indices_def fri_folded_received_def
      by simp_all
    have i_bound: "i < len div 2"
      using i_next next_length by simp
    have candidate_fold:
        "fri_table_fold_value b
            (fri_two_fold_reconstruction_table
              k next_dom len fri_dom current b0 b)
            fri_dom len 1 i =
          fri_fold_decoder k next_dom len fri_dom current b i"
      by (rule fri_two_fold_reconstruction_table_fold_other[
            OF challenges_distinct len_pos len_eq next_length i_bound
              successor_point[OF i_bound]
              sibling_point[OF i_bound]
              point_nonzero[OF i_bound]])
    show
      "i \<in> fri_folded_disagreement_indices b len fri_dom current
        (fri_two_fold_reconstruction_table
          k next_dom len fri_dom current b0 b)"
      using i_bound current_diff candidate_fold
      unfolding fri_folded_disagreement_indices_def by simp
  qed
qed
definition fri_rs_word_table ::
  "nat \<Rightarrow> 'f list \<Rightarrow> (nat \<Rightarrow> 'f) \<Rightarrow> 'f list"
where
  "fri_rs_word_table d fri_dom word =
    map (poly (fri_rs_code_polynomial d fri_dom word)) fri_dom"

lemma length_fri_rs_word_table:
  "length (fri_rs_word_table d fri_dom word) = length fri_dom"
  unfolding fri_rs_word_table_def by simp

lemma fri_rs_word_table_nth:
  assumes word_code: "word \<in> fri_rs_code_functions d fri_dom"
  shows "nth (fri_rs_word_table d fri_dom word) = word"
  unfolding fri_rs_word_table_def
  using fri_rs_code_polynomial_represents[OF word_code] by simp

lemma fri_reconstruction_table_eq_word_table:
  assumes word_code: "word \<in> fri_rs_code_functions (2 * k + 1) fri_dom"
    and reconstruction_word:
      "fri_two_fold_reconstruction_word
        k next_dom len fri_dom current b0 b = word"
  shows
    "fri_two_fold_reconstruction_table
        k next_dom len fri_dom current b0 b =
      fri_rs_word_table (2 * k + 1) fri_dom word"
proof (rule nth_equalityI)
  show
    "length (fri_two_fold_reconstruction_table
        k next_dom len fri_dom current b0 b) =
      length (fri_rs_word_table (2 * k + 1) fri_dom word)"
    using length_fri_two_fold_reconstruction_table
      length_fri_rs_word_table by simp
  fix i
  assume i_bound:
      "i < length (fri_two_fold_reconstruction_table
        k next_dom len fri_dom current b0 b)"
  have reconstruction_nth:
      "nth (fri_two_fold_reconstruction_table
        k next_dom len fri_dom current b0 b) = word"
    using reconstruction_word
    unfolding fri_two_fold_reconstruction_word_def by simp
  have word_nth:
      "nth (fri_rs_word_table (2 * k + 1) fri_dom word) = word"
    by (rule fri_rs_word_table_nth[OF word_code])
  show
    "fri_two_fold_reconstruction_table
        k next_dom len fri_dom current b0 b ! i =
      fri_rs_word_table (2 * k + 1) fri_dom word ! i"
    using arg_cong[OF reconstruction_nth, where f="\<lambda>f. f i"]
      arg_cong[OF word_nth, where f="\<lambda>f. f i"] by simp
qed

lemma fri_good_reconstruction_fiber_card_le_Suc:
  assumes anchor_good:
      "b0 \<in> fri_fold_good_challenges
        k next_dom len fri_dom current t"
    and word_code:
      "word \<in> fri_rs_code_functions (2 * k + 1) fri_dom"
    and current_far:
      "2 * t < card (code_disagreement_indices {..<length fri_dom}
        (nth current) word)"
    and len_pos: "0 < len"
    and even_len: "2 dvd len"
    and len_eq: "len = length fri_dom"
    and next_length: "length next_dom = len div 2"
    and successor_point:
      "\<And>i. i < len div 2 \<Longrightarrow>
        next_dom ! i = (fri_dom ! i) ^ 2"
    and sibling_point:
      "\<And>i. i < len div 2 \<Longrightarrow>
        fri_dom ! fri_sibling_index len i = - (fri_dom ! i)"
    and point_nonzero:
      "\<And>i. i < len div 2 \<Longrightarrow> fri_dom ! i \<noteq> 0"
  shows
    "card {b \<in>
        fri_fold_good_challenges
          k next_dom len fri_dom current t - {b0}.
      fri_two_fold_reconstruction_word
        k next_dom len fri_dom current b0 b = word} \<le> Suc t"
proof -
  let ?claimed = "fri_rs_word_table (2 * k + 1) fri_dom word"
  let ?IndexSet = "fri_coeff_pair_disagreement_indices
    len fri_dom current ?claimed"
  let ?Fiber = "{b \<in>
    fri_fold_good_challenges
      k next_dom len fri_dom current t - {b0}.
    fri_two_fold_reconstruction_word
      k next_dom len fri_dom current b0 b = word}"
  let ?hidden = "\<lambda>i. fri_table_local_hiding_challenges
    current ?claimed fri_dom len 1 i"
  have denominator_nonzero:
      "\<And>i. i < len div 2 \<Longrightarrow>
        fri_fold_denominator (fri_dom ! i) 1 \<noteq> 0"
    using point_nonzero two_nonzero
    unfolding fri_fold_denominator_def by simp
  have finite_indices: "finite ?IndexSet"
    by (rule finite_fri_coeff_pair_disagreement_indices)
  have finite_fiber: "finite ?Fiber"
    by simp
  have finite_hidden:
      "\<And>i. i \<in> ?IndexSet \<Longrightarrow> finite (?hidden i)"
    by simp
  have hidden_card:
      "\<And>i. i \<in> ?IndexSet \<Longrightarrow> card (?hidden i) \<le> 1"
  proof -
    fix i
    assume "i \<in> ?IndexSet"
    then show "card (?hidden i) \<le> 1"
      by (rule fri_pair_local_hiding_card_le_one)
  qed
  have per_challenge:
      "\<And>b. b \<in> ?Fiber \<Longrightarrow>
        card ?IndexSet - t \<le>
          card (hiding_indices ?IndexSet ?hidden b)"
  proof -
    fix b
    assume fiber: "b \<in> ?Fiber"
    then have b_good:
        "b \<in> fri_fold_good_challenges
          k next_dom len fri_dom current t"
      and b_distinct: "b \<noteq> b0"
      and reconstruction_word:
        "fri_two_fold_reconstruction_word
          k next_dom len fri_dom current b0 b = word"
      by simp_all
    have tables_equal:
        "fri_two_fold_reconstruction_table
            k next_dom len fri_dom current b0 b = ?claimed"
      by (rule fri_reconstruction_table_eq_word_table[
            OF word_code reconstruction_word])
    have error_sets:
        "fri_folded_disagreement_indices b len fri_dom current
            (fri_two_fold_reconstruction_table
              k next_dom len fri_dom current b0 b) =
          fri_fold_decoder_errors
            k next_dom len fri_dom current b"
      by (rule fri_reconstruction_folded_errors_eq[
            OF b_distinct len_pos len_eq next_length
              successor_point sibling_point point_nonzero])
    have folded_close:
        "card (fri_folded_disagreement_indices
          b len fri_dom current ?claimed) \<le> t"
      using error_sets tables_equal
        fri_fold_good_challenge_errors[OF b_good] by simp
    show
      "card ?IndexSet - t \<le>
        card (hiding_indices ?IndexSet ?hidden b)"
      by (rule fri_pair_hiding_indices_lower_bound[OF folded_close])
  qed
  have claimed_nth: "nth ?claimed = word"
    by (rule fri_rs_word_table_nth[OF word_code])
  have raw_pair:
      "card (code_disagreement_indices {..<len}
          (nth current) (nth ?claimed)) \<le> 2 * card ?IndexSet"
    by (rule fri_raw_disagreements_le_twice_pair_disagreements[
          OF len_pos even_len denominator_nonzero])
  have raw_far:
      "2 * t < card (code_disagreement_indices {..<len}
        (nth current) (nth ?claimed))"
    using current_far len_eq claimed_nth by simp
  have radius: "t < card ?IndexSet"
    using raw_pair raw_far by linarith
  show ?thesis
    by (rule hiding_incidence_card_le_Suc[
          OF finite_indices finite_fiber finite_hidden hidden_card
            per_challenge radius])
qed

lemma fri_one_round_good_challenges_card_exact:
  assumes anchor_good:
      "b0 \<in> fri_fold_good_challenges
        k next_dom len fri_dom current t"
    and current_far:
      "2 * t < fri_rs_distance_to_code
        (2 * k + 1) fri_dom (nth current)"
    and len_pos: "0 < len"
    and even_len: "2 dvd len"
    and len_eq: "len = length fri_dom"
    and next_length: "length next_dom = len div 2"
    and successor_point:
      "\<And>i. i < len div 2 \<Longrightarrow>
        next_dom ! i = (fri_dom ! i) ^ 2"
    and sibling_point:
      "\<And>i. i < len div 2 \<Longrightarrow>
        fri_dom ! fri_sibling_index len i = - (fri_dom ! i)"
    and point_nonzero:
      "\<And>i. i < len div 2 \<Longrightarrow> fri_dom ! i \<noteq> 0"
  shows
    "card (fri_fold_good_challenges
        k next_dom len fri_dom current t) \<le>
      1 + card (fri_rs_close_list
        (2 * k + 1) fri_dom (nth current) (4 * t)) * Suc t"
proof -
  let ?Good = "fri_fold_good_challenges
    k next_dom len fri_dom current t"
  let ?Close = "fri_rs_close_list
    (2 * k + 1) fri_dom (nth current) (4 * t)"
  let ?candidate = "fri_two_fold_reconstruction_word
    k next_dom len fri_dom current b0"
  have finite_good: "finite ?Good"
    by (rule finite_fri_fold_good_challenges)
  have finite_close: "finite ?Close"
    by (rule finite_fri_rs_close_list)
  have candidate_image: "?candidate ` (?Good - {b0}) \<subseteq> ?Close"
  proof
    fix word
    assume image_mem: "word \<in> ?candidate ` (?Good - {b0})"
    then obtain b where b_good: "b \<in> ?Good"
      and b_distinct: "b \<noteq> b0"
      and word_eq: "word = ?candidate b"
      by auto
    have word_code:
        "?candidate b \<in> fri_rs_code_functions (2 * k + 1) fri_dom"
      by (rule fri_two_fold_reconstruction_word_code)
    have word_close:
        "card (code_disagreement_indices {..<length fri_dom}
          (nth current) (?candidate b)) \<le> 4 * t"
      by (rule fri_two_good_folds_reconstruction_close[
            OF b_distinct anchor_good b_good len_pos even_len len_eq
              next_length successor_point sibling_point point_nonzero])
    show "word \<in> ?Close"
      using word_code word_close word_eq
      unfolding fri_rs_close_list_def by simp
  qed
  have fiber_bound:
      "\<And>word. word \<in> ?Close \<Longrightarrow>
        card {b \<in> ?Good - {b0}. ?candidate b = word} \<le> Suc t"
  proof -
    fix word
    assume word_close: "word \<in> ?Close"
    then have word_code:
        "word \<in> fri_rs_code_functions (2 * k + 1) fri_dom"
      unfolding fri_rs_close_list_def by simp
    have distance_le:
        "fri_rs_distance_to_code
            (2 * k + 1) fri_dom (nth current) \<le>
          card (code_disagreement_indices {..<length fri_dom}
            (nth current) word)"
      by (rule fri_rs_distance_to_code_le[OF word_code])
    have word_far:
        "2 * t < card (code_disagreement_indices {..<length fri_dom}
          (nth current) word)"
      using current_far distance_le by linarith
    show
      "card {b \<in> ?Good - {b0}. ?candidate b = word} \<le> Suc t"
      by (rule fri_good_reconstruction_fiber_card_le_Suc[
            OF anchor_good word_code word_far len_pos even_len len_eq
              next_length successor_point sibling_point point_nonzero])
  qed
  show ?thesis
    by (rule finite_fibers_card_bound[
          OF finite_good finite_close anchor_good candidate_image
            fiber_bound])
qed

lemma fri_one_round_good_challenges_card_le:
  assumes anchor_good:
      "b0 \<in> fri_fold_good_challenges
        k next_dom len fri_dom current t"
    and current_far:
      "2 * t < fri_rs_distance_to_code
        (2 * k + 1) fri_dom (nth current)"
    and close_list_cap:
      "card (fri_rs_close_list
        (2 * k + 1) fri_dom (nth current) (4 * t)) \<le> L"
    and len_pos: "0 < len"
    and even_len: "2 dvd len"
    and len_eq: "len = length fri_dom"
    and next_length: "length next_dom = len div 2"
    and successor_point:
      "\<And>i. i < len div 2 \<Longrightarrow>
        next_dom ! i = (fri_dom ! i) ^ 2"
    and sibling_point:
      "\<And>i. i < len div 2 \<Longrightarrow>
        fri_dom ! fri_sibling_index len i = - (fri_dom ! i)"
    and point_nonzero:
      "\<And>i. i < len div 2 \<Longrightarrow> fri_dom ! i \<noteq> 0"
  shows
    "card (fri_fold_good_challenges
        k next_dom len fri_dom current t) \<le>
      1 + L * Suc t"
proof -
  have exact:
      "card (fri_fold_good_challenges
          k next_dom len fri_dom current t) \<le>
        1 + card (fri_rs_close_list
          (2 * k + 1) fri_dom (nth current) (4 * t)) * Suc t"
    by (rule fri_one_round_good_challenges_card_exact[
          OF anchor_good current_far len_pos even_len len_eq
            next_length successor_point sibling_point point_nonzero])
  have product_mono:
      "card (fri_rs_close_list
          (2 * k + 1) fri_dom (nth current) (4 * t)) * Suc t \<le>
        L * Suc t"
    by (rule mult_right_mono[OF close_list_cap]) simp
  show ?thesis
    using exact product_mono by linarith
qed

lemma four_half_sixteenth_le_quarter:
  fixes n :: nat
  shows "4 * ((n div 2) div 16) \<le> n div 4"
proof (rule less_eq_div_iff_mult_less_eq[
    OF zero_less_numeral, THEN iffD2])
  have "4 * ((n div 2) div 16) * 4 \<le>
      4 * ((n div 2) div 16) * 8"
    by simp
  also have "... = ((n div 2) div 16) * 32"
    by simp
  also have "... \<le> n"
    by simp
  finally show "4 * ((n div 2) div 16) * 4 \<le> n" .
qed

lemma fri_canonical_one_round_decode_or_reject:
  fixes d i N :: nat
  assumes eval_power: "clength * scale = 2 ^ N"
    and active_round: "i < ceil_log (Suc d)"
    and rounds_fit: "Suc (ceil_log (Suc d)) \<le> N"
    and initial_rate:
      "4 * fri_padded_degree_bound d \<le> clength * scale"
  defines
    "t \<equiv> length (fri_canonical_domain_at (Suc i)) div 16"
  shows
    "fri_rs_distance_to_code
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i) (nth current) \<le> 2 * t \<or>
      card (fri_fold_good_challenges
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (length (fri_canonical_domain_at i))
        (fri_canonical_domain_at i) current t) \<le> 2 * t + 3"
proof -
  let ?dom = "fri_canonical_domain_at i"
  let ?next_dom = "fri_canonical_domain_at (Suc i)"
  let ?len = "length ?dom"
  let ?k = "fri_degree_after (Suc i) (fri_padded_degree_bound d)"
  let ?Good =
    "fri_fold_good_challenges ?k ?next_dom ?len ?dom current t"
  have two_rounds: "i + 2 \<le> N"
    using active_round rounds_fit by linarith
  have i_lt_N: "i < N"
    using two_rounds by linarith
  have i_le_N: "i \<le> N"
    using i_lt_N by simp
  have len_pos: "0 < ?len"
    by (rule fri_canonical_domain_at_pos[OF eval_power i_le_N])
  have even_len: "2 dvd ?len"
    by (rule fri_canonical_domain_at_even[OF eval_power i_lt_N])
  have next_length: "length ?next_dom = ?len div 2"
    by (rule fri_canonical_domain_successor_length[
          OF eval_power i_lt_N])
  have round: "?len * 2 ^ i = clength * scale"
    by (rule fri_canonical_domain_at_round_product[
          OF eval_power i_le_N])
  have dom_eq:
      "?dom = map (\<lambda>idx. (h ^ idx * shift) ^ (2 ^ i)) [0..<?len]"
    unfolding fri_canonical_domain_at_def
      fri_canonical_domain_at_length by simp
  have successor_map:
      "?next_dom =
        map (\<lambda>j. (?dom ! j) ^ 2) [0..<?len div 2]"
    by (rule fri_canonical_domain_successor_map_square[
          OF eval_power i_lt_N])
  have successor_point:
      "\<And>j. j < ?len div 2 \<Longrightarrow>
        ?next_dom ! j = (?dom ! j) ^ 2"
    using successor_map by simp
  have sibling_point:
      "\<And>j. j < ?len div 2 \<Longrightarrow>
        ?dom ! fri_sibling_index ?len j = - (?dom ! j)"
  proof -
    fix j
    assume j_bound: "j < ?len div 2"
    have j_len: "j < ?len"
      using j_bound by simp
    have sibling_len: "fri_sibling_index ?len j < ?len"
      using len_pos unfolding fri_sibling_index_def by simp
    have dom_j:
        "?dom ! j = (h ^ j * shift) ^ (2 ^ i)"
      by (rule fri_canonical_domain_at_nth[OF j_len])
    have dom_sibling:
        "?dom ! fri_sibling_index ?len j =
          (h ^ fri_sibling_index ?len j * shift) ^ (2 ^ i)"
      by (rule fri_canonical_domain_at_nth[OF sibling_len])
    show "?dom ! fri_sibling_index ?len j = - (?dom ! j)"
      using fri_sibling_domain_round[
          OF len_pos even_len round, of j]
        dom_j dom_sibling
      unfolding fri_sibling_index_def by simp
  qed
  have point_nonzero:
      "\<And>j. j < ?len div 2 \<Longrightarrow> ?dom ! j \<noteq> 0"
  proof -
    fix j
    assume j_bound: "j < ?len div 2"
    have j_len: "j < ?len"
      using j_bound by simp
    have dom_j: "?dom ! j = (h ^ j * shift) ^ (2 ^ i)"
      by (rule fri_canonical_domain_at_nth[OF j_len])
    show "?dom ! j \<noteq> 0"
      using dom_j h_nonzero shift_nonzero by simp
  qed
  have degree_step:
      "fri_degree_after i (fri_padded_degree_bound d) =
        2 * ?k + 1"
    by (rule fri_degree_after_padded_step[OF active_round])
  have radius:
      "4 * t \<le> ?len div 4"
    unfolding t_def next_length
    by (rule four_half_sixteenth_le_quarter)
  have close_cap:
      "card (fri_rs_close_list
          (2 * ?k + 1) ?dom (nth current) (4 * t)) \<le> 2"
  proof -
    have
        "card (fri_rs_close_list
          (fri_degree_after i (fri_padded_degree_bound d))
          ?dom (nth current) (4 * t)) \<le> 2"
      by (rule fri_rs_active_layer_small_radius_list_cap[
            OF eval_power active_round rounds_fit initial_rate radius])
    then show ?thesis
      unfolding degree_step .
  qed
  show ?thesis
  proof (cases
      "fri_rs_distance_to_code
        (fri_degree_after i (fri_padded_degree_bound d))
        ?dom (nth current) \<le> 2 * t")
    case True
    then show ?thesis by simp
  next
    case False
    have far_at_current_degree:
        "2 * t < fri_rs_distance_to_code
          (fri_degree_after i (fri_padded_degree_bound d))
          ?dom (nth current)"
      using False by simp
    have current_far:
        "2 * t < fri_rs_distance_to_code
          (2 * ?k + 1) ?dom (nth current)"
      using far_at_current_degree
      unfolding degree_step .
    show ?thesis
    proof (cases "?Good = {}")
      case True
      then show ?thesis by simp
    next
      case False
      then obtain b0 where anchor_good: "b0 \<in> ?Good"
        by blast
      have good_bound: "card ?Good \<le> 1 + 2 * Suc t"
        by (rule fri_one_round_good_challenges_card_le[
              OF anchor_good current_far close_cap len_pos even_len
                refl next_length successor_point sibling_point
                point_nonzero])
      show ?thesis
        by (rule disjI2) (use good_bound in simp)
    qed
  qed
qed

end

end
