theory Soundness_FRI_Conditioned_Query_Challenge_Dual
  imports Stark.Soundness_FRI_Conditioned_Query_Start
begin

context soundness
begin

definition fri_symbolic_fold_odd_polynomial
  :: "'f poly \<Rightarrow> 'f poly"
where
  "fri_symbolic_fold_odd_polynomial p =
    poly_of_list (nths_pred (coeffs p) odd)"

definition fri_symbolic_fold_even_polynomial
  :: "'f poly \<Rightarrow> 'f poly"
where
  "fri_symbolic_fold_even_polynomial p =
    poly_of_list (nths_pred (coeffs p) even)"

definition fri_challenge_degenerate_agreement_indices
  :: "'f poly \<Rightarrow> 'f poly \<Rightarrow> 'f list \<Rightarrow> nat set"
where
  "fri_challenge_degenerate_agreement_indices p q xs =
    {i. i < length xs \<and>
      poly (fri_symbolic_fold_odd_polynomial p) (xs ! i) = 0 \<and>
      poly (fri_symbolic_fold_even_polynomial p) (xs ! i) =
        poly q (xs ! i)}"

lemma fri_symbolic_fold_polynomial_eval_affine:
  "poly (fri_symbolic_fold_polynomial p b) x =
    b * poly (fri_symbolic_fold_odd_polynomial p) x +
      poly (fri_symbolic_fold_even_polynomial p) x"
  unfolding fri_symbolic_fold_polynomial_def
    fri_symbolic_fold_odd_polynomial_def
    fri_symbolic_fold_even_polynomial_def CP_def
  by (simp add: poly_monom)

lemma fri_symbolic_fold_eval_challenge_unique:
  assumes odd_nonzero:
      "poly (fri_symbolic_fold_odd_polynomial p) x \<noteq> 0"
    and left:
      "poly (fri_symbolic_fold_polynomial p b) x = poly q x"
    and right:
      "poly (fri_symbolic_fold_polynomial p b') x = poly q x"
  shows "b = b'"
proof -
  have equal_sums:
      "b * poly (fri_symbolic_fold_odd_polynomial p) x +
          poly (fri_symbolic_fold_even_polynomial p) x =
        b' * poly (fri_symbolic_fold_odd_polynomial p) x +
          poly (fri_symbolic_fold_even_polynomial p) x"
    using left right
    by (simp only: fri_symbolic_fold_polynomial_eval_affine)
  have equal_products:
      "b * poly (fri_symbolic_fold_odd_polynomial p) x =
        b' * poly (fri_symbolic_fold_odd_polynomial p) x"
    using equal_sums by simp
  then show ?thesis
    using odd_nonzero by simp
qed

lemma fri_challenge_degenerate_agreement_indices_subset:
  "fri_challenge_degenerate_agreement_indices p q xs \<subseteq>
    fri_polynomial_agreement_indices
      (fri_symbolic_fold_polynomial p 0) q xs"
  unfolding fri_challenge_degenerate_agreement_indices_def
    fri_polynomial_agreement_indices_def
  by (auto simp add: fri_symbolic_fold_polynomial_eval_affine)

lemma fri_challenge_degenerate_agreement_imp_agreement:
  assumes idx:
      "i \<in> fri_challenge_degenerate_agreement_indices p q xs"
  shows
      "i \<in> fri_polynomial_agreement_indices
        (fri_symbolic_fold_polynomial p b) q xs"
proof -
  have i_bound: "i < length xs"
    and odd_zero:
      "poly (fri_symbolic_fold_odd_polynomial p) (xs ! i) = 0"
    and base:
      "poly (fri_symbolic_fold_even_polynomial p) (xs ! i) =
        poly q (xs ! i)"
    using idx
    unfolding fri_challenge_degenerate_agreement_indices_def by blast+
  have
      "poly (fri_symbolic_fold_polynomial p b) (xs ! i) =
        poly q (xs ! i)"
    unfolding fri_symbolic_fold_polynomial_eval_affine
    using odd_zero base by simp
  then show ?thesis
    unfolding fri_polynomial_agreement_indices_def
    using i_bound by simp
qed

lemma fri_nondegenerate_agreement_challenge_unique:
  assumes left:
      "i \<in> fri_polynomial_agreement_indices
        (fri_symbolic_fold_polynomial p b) q xs"
    and right:
      "i \<in> fri_polynomial_agreement_indices
        (fri_symbolic_fold_polynomial p b') q xs"
    and not_degenerate:
      "i \<notin> fri_challenge_degenerate_agreement_indices p q xs"
  shows "b = b'"
proof -
  have i_bound: "i < length xs"
    and left_eq:
      "poly (fri_symbolic_fold_polynomial p b) (xs ! i) =
        poly q (xs ! i)"
    and right_eq:
      "poly (fri_symbolic_fold_polynomial p b') (xs ! i) =
        poly q (xs ! i)"
    using left right
    unfolding fri_polynomial_agreement_indices_def by blast+
  have odd_nonzero:
      "poly (fri_symbolic_fold_odd_polynomial p) (xs ! i) \<noteq> 0"
  proof
    assume odd_zero:
      "poly (fri_symbolic_fold_odd_polynomial p) (xs ! i) = 0"
    have base:
      "poly (fri_symbolic_fold_even_polynomial p) (xs ! i) =
        poly q (xs ! i)"
      using left_eq odd_zero
      unfolding fri_symbolic_fold_polynomial_eval_affine by simp
    have
      "i \<in> fri_challenge_degenerate_agreement_indices p q xs"
      unfolding fri_challenge_degenerate_agreement_indices_def
      using i_bound odd_zero base by simp
    then show False using not_degenerate by contradiction
  qed
  show ?thesis
    by (rule fri_symbolic_fold_eval_challenge_unique[
      OF odd_nonzero left_eq right_eq])
qed

definition fri_conditioned_degenerate_agreement_indices
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
where
  "fri_conditioned_degenerate_agreement_indices i current next =
    fri_challenge_degenerate_agreement_indices
      (fri_table_interpolant (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i current))
      (fri_table_interpolant (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i) next))
      (fri_canonical_domain_at (Suc i))"

lemma fri_conditioned_degenerate_agreement_indices_subset:
  "fri_conditioned_degenerate_agreement_indices i current next \<subseteq>
    fri_conditioned_agreement_indices i current next b"
proof
  fix idx
  assume
    "idx \<in> fri_conditioned_degenerate_agreement_indices i current next"
  then show
    "idx \<in> fri_conditioned_agreement_indices i current next b"
    unfolding fri_conditioned_degenerate_agreement_indices_def
      fri_conditioned_agreement_indices_def
    by (rule fri_challenge_degenerate_agreement_imp_agreement)
qed

lemma fri_conditioned_nondegenerate_agreement_challenge_unique:
  assumes left:
      "idx \<in> fri_conditioned_agreement_indices i current next b"
    and right:
      "idx \<in> fri_conditioned_agreement_indices i current next b'"
    and not_degenerate:
      "idx \<notin> fri_conditioned_degenerate_agreement_indices i current next"
  shows "b = b'"
  using left right not_degenerate
  unfolding fri_conditioned_agreement_indices_def
    fri_conditioned_degenerate_agreement_indices_def
  by (rule fri_nondegenerate_agreement_challenge_unique)

lemma card_fri_conditioned_degenerate_agreement_indices_strict:
  fixes prefix :: "'f list"
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_bound: "i < ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and current_cover:
      "length (fri_canonical_domain_at i) \<le> length current"
    and next_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le> length next"
    and committed: "committed i prefix = current"
    and current_not_low:
      "\<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i current)"
    and next_low:
      "fri_table_low_degree_on
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i) next)"
  shows
    "card (fri_conditioned_degenerate_agreement_indices i current next) \<le>
      length (fri_canonical_domain_at (Suc i)) - 1"
proof -
  have field_two: "2 \<le> CARD('f)"
  proof -
    have finite: "finite (UNIV::'f set)" by simp
    have subset: "{0, 1::'f} \<subseteq> UNIV" by simp
    have "card {0, 1::'f} \<le> card (UNIV::'f set)"
      by (rule card_mono[OF finite subset])
    then show ?thesis by simp
  qed
  have cover_card:
      "card (fri_conditioned_bad_challenges d committed i prefix) \<le> 1"
    by (rule card_fri_conditioned_bad_challenges_le_one)
  have cover_not_univ:
      "fri_conditioned_bad_challenges d committed i prefix \<noteq> UNIV"
  proof
    assume eq: "fri_conditioned_bad_challenges d committed i prefix = UNIV"
    have "CARD('f) \<le> 1"
      using cover_card unfolding eq by simp
    then show False using field_two by simp
  qed
  then obtain b where not_cover:
      "b \<notin> fri_conditioned_bad_challenges d committed i prefix"
    by blast
  have agreement:
      "card (fri_conditioned_agreement_indices i current next b) \<le>
        length (fri_canonical_domain_at (Suc i)) - 1"
    by (rule card_fri_conditioned_agreement_indices_strict[
      OF eval_power round_bound rounds_le current_cover next_cover
        committed current_not_low next_low not_cover])
  have subset:
      "fri_conditioned_degenerate_agreement_indices i current next \<subseteq>
        fri_conditioned_agreement_indices i current next b"
    by (rule fri_conditioned_degenerate_agreement_indices_subset)
  have finite_agreement:
      "finite (fri_conditioned_agreement_indices i current next b)"
    unfolding fri_conditioned_agreement_indices_def
      fri_polynomial_agreement_indices_def
    by simp
  have
      "card (fri_conditioned_degenerate_agreement_indices i current next) \<le>
        card (fri_conditioned_agreement_indices i current next b)"
    by (rule card_mono[OF finite_agreement subset])
  then show ?thesis
    by (rule order_trans[OF _ agreement])
qed

definition fri_conditioned_degenerate_residual_query_lists
  :: "'f list \<Rightarrow> 'f list list \<Rightarrow> nat \<Rightarrow> nat list set"
where
  "fri_conditioned_degenerate_residual_query_lists roots layers i =
    {qs. \<forall>round_idx < length qs.
      fri_evidence_next_idx roots qs round_idx i \<in>
        fri_conditioned_degenerate_agreement_indices i
          (layers ! i) (layers ! Suc i)}"

lemma fri_conditioned_degenerate_residual_query_lists_subset:
  "fri_conditioned_degenerate_residual_query_lists roots layers i \<subseteq>
    fri_conditioned_residual_query_lists roots challenges layers i"
  unfolding fri_conditioned_degenerate_residual_query_lists_def
    fri_conditioned_residual_query_lists_def
  using fri_conditioned_degenerate_agreement_indices_subset
  by blast

definition fri_conditioned_residual_query_lists_at_value
  :: "'f list \<Rightarrow> 'f \<Rightarrow> 'f list list \<Rightarrow> nat \<Rightarrow> nat list set"
where
  "fri_conditioned_residual_query_lists_at_value roots b layers i =
    {qs. \<forall>round_idx < length qs.
      fri_evidence_next_idx roots qs round_idx i \<in>
        fri_conditioned_agreement_indices i
          (layers ! i) (layers ! Suc i) b}"

lemma fri_conditioned_residual_query_lists_at_value_eq:
  assumes i_bound: "i < length challenges"
  shows
    "fri_conditioned_residual_query_lists_at_value roots
        (challenges ! i) layers i =
      fri_conditioned_residual_query_lists roots challenges layers i"
  unfolding fri_conditioned_residual_query_lists_at_value_def
    fri_conditioned_residual_query_lists_def
  by simp

definition fri_conditioned_quantitative_residual_query_lists_at_value
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f protocol_channel \<Rightarrow> nat \<Rightarrow>
      nat list set"
where
  "fri_conditioned_quantitative_residual_query_lists_at_value d roots b
      final_value prefix_state i =
    (let layers =
      fri_builder_conceptual_layers roots prefix_state final_value
     in {qs \<in> fri_query_index_list_space.
       b \<notin> fri_conditioned_bad_challenges d
         (\<lambda>j _. layers ! j) i [] \<and>
       \<not> fri_table_low_degree_on
         (fri_degree_after i (fri_padded_degree_bound d))
         (fri_canonical_domain_at i)
         (fri_conditioned_layer_table i (layers ! i)) \<and>
       fri_table_low_degree_on
         (fri_degree_after (Suc i) (fri_padded_degree_bound d))
         (fri_canonical_domain_at (Suc i))
         (fri_conditioned_layer_table (Suc i) (layers ! Suc i)) \<and>
       qs \<in> fri_conditioned_residual_query_lists_at_value
         roots b layers i})"

definition fri_conditioned_quantitative_degenerate_query_lists_at
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f protocol_channel \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat list set"
where
  "fri_conditioned_quantitative_degenerate_query_lists_at d roots
      final_value prefix_state i round_idx =
    (let layers =
      fri_builder_conceptual_layers roots prefix_state final_value
     in {qs \<in> fri_query_index_list_space.
       \<not> fri_table_low_degree_on
         (fri_degree_after i (fri_padded_degree_bound d))
         (fri_canonical_domain_at i)
         (fri_conditioned_layer_table i (layers ! i)) \<and>
       fri_table_low_degree_on
         (fri_degree_after (Suc i) (fri_padded_degree_bound d))
         (fri_canonical_domain_at (Suc i))
         (fri_conditioned_layer_table (Suc i) (layers ! Suc i)) \<and>
       round_idx < length qs \<and>
       fri_evidence_next_idx roots qs round_idx i \<in>
         fri_conditioned_degenerate_agreement_indices i
           (layers ! i) (layers ! Suc i)})"

lemma fri_conditioned_quantitative_residual_query_lists_at_value_eq:
  assumes i_bound: "i < length challenges"
  shows
    "fri_conditioned_quantitative_residual_query_lists_at_value d roots
        (challenges ! i) final_value prefix_state i =
      fri_conditioned_quantitative_residual_query_lists_at d roots
        challenges final_value prefix_state i"
  using i_bound
  unfolding
    fri_conditioned_quantitative_residual_query_lists_at_value_def
    fri_conditioned_quantitative_residual_query_lists_at_def Let_def
    fri_conditioned_residual_query_lists_at_value_def
    fri_conditioned_residual_query_lists_def
    fri_conditioned_bad_challenges_def
  by simp

lemma fri_conditioned_quantitative_residual_imp_degenerate:
  assumes residual:
      "qs \<in> fri_conditioned_quantitative_residual_query_lists_at_value
        d roots b final_value prefix_state i"
    and round_bound: "round_idx < length qs"
    and idx:
      "fri_evidence_next_idx roots qs round_idx i \<in>
        fri_conditioned_degenerate_agreement_indices i
          (fri_builder_conceptual_layers roots prefix_state final_value ! i)
          (fri_builder_conceptual_layers roots prefix_state final_value !
            Suc i)"
  shows
    "qs \<in> fri_conditioned_quantitative_degenerate_query_lists_at d roots
        final_value prefix_state i round_idx"
  using residual round_bound idx
  unfolding
    fri_conditioned_quantitative_residual_query_lists_at_value_def
    fri_conditioned_quantitative_degenerate_query_lists_at_def Let_def
  by blast

lemma fri_conditioned_quantitative_residual_nondegenerate_unique:
  assumes left:
      "qs \<in> fri_conditioned_quantitative_residual_query_lists_at_value
        d roots b final_value prefix_state i"
    and right:
      "qs \<in> fri_conditioned_quantitative_residual_query_lists_at_value
        d roots b' final_value prefix_state i"
    and round_bound: "round_idx < length qs"
    and not_degenerate:
      "qs \<notin> fri_conditioned_quantitative_degenerate_query_lists_at d roots
        final_value prefix_state i round_idx"
  shows "b = b'"
proof -
  let ?layers =
    "fri_builder_conceptual_layers roots prefix_state final_value"
  have left_agreement:
      "fri_evidence_next_idx roots qs round_idx i \<in>
        fri_conditioned_agreement_indices i
          (?layers ! i) (?layers ! Suc i) b"
    using left round_bound
    unfolding
      fri_conditioned_quantitative_residual_query_lists_at_value_def
      fri_conditioned_residual_query_lists_at_value_def Let_def
    by blast
  have right_agreement:
      "fri_evidence_next_idx roots qs round_idx i \<in>
        fri_conditioned_agreement_indices i
          (?layers ! i) (?layers ! Suc i) b'"
    using right round_bound
    unfolding
      fri_conditioned_quantitative_residual_query_lists_at_value_def
      fri_conditioned_residual_query_lists_at_value_def Let_def
    by blast
  have index_not_degenerate:
      "fri_evidence_next_idx roots qs round_idx i \<notin>
        fri_conditioned_degenerate_agreement_indices i
          (?layers ! i) (?layers ! Suc i)"
  proof
    assume degenerate:
      "fri_evidence_next_idx roots qs round_idx i \<in>
        fri_conditioned_degenerate_agreement_indices i
          (?layers ! i) (?layers ! Suc i)"
    have
      "qs \<in> fri_conditioned_quantitative_degenerate_query_lists_at d roots
        final_value prefix_state i round_idx"
      by (rule fri_conditioned_quantitative_residual_imp_degenerate[
        OF left round_bound degenerate])
    then show False using not_degenerate by contradiction
  qed
  show ?thesis
    by (rule fri_conditioned_nondegenerate_agreement_challenge_unique[
      OF left_agreement right_agreement index_not_degenerate])
qed

lemma fri_conditioned_degenerate_agreement_indices_subset_range:
  "fri_conditioned_degenerate_agreement_indices i current next \<subseteq>
    {..<length (fri_canonical_domain_at (Suc i))}"
  by (rule subset_trans[
      OF fri_conditioned_degenerate_agreement_indices_subset
        fri_conditioned_agreement_indices_subset])

lemma card_fri_conditioned_degenerate_query_indices:
  fixes prefix :: "'f list"
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_bound: "i < ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and current_cover:
      "length (fri_canonical_domain_at i) \<le> length current"
    and next_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le> length next"
    and committed: "committed i prefix = current"
    and current_not_low:
      "\<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i current)"
    and next_low:
      "fri_table_low_degree_on
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i) next)"
    and modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
  shows
    "card
      (fri_conditioned_query_indices roots i
        (fri_conditioned_degenerate_agreement_indices i current next)) \<le>
      modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) - 1)"
proof (rule card_fri_conditioned_query_indices)
  show
    "0 < length (fri_canonical_domain_at (Suc i))"
    by (rule modulus_pos)
  show
    "fri_conditioned_degenerate_agreement_indices i current next \<subseteq>
      {..<length (fri_canonical_domain_at (Suc i))}"
    by (rule fri_conditioned_degenerate_agreement_indices_subset_range)
  show
    "card (fri_conditioned_degenerate_agreement_indices i current next) \<le>
      length (fri_canonical_domain_at (Suc i)) - 1"
    by (rule card_fri_conditioned_degenerate_agreement_indices_strict[
      where N=N and d=d and i=i and committed=committed
        and prefix=prefix,
      OF eval_power round_bound rounds_le current_cover next_cover
        committed current_not_low next_low])
qed

lemma card_fri_conditioned_degenerate_raw_query_values:
  fixes prefix :: "'f list"
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_bound: "i < ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and current_cover:
      "length (fri_canonical_domain_at i) \<le> length current"
    and next_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le> length next"
    and committed: "committed i prefix = current"
    and current_not_low:
      "\<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i current)"
    and next_low:
      "fri_table_low_degree_on
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i) next)"
    and modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
  shows
    "card
      (query_index_raw_preimage
        (fri_conditioned_query_indices roots i
          (fri_conditioned_degenerate_agreement_indices i current next))) \<le>
      query_raw_preimage_card_envelope
        (modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i)))
          (length (fri_canonical_domain_at (Suc i)) - 1))"
proof -
  let ?I =
    "fri_conditioned_query_indices roots i
      (fri_conditioned_degenerate_agreement_indices i current next)"
  let ?K =
    "modulo_preimage_card_envelope query_sample_space_size
      (length (fri_canonical_domain_at (Suc i)))
      (length (fri_canonical_domain_at (Suc i)) - 1)"
  have subset: "?I \<subseteq> query_sample_space"
    by (rule fri_conditioned_query_indices_subset)
  have raw:
      "card (query_index_raw_preimage ?I) \<le>
        query_raw_preimage_card_envelope (card ?I)"
    by (rule card_query_index_raw_preimage_le_query_envelope[OF subset])
  have index: "card ?I \<le> ?K"
    by (rule card_fri_conditioned_degenerate_query_indices[
      where N=N and d=d and i=i and roots=roots
        and committed=committed and prefix=prefix,
      OF eval_power round_bound rounds_le current_cover next_cover
        committed current_not_low next_low modulus_pos])
  have envelope:
      "query_raw_preimage_card_envelope (card ?I) \<le>
        query_raw_preimage_card_envelope ?K"
    by (rule query_raw_preimage_card_envelope_mono[OF index])
  show ?thesis
    by (rule order_trans[OF raw envelope])
qed

lemma fri_conditioned_residual_at_value_restricted_subset:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and layer_bound: "i < length roots"
  shows
    "fri_conditioned_residual_query_lists_at_value roots b layers i \<inter>
        fri_query_index_list_space \<subseteq>
      fri_conditioned_query_lists
        (fri_conditioned_query_indices roots i
          (fri_conditioned_agreement_indices i
            (layers ! i) (layers ! Suc i) b))"
proof
  fix qs
  assume qs:
      "qs \<in>
        fri_conditioned_residual_query_lists_at_value roots b layers i \<inter>
          fri_query_index_list_space"
  then have qs_len: "length qs = rounds"
    and qs_space: "set qs \<subseteq> query_sample_space"
    unfolding fri_query_index_list_space_def by auto
  have entries:
      "set qs \<subseteq>
        fri_conditioned_query_indices roots i
          (fri_conditioned_agreement_indices i
            (layers ! i) (layers ! Suc i) b)"
  proof
    fix q
    assume q_in: "q \<in> set qs"
    then obtain round_idx where round_bound: "round_idx < length qs"
      and q_eq: "q = qs ! round_idx"
      by (metis in_set_conv_nth)
    have agreement:
        "fri_evidence_next_idx roots qs round_idx i \<in>
          fri_conditioned_agreement_indices i
            (layers ! i) (layers ! Suc i) b"
      using qs round_bound
      unfolding fri_conditioned_residual_query_lists_at_value_def by auto
    have mod_agreement:
        "q mod length (fri_canonical_domain_at (Suc i)) \<in>
          fri_conditioned_agreement_indices i
            (layers ! i) (layers ! Suc i) b"
      using agreement
        fri_evidence_next_idx_at[
          OF eval_power roots_le layer_bound round_bound]
        q_eq
      by simp
    show
      "q \<in> fri_conditioned_query_indices roots i
        (fri_conditioned_agreement_indices i
          (layers ! i) (layers ! Suc i) b)"
      using qs_space q_in mod_agreement
      unfolding fri_conditioned_query_indices_def by auto
  qed
  show
      "qs \<in> fri_conditioned_query_lists
        (fri_conditioned_query_indices roots i
          (fri_conditioned_agreement_indices i
            (layers ! i) (layers ! Suc i) b))"
    unfolding fri_conditioned_query_lists_def
    using qs_len entries by simp
qed

lemma card_fri_conditioned_residual_at_value_restricted:
  assumes eval_power: "clength * scale = 2 ^ N"
    and roots_le: "length roots \<le> N"
    and layer_bound: "i < length roots"
    and agreement_card:
      "card (fri_conditioned_agreement_indices i
        (layers ! i) (layers ! Suc i) b) \<le> K"
    and modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
  shows
    "card
      (fri_conditioned_residual_query_lists_at_value roots b layers i \<inter>
        fri_query_index_list_space) \<le>
      (modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i))) K) ^ rounds"
proof -
  let ?A =
    "fri_conditioned_agreement_indices i
      (layers ! i) (layers ! Suc i) b"
  let ?I = "fri_conditioned_query_indices roots i ?A"
  have subset:
      "fri_conditioned_residual_query_lists_at_value roots b layers i \<inter>
          fri_query_index_list_space \<subseteq> fri_conditioned_query_lists ?I"
    by (rule fri_conditioned_residual_at_value_restricted_subset[
      OF eval_power roots_le layer_bound])
  have finite_lists: "finite (fri_conditioned_query_lists ?I)"
    unfolding fri_conditioned_query_lists_def
    by (rule finite_lists_length_eq)
      (rule finite_fri_conditioned_query_indices)
  have card_subset:
      "card
        (fri_conditioned_residual_query_lists_at_value roots b layers i \<inter>
          fri_query_index_list_space) \<le>
        card (fri_conditioned_query_lists ?I)"
    by (rule card_mono[OF finite_lists subset])
  have indices_card:
      "card ?I \<le>
        modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i))) K"
    by (rule card_fri_conditioned_query_indices[
      OF modulus_pos fri_conditioned_agreement_indices_subset
        agreement_card])
  have lists_card:
      "card (fri_conditioned_query_lists ?I) = card ?I ^ rounds"
    by (rule card_fri_conditioned_query_lists)
      (rule finite_fri_conditioned_query_indices)
  have card_subset_power:
      "card
        (fri_conditioned_residual_query_lists_at_value roots b layers i \<inter>
          fri_query_index_list_space) \<le> card ?I ^ rounds"
    using card_subset lists_card by simp
  have envelope_power:
      "card ?I ^ rounds \<le>
        (modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i))) K) ^ rounds"
    by (rule power_mono[OF indices_card]) simp
  show ?thesis
    by (rule order_trans[OF card_subset_power envelope_power])
qed

lemma card_fri_conditioned_quantitative_residual_query_lists_at_value:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_count: "length roots = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and i_bound: "i < length roots"
  shows
    "card
      (fri_conditioned_quantitative_residual_query_lists_at_value d roots b
        final_value prefix_state i) \<le>
      (modulo_preimage_card_envelope query_sample_space_size
        (length (fri_canonical_domain_at (Suc i)))
        (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
proof (cases
    "b \<notin> fri_conditioned_bad_challenges d
        (\<lambda>j _. fri_builder_conceptual_layers roots prefix_state
          final_value ! j) i [] \<and>
      \<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i
          (fri_builder_conceptual_layers roots prefix_state
            final_value ! i)) \<and>
      fri_table_low_degree_on
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i)
          (fri_builder_conceptual_layers roots prefix_state final_value !
            Suc i))")
  case False
  then have empty:
      "fri_conditioned_quantitative_residual_query_lists_at_value d roots b
        final_value prefix_state i = {}"
    unfolding
      fri_conditioned_quantitative_residual_query_lists_at_value_def
      by auto
  show ?thesis unfolding empty by simp
next
  case True
  let ?layers =
    "fri_builder_conceptual_layers roots prefix_state final_value"
  have root_le: "length roots \<le> N"
    using round_count rounds_le by simp
  have current_cover:
      "length (fri_canonical_domain_at i) \<le> length (?layers ! i)"
    by (rule fri_builder_conceptual_layers_cover)
      (use i_bound in simp)
  have next_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        length (?layers ! Suc i)"
    by (rule fri_builder_conceptual_layers_cover)
      (use i_bound in simp)
  have agreement_card:
      "card
        (fri_conditioned_agreement_indices i
          (?layers ! i) (?layers ! Suc i) b) \<le>
        length (fri_canonical_domain_at (Suc i)) - 1"
    by (rule card_fri_conditioned_agreement_indices_strict[
      where N=N and d=d and i=i
        and committed="\<lambda>j _. ?layers ! j" and prefix="[]",
      OF eval_power])
      (use round_count rounds_le current_cover next_cover True i_bound
        in simp_all)
  have modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
    by (rule fri_canonical_domain_at_pos[OF eval_power])
      (use round_count rounds_le i_bound in simp)
  have residual_card:
      "card
        (fri_conditioned_residual_query_lists_at_value roots b ?layers i \<inter>
          fri_query_index_list_space) \<le>
        (modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i)))
          (length (fri_canonical_domain_at (Suc i)) - 1)) ^ rounds"
    by (rule card_fri_conditioned_residual_at_value_restricted[
      OF eval_power root_le i_bound agreement_card modulus_pos])
  have set_eq:
      "fri_conditioned_quantitative_residual_query_lists_at_value d roots b
          final_value prefix_state i =
        fri_conditioned_residual_query_lists_at_value roots b ?layers i \<inter>
          fri_query_index_list_space"
    using True
    unfolding
      fri_conditioned_quantitative_residual_query_lists_at_value_def
    by auto
  show ?thesis
    unfolding set_eq by (rule residual_card)
qed

definition fri_conditioned_quantitative_degenerate_raw_values_at
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f protocol_channel \<Rightarrow> nat \<Rightarrow> 'f set"
where
  "fri_conditioned_quantitative_degenerate_raw_values_at d roots
      final_value prefix_state i =
    (let layers =
      fri_builder_conceptual_layers roots prefix_state final_value
     in if
       \<not> fri_table_low_degree_on
         (fri_degree_after i (fri_padded_degree_bound d))
         (fri_canonical_domain_at i)
         (fri_conditioned_layer_table i (layers ! i)) \<and>
       fri_table_low_degree_on
         (fri_degree_after (Suc i) (fri_padded_degree_bound d))
         (fri_canonical_domain_at (Suc i))
         (fri_conditioned_layer_table (Suc i) (layers ! Suc i))
     then
       query_index_raw_preimage
         (fri_conditioned_query_indices roots i
           (fri_conditioned_degenerate_agreement_indices i
             (layers ! i) (layers ! Suc i)))
     else {})"

definition fri_conditioned_degenerate_raw_value_card_bound :: "nat \<Rightarrow> nat"
where
  "fri_conditioned_degenerate_raw_value_card_bound d =
    (\<Sum>i < ceil_log (Suc d).
      query_raw_preimage_card_envelope
        (modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i)))
          (length (fri_canonical_domain_at (Suc i)) - 1)))"

lemma card_fri_conditioned_quantitative_degenerate_raw_values_at:
  assumes eval_power: "clength * scale = 2 ^ N"
    and round_count: "length roots = ceil_log (Suc d)"
    and rounds_le: "ceil_log (Suc d) \<le> N"
    and i_bound: "i < length roots"
  shows
    "card
      (fri_conditioned_quantitative_degenerate_raw_values_at d roots
        final_value prefix_state i) \<le>
      query_raw_preimage_card_envelope
        (modulo_preimage_card_envelope query_sample_space_size
          (length (fri_canonical_domain_at (Suc i)))
          (length (fri_canonical_domain_at (Suc i)) - 1))"
proof (cases
    "\<not> fri_table_low_degree_on
        (fri_degree_after i (fri_padded_degree_bound d))
        (fri_canonical_domain_at i)
        (fri_conditioned_layer_table i
          (fri_builder_conceptual_layers roots prefix_state
            final_value ! i)) \<and>
      fri_table_low_degree_on
        (fri_degree_after (Suc i) (fri_padded_degree_bound d))
        (fri_canonical_domain_at (Suc i))
        (fri_conditioned_layer_table (Suc i)
          (fri_builder_conceptual_layers roots prefix_state final_value !
            Suc i))")
  case False
  show ?thesis
    unfolding fri_conditioned_quantitative_degenerate_raw_values_at_def
      Let_def if_not_P[OF False]
    by simp
next
  case True
  let ?layers =
    "fri_builder_conceptual_layers roots prefix_state final_value"
  have current_cover:
      "length (fri_canonical_domain_at i) \<le> length (?layers ! i)"
    by (rule fri_builder_conceptual_layers_cover)
      (use i_bound in simp)
  have next_cover:
      "length (fri_canonical_domain_at (Suc i)) \<le>
        length (?layers ! Suc i)"
    by (rule fri_builder_conceptual_layers_cover)
      (use i_bound in simp)
  have modulus_pos:
      "0 < length (fri_canonical_domain_at (Suc i))"
    by (rule fri_canonical_domain_at_pos[OF eval_power])
      (use round_count rounds_le i_bound in simp)
  have raw:
      "card
        (query_index_raw_preimage
          (fri_conditioned_query_indices roots i
            (fri_conditioned_degenerate_agreement_indices i
              (?layers ! i) (?layers ! Suc i)))) \<le>
        query_raw_preimage_card_envelope
          (modulo_preimage_card_envelope query_sample_space_size
            (length (fri_canonical_domain_at (Suc i)))
            (length (fri_canonical_domain_at (Suc i)) - 1))"
    by (rule card_fri_conditioned_degenerate_raw_query_values[
      where N=N and d=d and i=i and roots=roots
        and committed="\<lambda>j _. ?layers ! j" and prefix="[]",
      OF eval_power])
      (use round_count rounds_le current_cover next_cover True i_bound
        modulus_pos in simp_all)
  show ?thesis
    unfolding fri_conditioned_quantitative_degenerate_raw_values_at_def
      Let_def
    using True raw by simp
qed

lemma fri_conditioned_degenerate_raw_value_card_bound_mono:
  assumes le: "d \<le> D"
  shows
    "fri_conditioned_degenerate_raw_value_card_bound d \<le>
      fri_conditioned_degenerate_raw_value_card_bound D"
  unfolding fri_conditioned_degenerate_raw_value_card_bound_def
  by (rule sum_mono2)
    (use ceil_log_mono[of "Suc d" "Suc D"] le in auto)

end
end
