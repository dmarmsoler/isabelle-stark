theory Soundness_FRI_Conditioned_Composition_Padding_Agreement
  imports
    Stark.Soundness_FRI_Conditioned_Prequery_Outcome_Bridge
    Stark.Soundness_Query_Agreement_Generalized
begin

context soundness
begin

lemma soundness_root_factor_pCons:
  fixes r :: 'f
  shows "XP 1 - CP r = pCons (- r) 1"
unfolding XP_def CP_def
by (simp add: monom_0 monom_Suc)

lemma soundness_prod_roots_nonzero:
  fixes roots :: "'f list"
  shows "prod roots \<noteq> (0 :: 'f poly)"
proof (induction roots)
  case Nil
  then show ?case
    unfolding prod_def by simp
next
  case (Cons r roots)
  have factor: "XP 1 - CP r \<noteq> (0 :: 'f poly)"
    unfolding soundness_root_factor_pCons by simp
  show ?case
    unfolding prod_Cons
    using factor Cons.IH by simp
qed

lemma soundness_degree_prod_roots:
  fixes roots :: "'f list"
  shows "degree (prod roots :: 'f poly) = length roots"
proof (induction roots)
  case Nil
  then show ?case
    unfolding prod_def by simp
next
  case (Cons r roots)
  have factor_nonzero: "XP 1 - CP r \<noteq> (0 :: 'f poly)"
    unfolding soundness_root_factor_pCons by simp
  have factor_degree: "degree (XP 1 - CP r :: 'f poly) = 1"
    unfolding soundness_root_factor_pCons by simp
  have product:
      "degree (prod (r # roots) :: 'f poly) =
        degree (XP 1 - CP r :: 'f poly) +
          degree (prod roots :: 'f poly)"
    unfolding prod_Cons
    by (rule degree_mult_eq[OF factor_nonzero soundness_prod_roots_nonzero])
  show ?case
    using product factor_degree Cons.IH by simp
qed

lemma common_denominator_residual_zero_imp_degree_le_max:
  assumes deg_f: "degree f < clength"
    and residual_zero:
      "common_denominator_numerator f as -
        common_denominator_poly * q = 0"
  shows "degree q \<le> maxDegree"
proof (cases "q = 0")
  case True
  then show ?thesis by simp
next
  case q_nonzero: False
  have denominator_nonzero:
      "common_denominator_poly \<noteq> 0"
    unfolding common_denominator_poly_def
    by (rule soundness_prod_roots_nonzero)
  have denominator_degree:
      "degree common_denominator_poly = length all_constraint_roots"
    unfolding common_denominator_poly_def
    by (rule soundness_degree_prod_roots)
  have numerator_degree:
      "degree (common_denominator_numerator f as) \<le>
        maxDegree + length all_constraint_roots"
    using common_denominator_numerator_degree_le_bound[OF deg_f]
    unfolding query_agreement_bound_def .
  have numerator_eq:
      "common_denominator_numerator f as =
        common_denominator_poly * q"
    using residual_zero by simp
  have product_degree:
      "degree (common_denominator_poly * q) =
        degree common_denominator_poly + degree q"
    by (rule degree_mult_eq[OF denominator_nonzero q_nonzero])
  show ?thesis
    using numerator_degree denominator_degree product_degree
    unfolding numerator_eq
    by linarith
qed

lemma composition_not_low_max_residual_witness:
  assumes trace_low: "trace_table_low_degree trace_table"
    and composition_low:
      "composition_table_low_degree composition_degree_bound composition_table"
    and composition_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
  obtains f q where
    "degree f < clength"
    "trace_table = map (poly f) eval_domain"
    "degree q \<le> composition_degree_bound"
    "composition_table = map (poly q) eval_domain"
    "common_denominator_numerator f as -
      common_denominator_poly * q \<noteq> 0"
proof -
  from trace_low obtain f where
    deg_f: "degree f < clength"
    and trace_table_eq: "trace_table = map (poly f) eval_domain"
    unfolding trace_table_low_degree_def by blast
  from composition_low obtain q where
    deg_q: "degree q \<le> composition_degree_bound"
    and composition_table_eq:
      "composition_table = map (poly q) eval_domain"
    unfolding composition_table_low_degree_def by blast
  have residual_nonzero:
      "common_denominator_numerator f as -
        common_denominator_poly * q \<noteq> 0"
  proof
    assume residual_zero:
        "common_denominator_numerator f as -
          common_denominator_poly * q = 0"
    have degree_max: "degree q \<le> maxDegree"
      by (rule common_denominator_residual_zero_imp_degree_le_max[
        OF deg_f residual_zero])
    have "composition_table_low_degree maxDegree composition_table"
      unfolding composition_table_low_degree_def
      using degree_max composition_table_eq by blast
    then show False using composition_not_low by contradiction
  qed
  show ?thesis
    by (rule that[OF deg_f trace_table_eq deg_q composition_table_eq
          residual_nonzero])
qed

lemma query_agreement_indices_card_bound_for_if_composition_not_low_max:
  assumes trace_low: "trace_table_low_degree trace_table"
    and composition_low:
      "composition_table_low_degree composition_degree_bound composition_table"
    and composition_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
  shows
    "card (query_agreement_indices trace_table composition_table as) \<le>
      query_agreement_bound_for composition_degree_bound"
proof -
  from composition_not_low_max_residual_witness[
      OF trace_low composition_low composition_not_low]
  obtain f q where
    deg_f: "degree f < clength"
    and trace_table_eq: "trace_table = map (poly f) eval_domain"
    and deg_q: "degree q \<le> composition_degree_bound"
    and composition_table_eq:
      "composition_table = map (poly q) eval_domain"
    and residual_nonzero:
      "common_denominator_numerator f as -
        common_denominator_poly * q \<noteq> 0"
    .
  let ?A = "query_agreement_indices trace_table composition_table as"
  let ?R =
    "common_denominator_numerator f as - common_denominator_poly * q"
  have A_subset: "?A \<subseteq> query_sample_space"
    unfolding query_agreement_indices_def by auto
  have inj: "inj_on (\<lambda>idx. h ^ idx * shift) ?A"
  proof (intro inj_onI)
    fix i j
    assume i_in: "i \<in> ?A"
      and j_in: "j \<in> ?A"
      and eq: "h ^ i * shift = h ^ j * shift"
    have i_bound: "i < clength * scale"
      by (rule query_sample_space_less_domain[OF set_mp[OF A_subset i_in]])
    have j_bound: "j < clength * scale"
      by (rule query_sample_space_less_domain[OF set_mp[OF A_subset j_in]])
    have "h ^ i = h ^ j"
      using eq shift_nonzero by simp
    then show "i = j"
      by (rule h_power_inj_on_eval_domain[OF i_bound j_bound])
  qed
  have image_subset:
      "(\<lambda>idx. h ^ idx * shift) ` ?A \<subseteq> {x. poly ?R x = 0}"
  proof
    fix x
    assume x_in: "x \<in> (\<lambda>idx. h ^ idx * shift) ` ?A"
    then obtain idx where idx_in: "idx \<in> ?A"
      and x_eq: "x = h ^ idx * shift"
      by blast
    have idx_sample: "idx \<in> query_sample_space"
      by (rule set_mp[OF A_subset idx_in])
    have idx_bound: "idx < clength * scale"
      by (rule query_sample_space_less_domain[OF idx_sample])
    have qc: "query_consistent_at trace_table composition_table as idx"
      using idx_in unfolding query_agreement_indices_def by simp
    have comp_value:
        "composition_table ! idx = poly q (h ^ idx * shift)"
      using composition_table_eq eval_domain_nth[OF idx_bound] idx_bound
        eval_domain_length by simp
    have trace_powers:
        "map ((!) trace_table) (powers_scaled idx) =
          map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f)"
      by (rule query_values_trace_powers[OF trace_table_eq])
        (rule query_sample_space_powers_scaled_bound[OF idx_sample])
    have mult:
        "poly common_denominator_poly (h ^ idx * shift) *
            cp_eval as
              (map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f))
              (h ^ idx * shift) =
          poly (common_denominator_numerator f as) (h ^ idx * shift)"
      by (rule common_denominator_mult_cp_eval_trace_powers[OF idx_bound])
    have cp_eq:
        "cp_eval as
            (map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f))
            (h ^ idx * shift) =
          poly q (h ^ idx * shift)"
      using qc comp_value trace_powers
      unfolding query_consistent_at_def by simp
    have
        "poly (common_denominator_numerator f as) (h ^ idx * shift) =
          poly common_denominator_poly (h ^ idx * shift) *
            poly q (h ^ idx * shift)"
      using mult cp_eq by simp
    then have "poly ?R (h ^ idx * shift) = 0"
      by simp
    then show "x \<in> {x. poly ?R x = 0}"
      unfolding x_eq by simp
  qed
  have "card ?A = card ((\<lambda>idx. h ^ idx * shift) ` ?A)"
    using card_image[OF inj] by simp
  also have "... \<le> card {x. poly ?R x = 0}"
    by (rule card_mono[OF poly_roots_finite[OF residual_nonzero]
          image_subset])
  also have "... \<le> degree ?R"
    by (rule card_poly_roots_bound[OF residual_nonzero])
  also have "... \<le> query_agreement_bound_for composition_degree_bound"
    by (rule common_denominator_residual_degree_le_bound_for[OF deg_f deg_q])
  finally show ?thesis .
qed

definition composition_padding_query_lists
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> nat list set"
where
  "composition_padding_query_lists trace_table composition_table as
      composition_degree_bound =
    (if trace_table_low_degree trace_table \<and>
        composition_table_low_degree composition_degree_bound composition_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table
     then query_index_lists_over
       (query_agreement_indices trace_table composition_table as)
     else {})"

lemma composition_padding_query_lists_subset:
  "composition_padding_query_lists trace_table composition_table as
      composition_degree_bound \<subseteq> fri_query_index_list_space"
proof (cases
    "trace_table_low_degree trace_table \<and>
      composition_table_low_degree composition_degree_bound composition_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table")
  assume condition:
      "trace_table_low_degree trace_table \<and>
        composition_table_low_degree composition_degree_bound composition_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table"
  have family_eq:
      "composition_padding_query_lists trace_table composition_table as
          composition_degree_bound =
        query_index_lists_over
          (query_agreement_indices trace_table composition_table as)"
    unfolding composition_padding_query_lists_def
    using condition by simp
  have indices_subset:
      "query_agreement_indices trace_table composition_table as \<subseteq>
        query_sample_space"
    unfolding query_agreement_indices_def by auto
  show ?thesis
    unfolding family_eq
    by (rule query_index_lists_over_subset_fri_query_index_list_space[
      OF indices_subset])
next
  assume not_condition:
      "\<not> (trace_table_low_degree trace_table \<and>
        composition_table_low_degree composition_degree_bound composition_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table)"
  have family_eq:
      "composition_padding_query_lists trace_table composition_table as
          composition_degree_bound = {}"
    unfolding composition_padding_query_lists_def
    by (simp only: if_not_P[OF not_condition])
  show ?thesis
    unfolding family_eq by simp
qed

lemma card_composition_padding_query_lists:
  "card
      (composition_padding_query_lists trace_table composition_table as
        composition_degree_bound) \<le>
    query_agreement_bound_for composition_degree_bound ^ rounds"
proof (cases
    "trace_table_low_degree trace_table \<and>
      composition_table_low_degree composition_degree_bound composition_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table")
  assume condition:
      "trace_table_low_degree trace_table \<and>
        composition_table_low_degree composition_degree_bound composition_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table"
  then have trace_low: "trace_table_low_degree trace_table"
    and composition_low:
      "composition_table_low_degree composition_degree_bound composition_table"
    and composition_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    by blast+
  let ?indices = "query_agreement_indices trace_table composition_table as"
  have finite_indices: "finite ?indices"
    unfolding query_agreement_indices_def query_sample_space_def by simp
  have indices_card:
      "card ?indices \<le> query_agreement_bound_for composition_degree_bound"
    by (rule
      query_agreement_indices_card_bound_for_if_composition_not_low_max[
        OF trace_low composition_low composition_not_low])
  have family_eq:
      "composition_padding_query_lists trace_table composition_table as
          composition_degree_bound =
        query_index_lists_over ?indices"
    unfolding composition_padding_query_lists_def
    by (simp only: if_P[OF condition])
  have
      "card (composition_padding_query_lists trace_table composition_table as
          composition_degree_bound) =
        card ?indices ^ rounds"
    unfolding family_eq
    by (rule card_query_index_lists_over[OF finite_indices])
  also have "... \<le>
      query_agreement_bound_for composition_degree_bound ^ rounds"
    by (rule power_mono[OF indices_card]) simp
  finally show ?thesis .
next
  assume not_condition:
      "\<not> (trace_table_low_degree trace_table \<and>
        composition_table_low_degree composition_degree_bound composition_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table)"
  have family_eq:
      "composition_padding_query_lists trace_table composition_table as
          composition_degree_bound = {}"
    unfolding composition_padding_query_lists_def
    by (simp only: if_not_P[OF not_condition])
  show ?thesis
    unfolding family_eq by simp
qed

lemma composition_padding_query_lists_raw_relation_fiber_bound:
  "query_index_raw_list_relation_fiber_bound
      (composition_padding_query_lists trace_table composition_table as
        composition_degree_bound) \<le>
    rounds * query_raw_preimage_card_envelope
      (rounds *
        (query_agreement_bound_for composition_degree_bound ^ rounds))"
proof (rule query_index_raw_list_relation_fiber_bound_by_card)
  show
    "composition_padding_query_lists trace_table composition_table as
        composition_degree_bound \<subseteq> fri_query_index_list_space"
    by (rule composition_padding_query_lists_subset)
  show
    "card
        (composition_padding_query_lists trace_table composition_table as
          composition_degree_bound) \<le>
      query_agreement_bound_for composition_degree_bound ^ rounds"
    by (rule card_composition_padding_query_lists)
qed

lemma composition_padding_query_lists_strict:
  assumes agreement_lt:
      "query_agreement_bound_for composition_degree_bound <
        query_sample_space_size"
    and rounds_pos: "0 < rounds"
  shows
    "card
        (composition_padding_query_lists trace_table composition_table as
          composition_degree_bound) <
      card fri_query_index_list_space"
proof -
  have power_lt:
      "query_agreement_bound_for composition_degree_bound ^ rounds <
        query_sample_space_size ^ rounds"
    by (rule power_strict_mono[OF agreement_lt _ rounds_pos]) simp
  have
      "card
          (composition_padding_query_lists trace_table composition_table as
            composition_degree_bound) \<le>
        query_agreement_bound_for composition_degree_bound ^ rounds"
    by (rule card_composition_padding_query_lists)
  also have "... < query_sample_space_size ^ rounds"
    by (rule power_lt)
  also have "... = card fri_query_index_list_space"
    unfolding card_fri_query_index_list_space card_query_sample_space by simp
  finally show ?thesis .
qed

lemma composition_padding_query_lists_not_full:
  assumes agreement_lt:
      "query_agreement_bound_for composition_degree_bound <
        query_sample_space_size"
    and rounds_pos: "0 < rounds"
  shows
    "composition_padding_query_lists trace_table composition_table as
        composition_degree_bound \<noteq> fri_query_index_list_space"
proof
  assume equal:
      "composition_padding_query_lists trace_table composition_table as
          composition_degree_bound = fri_query_index_list_space"
  have strict:
      "card
          (composition_padding_query_lists trace_table composition_table as
            composition_degree_bound) <
        card fri_query_index_list_space"
    by (rule composition_padding_query_lists_strict[
      OF agreement_lt rounds_pos])
  show False using strict equal by simp
qed

end
end
