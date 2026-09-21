(*  Title:      Stark/Soundness_Query_Agreement_Generalized.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Query_Agreement_Generalized
  imports
    Soundness_FRI_RO_Actual_Query_Trace_Composition_Boundary
    Soundness_FRI_Padded_Degree
begin

text \<open>
  Polynomial agreement remains quantitative when a composition candidate is
  known only at a padded FRI degree.  The original bound is recovered when the
  supplied candidate-degree bound is at most @{term maxDegree}.
\<close>

context soundness
begin

definition query_agreement_bound_for :: "nat \<Rightarrow> nat"
where
  "query_agreement_bound_for composition_degree_bound =
    max maxDegree composition_degree_bound + length all_constraint_roots"

lemma common_denominator_numerator_degree_le_bound_for:
  assumes deg_f: "degree f < clength"
  shows
    "degree (common_denominator_numerator f as) \<le>
      query_agreement_bound_for composition_degree_bound"
proof -
  have old:
    "degree (common_denominator_numerator f as) \<le> query_agreement_bound"
    by (rule common_denominator_numerator_degree_le_bound[OF deg_f])
  show ?thesis
    using old
    unfolding query_agreement_bound_def query_agreement_bound_for_def
    by linarith
qed

lemma common_denominator_product_degree_le_bound_for:
  assumes deg_q: "degree q \<le> composition_degree_bound"
  shows
    "degree (common_denominator_poly * q) \<le>
      query_agreement_bound_for composition_degree_bound"
proof -
  have product:
    "degree (common_denominator_poly * q) \<le>
      degree common_denominator_poly + degree q"
    by (rule degree_mult_le)
  have denominator:
    "degree common_denominator_poly \<le> length all_constraint_roots"
    by (rule common_denominator_poly_degree_le)
  show ?thesis
    using product denominator deg_q
    unfolding query_agreement_bound_for_def
    by linarith
qed

lemma common_denominator_residual_degree_le_bound_for:
  assumes deg_f: "degree f < clength"
    and deg_q: "degree q \<le> composition_degree_bound"
  shows
    "degree (common_denominator_numerator f as -
      common_denominator_poly * q) \<le>
      query_agreement_bound_for composition_degree_bound"
  by (rule degree_diff_le)
    (rule common_denominator_numerator_degree_le_bound_for[OF deg_f],
     rule common_denominator_product_degree_le_bound_for[OF deg_q])

lemma query_agreement_indices_card_bound_for:
  assumes trace_low: "trace_table_low_degree trace_table"
    and composition_low:
      "composition_table_low_degree composition_degree_bound composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows
    "card (query_agreement_indices trace_table composition_table as) \<le>
      query_agreement_bound_for composition_degree_bound"
proof -
  from trace_low obtain f where deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    unfolding trace_table_low_degree_def by blast
  from composition_low obtain q where
    deg_q: "degree q \<le> composition_degree_bound"
    and composition_table: "composition_table = map (poly q) eval_domain"
    unfolding composition_table_low_degree_def by blast
  let ?A = "query_agreement_indices trace_table composition_table as"
  let ?R =
    "common_denominator_numerator f as - common_denominator_poly * q"
  have A_subset: "?A \<subseteq> query_sample_space"
    unfolding query_agreement_indices_def by auto
  have finite_A: "finite ?A"
    unfolding query_agreement_indices_def query_sample_space_def by simp
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
  have residual_nonzero: "?R \<noteq> 0"
    by (rule common_denominator_residual_nonzero_from_query_disagreement
        [OF trace_table composition_table not_all])
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
      using composition_table eval_domain_nth[OF idx_bound] idx_bound
        eval_domain_length by simp
    have trace_powers:
      "map ((!) trace_table) (powers_scaled idx) =
        map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f)"
      by (rule query_values_trace_powers[OF trace_table])
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

end
end
