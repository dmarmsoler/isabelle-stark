(*  Title:      Stark/Soundness_Core_Base.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Core_Base
  imports Stark_Core.Stark
begin

text \<open>
  Core definitions and deterministic relations used by the STARK soundness
  development. Later layers separate Merkle binding, verifier execution, bad
  events, FRI, random-oracle accounting, and the public reduction theorems.
\<close>

locale soundness =
  verifier concat omega shift scale clength powers to_nat of_nat size spec rounds spec2
  for concat :: "'f::proth_field \<Rightarrow> 'f \<Rightarrow> 'f"
    and omega :: 'f
    and shift :: 'f
    and scale :: nat
    and clength :: nat
    and powers :: nat
    and to_nat :: "'f \<Rightarrow> nat"
    and of_nat :: "nat \<Rightarrow> 'f"
    and size :: nat
    and spec :: "(('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat) list"
    and rounds :: nat
    and spec2 :: "(('f list \<Rightarrow> 'f) \<times> nat list) list"
  +
  fixes trace_fri_error :: prob
    and composition_fri_error :: prob
    and merkle_binding_error :: prob
  assumes rounds_positive: "0 < rounds"
    and spec_query_margin:
      "Max (degrees clength spec) +
        sum_list (map (\<lambda>(_, roots, _). length roots) spec)
        < clength * scale - Max (set [0..<powers]) * scale"
begin

definition trace_satisfies_constraint
  :: "'f poly \<Rightarrow> ('f poly list \<Rightarrow> 'f poly) \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "trace_satisfies_constraint f c roots \<longleftrightarrow>
      (\<forall>r \<in> set roots.
        poly (c (trace_powers_of f)) (g ^ r) = 0)"

definition exists_valid_trace :: bool
  where
    "exists_valid_trace \<longleftrightarrow>
      (\<exists>f.
        degree f < clength \<and>
        (\<forall>(c, roots, d) \<in> set spec.
          trace_satisfies_constraint f c roots))"

definition composition_error_bound :: prob
  where "composition_error_bound = 1 / nnreal size"

definition query_sample_space_size :: nat
  where
    "query_sample_space_size =
      clength * scale - Max (set [0..<powers]) * scale"

definition query_sample_space :: "nat set"
  where "query_sample_space = {idx. idx < query_sample_space_size}"

definition all_constraint_roots :: "'f list"
  where
    "all_constraint_roots =
      remdups (List.concat (map (\<lambda>(c, roots, d). g_map roots) spec))"

definition query_agreement_bound :: nat
  where "query_agreement_bound = maxDegree + length all_constraint_roots"

definition query_error_bound :: prob
  where
    "query_error_bound =
      nnreal query_agreement_bound / nnreal query_sample_space_size"

definition soundness_bound :: prob
  where
    "soundness_bound =
      composition_error_bound +
      trace_fri_error +
      composition_fri_error +
      nnreal rounds * query_error_bound"

definition soundness_bound_with_merkle :: prob
  where
    "soundness_bound_with_merkle =
      soundness_bound + merkle_binding_error"

text \<open>
  Soundness should expose a transcript-only verifier interface: the adversary
  chooses the proof transcript, while the verifier starts from an empty
  random-oracle/hash map and the initial Fiat-Shamir state.
\<close>

definition verifier_initial_state :: "'f list \<Rightarrow> 'f protocol_channel"
  where
    "verifier_initial_state tr =
      \<lparr>HashMap = fmempty, PState = 0, PTranscript = tr,
       PTraceFriCounter = 0, PCompositionFriCounter = 0,
       PAlphaCounter = 0, PQueryCounter = 0\<rparr>"

definition verify_transcript
  where
    "verify_transcript tr =
      execute verify_monad (verifier_initial_state tr)"

lemma verifier_initial_state_simps[simp]:
  "HashMap (verifier_initial_state tr) = fmempty"
  "PState (verifier_initial_state tr) = 0"
  "PTranscript (verifier_initial_state tr) = tr"
  "PTraceFriCounter (verifier_initial_state tr) = 0"
  "PCompositionFriCounter (verifier_initial_state tr) = 0"
  "PAlphaCounter (verifier_initial_state tr) = 0"
  "PQueryCounter (verifier_initial_state tr) = 0"
  unfolding verifier_initial_state_def by simp_all

definition alpha_future_fresh
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "alpha_future_fresh s \<longleftrightarrow>
      (\<forall>i x.
        PAlphaCounter s \<le> i \<longrightarrow>
        fmlookup (HashMap s) (AlphaChallenge i x) = None)"

definition trace_fri_future_fresh
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "trace_fri_future_fresh s \<longleftrightarrow>
      (\<forall>i x.
        PTraceFriCounter s \<le> i \<longrightarrow>
        fmlookup (HashMap s) (TraceFriChallenge i x) = None)"

definition composition_fri_future_fresh
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "composition_fri_future_fresh s \<longleftrightarrow>
      (\<forall>i x.
        PCompositionFriCounter s \<le> i \<longrightarrow>
        fmlookup (HashMap s) (CompositionFriChallenge i x) = None)"

definition query_future_fresh
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> bool"
  where
    "query_future_fresh s \<longleftrightarrow>
      (\<forall>i x.
        PQueryCounter s \<le> i \<longrightarrow>
        fmlookup (HashMap s) (QueryIndexChallenge i x) = None)"

lemma alpha_future_fresh_current:
  assumes "alpha_future_fresh s"
  shows
    "fmlookup (HashMap s)
      (AlphaChallenge (PAlphaCounter s) (PState s)) = None"
  using assms unfolding alpha_future_fresh_def by simp

lemma query_future_fresh_current:
  assumes "query_future_fresh s"
  shows
    "fmlookup (HashMap s)
      (QueryIndexChallenge (PQueryCounter s) (PState s)) = None"
  using assms unfolding query_future_fresh_def by simp

lemma verifier_initial_alpha_future_fresh[simp]:
  "alpha_future_fresh (verifier_initial_state tr)"
  unfolding alpha_future_fresh_def by simp

lemma verifier_initial_trace_fri_future_fresh[simp]:
  "trace_fri_future_fresh (verifier_initial_state tr)"
  unfolding trace_fri_future_fresh_def by simp

lemma verifier_initial_composition_fri_future_fresh[simp]:
  "composition_fri_future_fresh (verifier_initial_state tr)"
  unfolding composition_fri_future_fresh_def by simp

lemma verifier_initial_query_future_fresh[simp]:
  "query_future_fresh (verifier_initial_state tr)"
  unfolding query_future_fresh_def by simp

text \<open>
  The current bound has no separate Merkle-binding error term.  Merkle binding
  is represented by the conditional premise
  \<^term>\<open>initial_merkle_binding_no_bad\<close> below, because the present hash-map
  model does not assign a collision-resistance probability to Merkle roots.
\<close>

subsection \<open>Proof structure for soundness\<close>

text \<open>
  The proof should decompose an accepting verifier execution for a false
  statement into four bad events:

    \<^item> the trace FRI accepts a table that is not the evaluation of a trace
      polynomial satisfying \<^term>\<open>degree f < clength\<close>;
    \<^item> the composition FRI accepts a table that is not low-degree;
    \<^item> the random linear combination hides a violated constraint;
    \<^item> the verifier's sampled query indices miss all disagreement points.

  The following predicates and lemmas are the intended interface between the
  probabilistic proof over \<^term>\<open>verify_monad\<close> and the deterministic
  algebraic arguments.
\<close>

definition accepted :: "('x \<times> 's) option \<Rightarrow> bool"
  where "accepted out \<longleftrightarrow> \<not> Option.is_none out"

definition trace_table_low_degree :: "'f list \<Rightarrow> bool"
  where
    "trace_table_low_degree ys \<longleftrightarrow>
      (\<exists>f. degree f < clength \<and> ys = map (poly f) eval_domain)"

definition composition_table_low_degree :: "nat \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "composition_table_low_degree d ys \<longleftrightarrow>
      (\<exists>q. degree q \<le> d \<and> ys = map (poly q) eval_domain)"

definition trace_table_valid :: "'f list \<Rightarrow> bool"
  where
    "trace_table_valid ys \<longleftrightarrow>
      (\<exists>f.
        degree f < clength \<and>
        ys = map (poly f) eval_domain \<and>
        (\<forall>(c, roots, d) \<in> set spec.
          trace_satisfies_constraint f c roots))"

definition query_consistent_at :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> bool"
  where
    "query_consistent_at trace_table composition_table as idx \<longleftrightarrow>
      idx < clength * scale \<and>
      length trace_table = clength * scale \<and>
      length composition_table = clength * scale \<and>
      (\<forall>i \<in> set (powers_scaled idx). i < length trace_table) \<and>
      composition_table ! idx =
        cp_eval as (map ((!) trace_table) (powers_scaled idx)) (h ^ idx * shift)"

lemma query_consistent_at_cong_opened_values:
  assumes trace_len:
      "length trace_table = length trace_table'"
    and composition_len:
      "length composition_table = length composition_table'"
    and trace_values:
      "map ((!) trace_table) (powers_scaled idx) =
        map ((!) trace_table') (powers_scaled idx)"
    and composition_value:
      "composition_table ! idx = composition_table' ! idx"
  shows
    "query_consistent_at trace_table composition_table as idx \<longleftrightarrow>
      query_consistent_at trace_table' composition_table' as idx"
proof -
  have cp_eq:
    "cp_eval as (map ((!) trace_table) (powers_scaled idx))
        (h ^ idx * shift) =
      cp_eval as (map ((!) trace_table') (powers_scaled idx))
        (h ^ idx * shift)"
    by (rule arg_cong[where
          f="\<lambda>xs. cp_eval as xs (h ^ idx * shift)", OF trace_values])
  show ?thesis
    unfolding query_consistent_at_def
    using trace_len composition_len composition_value cp_eq by simp
qed

definition all_queries_consistent :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "all_queries_consistent trace_table composition_table as \<longleftrightarrow>
      (\<forall>idx \<in> query_sample_space.
        query_consistent_at trace_table composition_table as idx)"

definition bad_query_indices :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
  where
    "bad_query_indices trace_table composition_table as =
      {idx \<in> query_sample_space.
        \<not> query_consistent_at trace_table composition_table as idx}"

definition query_agreement_indices :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
  where
    "query_agreement_indices trace_table composition_table as =
      {idx \<in> query_sample_space.
        query_consistent_at trace_table composition_table as idx}"

definition query_disagreement_indices :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
  where
    "query_disagreement_indices trace_table composition_table as =
      bad_query_indices trace_table composition_table as"

definition query_samples_miss_disagreements
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "query_samples_miss_disagreements trace_table composition_table as query_idxs \<longleftrightarrow>
      query_disagreement_indices trace_table composition_table as \<noteq> {} \<and>
      set query_idxs \<subseteq> query_agreement_indices trace_table composition_table as"

definition violated_constraints
  :: "'f poly \<Rightarrow> (('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat) set"
  where
    "violated_constraints f =
      {entry \<in> set spec.
        case entry of (c, roots, d) \<Rightarrow>
          \<not> trace_satisfies_constraint f c roots}"

definition constraint_remainder_bad
  :: "'f poly \<Rightarrow> (('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat) \<Rightarrow> bool"
  where
    "constraint_remainder_bad f entry \<longleftrightarrow>
      (case entry of (c, roots, d) \<Rightarrow>
        (\<exists>r \<in> set roots.
          poly (c (trace_powers_of f)) (g ^ r) \<noteq> 0))"

definition composition_vanishes_on_constraint_domain :: "'f poly \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "composition_vanishes_on_constraint_domain f as \<longleftrightarrow>
      (\<forall>x \<in> set G. poly (cp as (trace_powers_of f)) x = 0)"

definition constraint_root_residual
  :: "'f poly \<Rightarrow> nat \<Rightarrow>
      ('f \<times> (('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat)) \<Rightarrow> 'f"
  where
    "constraint_root_residual f r weighted_entry =
      (case weighted_entry of (a, (c, roots, d)) \<Rightarrow>
        if r \<in> set roots
        then a * poly (c (trace_powers_of f)) (g ^ r)
        else 0)"

definition composition_root_residual :: "'f poly \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f"
  where
    "composition_root_residual f as r =
      sum_list (map (constraint_root_residual f r) (zip as spec))"

definition random_combination_hides_violations :: "'f poly \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "random_combination_hides_violations f as \<longleftrightarrow>
      violated_constraints f \<noteq> {} \<and>
      (\<forall>entry \<in> violated_constraints f.
        case entry of (c, roots, d) \<Rightarrow>
          (\<forall>r \<in> set roots. composition_root_residual f as r = 0))"

definition constraint_root_cofactor :: "nat list \<Rightarrow> 'f poly"
  where
    "constraint_root_cofactor roots =
      prod (filter (\<lambda>x. x \<notin> set (g_map roots)) all_constraint_roots)"

definition common_denominator_poly :: "'f poly"
  where "common_denominator_poly = prod all_constraint_roots"

definition common_denominator_numerator_term
  :: "'f poly \<Rightarrow>
      ('f \<times> (('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat)) \<Rightarrow>
      'f poly"
  where
    "common_denominator_numerator_term f weighted_entry =
      (case weighted_entry of (a, (c, roots, d)) \<Rightarrow>
        CP a * c (trace_powers_of f) * constraint_root_cofactor roots)"

definition common_denominator_numerator :: "'f poly \<Rightarrow> 'f list \<Rightarrow> 'f poly"
  where
    "common_denominator_numerator f as =
      sum_list
        (map (common_denominator_numerator_term f) (zip as spec))"

definition composition_spec_eval_term
  :: "'f poly \<Rightarrow> 'f \<Rightarrow>
      ('f \<times> (('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat)) \<Rightarrow>
      'f"
  where
    "composition_spec_eval_term f x weighted_entry =
      (case weighted_entry of (a, (c, roots, d)) \<Rightarrow>
        a * (poly (c (trace_powers_of f)) x /
          poly (prod (g_map roots)) x))"

definition composition_spec_eval :: "'f poly \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> 'f"
  where
    "composition_spec_eval f as x =
      sum_list (map (composition_spec_eval_term f x) (zip as spec))"

definition common_denominator_constraint_root_residual
  :: "'f poly \<Rightarrow> nat \<Rightarrow>
      ('f \<times> (('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat)) \<Rightarrow> 'f"
  where
    "common_denominator_constraint_root_residual f r weighted_entry =
      (case weighted_entry of (a, (c, roots, d)) \<Rightarrow>
        if r \<in> set roots
        then
          a * poly (c (trace_powers_of f)) (g ^ r) *
            poly (constraint_root_cofactor roots) (g ^ r)
        else 0)"

definition common_denominator_composition_root_residual
  :: "'f poly \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f"
  where
    "common_denominator_composition_root_residual f as r =
      sum_list
        (map (common_denominator_constraint_root_residual f r) (zip as spec))"

definition random_combination_common_denominator_hides_violations
  :: "'f poly \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "random_combination_common_denominator_hides_violations f as \<longleftrightarrow>
      violated_constraints f \<noteq> {} \<and>
      (\<forall>entry \<in> violated_constraints f.
        case entry of (c, roots, d) \<Rightarrow>
          (\<forall>r \<in> set roots.
            common_denominator_composition_root_residual f as r = 0))"

definition common_denominator_degree_bounds :: "'f poly \<Rightarrow> 'f list \<Rightarrow> bool"
  where
    "common_denominator_degree_bounds f as \<longleftrightarrow>
      degree (common_denominator_numerator f as) < query_sample_space_size \<and>
      (\<forall>q. degree q \<le> maxDegree \<longrightarrow>
        degree (common_denominator_poly * q) < query_sample_space_size)"

definition query_agreement_margin :: bool
  where
    "query_agreement_margin \<longleftrightarrow>
      query_agreement_bound < query_sample_space_size"

definition spec_degree_wellformed :: bool
  where
    "spec_degree_wellformed \<longleftrightarrow> query_agreement_margin"

lemma spec_degree_wellformedI:
  assumes "query_agreement_margin"
  shows "spec_degree_wellformed"
  using assms unfolding spec_degree_wellformed_def by simp

lemma spec_degree_wellformed_query_agreement_margin:
  assumes "spec_degree_wellformed"
  shows "query_agreement_margin"
  using assms unfolding spec_degree_wellformed_def by simp

lemma spec_degree_wellformed_constraint_degree:
  assumes wf: "spec_degree_wellformed"
    and deg_f: "degree f < clength"
    and spec_entry: "(c, roots, d) \<in> set spec"
  shows "degree (c (trace_powers_of f)) \<le> d * (clength - 1)"
  by (rule constraint_degree_wellformed[OF deg_f spec_entry])

lemma query_agreement_marginD:
  assumes "query_agreement_margin"
  shows "query_agreement_bound < query_sample_space_size"
  using assms unfolding query_agreement_margin_def by simp

lemma spec_degree_wellformed_query_margin:
  assumes "spec_degree_wellformed"
  shows "query_agreement_bound < query_sample_space_size"
  by (rule query_agreement_marginD
      [OF spec_degree_wellformed_query_agreement_margin[OF assms]])

lemma all_constraint_roots_length_le_sum_roots:
  "length all_constraint_roots \<le>
    sum_list (map (\<lambda>(_, roots, _). length roots) spec)"
proof -
  have "length all_constraint_roots \<le>
      length (List.concat (map (\<lambda>(c, roots, d). g_map roots) spec))"
    unfolding all_constraint_roots_def
    by (rule length_remdups_leq)
  also have "... =
      sum_list (map (\<lambda>(_, roots, _). length roots) spec)"
    unfolding g_map_def
    by (induction spec) auto
  finally show ?thesis .
qed

lemma spec_degree_wellformed_from_spec_query_margin:
  "spec_degree_wellformed"
proof -
  have margin: "query_agreement_bound < query_sample_space_size"
    using spec_query_margin all_constraint_roots_length_le_sum_roots
    unfolding query_agreement_bound_def query_sample_space_size_def
      maxDegree_def
    by linarith
  then show ?thesis
    unfolding spec_degree_wellformed_def query_agreement_margin_def by simp
qed

lemma exists_valid_traceI:
  assumes "degree f < clength"
    and "\<And>c roots d. (c, roots, d) \<in> set spec \<Longrightarrow>
      trace_satisfies_constraint f c roots"
  shows "exists_valid_trace"
  using assms unfolding exists_valid_trace_def by auto

lemma trace_table_valid_imp_exists_valid_trace:
  assumes "trace_table_valid ys"
  shows "exists_valid_trace"
  using assms unfolding trace_table_valid_def
  by (auto intro!: exists_valid_traceI)

lemma false_statement_violated_constraints:
  assumes false_statement: "\<not> exists_valid_trace"
    and low_degree: "degree f < clength"
  shows "violated_constraints f \<noteq> {}"
proof
  assume empty: "violated_constraints f = {}"
  have "\<And>c roots d. (c, roots, d) \<in> set spec \<Longrightarrow>
      trace_satisfies_constraint f c roots"
    using empty unfolding violated_constraints_def by force
  then have "exists_valid_trace"
    using low_degree unfolding exists_valid_trace_def by auto
  then show False
    using false_statement by contradiction
qed

lemma constraint_remainder_bad_iff_not_trace_satisfies:
  "constraint_remainder_bad f (c, roots, d) \<longleftrightarrow>
    \<not> trace_satisfies_constraint f c roots"
  unfolding constraint_remainder_bad_def trace_satisfies_constraint_def
  by auto

lemma violated_constraints_has_remainder_bad:
  assumes "violated_constraints f \<noteq> {}"
  shows "\<exists>entry \<in> violated_constraints f. constraint_remainder_bad f entry"
  using assms
  unfolding violated_constraints_def
  by (auto simp: constraint_remainder_bad_iff_not_trace_satisfies)

lemma random_combination_hides_violations_has_remainder_bad:
  assumes "random_combination_hides_violations f as"
  shows "\<exists>entry \<in> violated_constraints f. constraint_remainder_bad f entry"
  using assms violated_constraints_has_remainder_bad
  unfolding random_combination_hides_violations_def
  by blast

lemma linear_equation_solution_unique:
  fixes c b x y :: "'f"
  assumes c_nonzero: "c \<noteq> 0"
    and x_sol: "c * x + b = 0"
    and y_sol: "c * y + b = 0"
  shows "x = y"
proof -
  have x_eq: "c * x = - b"
  proof -
    have "c * x + b + (- b) = 0 + (- b)"
      using x_sol by simp
    then show ?thesis
      by simp
  qed
  have y_eq: "c * y = - b"
  proof -
    have "c * y + b + (- b) = 0 + (- b)"
      using y_sol by simp
    then show ?thesis
      by simp
  qed
  have "c * (x - y) = 0"
    using x_eq y_eq by (simp add: algebra_simps)
  then have "x - y = 0"
    using c_nonzero by simp
  then show ?thesis
    by simp
qed

lemma composition_root_residual_sum_nth:
  assumes len: "length as = length spec"
  shows
    "composition_root_residual f as r =
      (\<Sum>i \<in> {0..<length spec}.
        constraint_root_residual f r (as ! i, spec ! i))"
proof -
  have "composition_root_residual f as r =
      sum_list (map (constraint_root_residual f r) (zip as spec))"
    by (simp add: composition_root_residual_def)
  also have "... =
      (\<Sum>i \<in> {0..<length (zip as spec)}.
        map (constraint_root_residual f r) (zip as spec) ! i)"
    by (simp add: sum_list_sum_nth)
  also have "... =
      (\<Sum>i \<in> {0..<length spec}.
        constraint_root_residual f r (as ! i, spec ! i))"
    using len by (intro sum.cong) auto
  finally show ?thesis .
qed

lemma composition_root_residual_split_index:
  assumes len: "length as = length spec"
    and i_bound: "i < length spec"
  shows
    "composition_root_residual f as r =
      constraint_root_residual f r (as ! i, spec ! i) +
      (\<Sum>j \<in> {0..<length spec} - {i}.
        constraint_root_residual f r (as ! j, spec ! j))"
proof -
  let ?F = "\<lambda>j. constraint_root_residual f r (as ! j, spec ! j)"
  have "composition_root_residual f as r = (\<Sum>j \<in> {0..<length spec}. ?F j)"
    by (rule composition_root_residual_sum_nth[OF len])
  also have "... = ?F i + (\<Sum>j \<in> {0..<length spec} - {i}. ?F j)"
    using i_bound by (simp add: sum.remove)
  finally show ?thesis .
qed

lemma composition_root_residual_zero_unique_nth:
  fixes as bs :: "'f list"
  assumes len_as: "length as = length spec"
    and len_bs: "length bs = length spec"
    and i_bound: "i < length spec"
    and spec_i: "spec ! i = (c, roots, d)"
    and r_in: "r \<in> set roots"
    and nonzero:
      "poly (c (trace_powers_of f)) (g ^ r) \<noteq> 0"
    and outside:
      "\<And>j. j < length spec \<Longrightarrow> j \<noteq> i \<Longrightarrow> as ! j = bs ! j"
    and zero_as: "composition_root_residual f as r = 0"
    and zero_bs: "composition_root_residual f bs r = 0"
  shows "as ! i = bs ! i"
proof -
  let ?C = "poly (c (trace_powers_of f)) (g ^ r)"
  let ?B =
    "(\<Sum>j \<in> {0..<length spec} - {i}.
      constraint_root_residual f r (as ! j, spec ! j))"
  have B_eq:
    "(\<Sum>j \<in> {0..<length spec} - {i}.
      constraint_root_residual f r (bs ! j, spec ! j)) = ?B"
    by (intro sum.cong) (use outside in auto)
  have as_eq:
    "composition_root_residual f as r = ?C * (as ! i) + ?B"
    using composition_root_residual_split_index[OF len_as i_bound]
      spec_i r_in
    unfolding constraint_root_residual_def
    by (simp add: algebra_simps)
  have bs_eq:
    "composition_root_residual f bs r = ?C * (bs ! i) + ?B"
    using composition_root_residual_split_index[OF len_bs i_bound]
      spec_i r_in B_eq
    unfolding constraint_root_residual_def
    by (simp add: algebra_simps)
  show ?thesis
  proof (rule linear_equation_solution_unique[OF nonzero])
    show "?C * (as ! i) + ?B = 0"
      using as_eq zero_as by simp
    show "?C * (bs ! i) + ?B = 0"
      using bs_eq zero_bs by simp
  qed
qed

lemma random_combination_hides_violations_unique_nth:
  fixes as bs :: "'f list"
  assumes len_as: "length as = length spec"
    and len_bs: "length bs = length spec"
    and i_bound: "i < length spec"
    and spec_i: "spec ! i = (c, roots, d)"
    and violated: "(c, roots, d) \<in> violated_constraints f"
    and r_in: "r \<in> set roots"
    and nonzero:
      "poly (c (trace_powers_of f)) (g ^ r) \<noteq> 0"
    and outside:
      "\<And>j. j < length spec \<Longrightarrow> j \<noteq> i \<Longrightarrow> as ! j = bs ! j"
    and hides_as: "random_combination_hides_violations f as"
    and hides_bs: "random_combination_hides_violations f bs"
  shows "as ! i = bs ! i"
proof -
  have zero_as: "composition_root_residual f as r = 0"
    using hides_as violated r_in
    unfolding random_combination_hides_violations_def by auto
  have zero_bs: "composition_root_residual f bs r = 0"
    using hides_bs violated r_in
    unfolding random_combination_hides_violations_def by auto
  show ?thesis
    by (rule composition_root_residual_zero_unique_nth
        [OF len_as len_bs i_bound spec_i r_in nonzero outside zero_as zero_bs])
qed

lemma bad_query_indices_subset:
  "bad_query_indices trace_table composition_table as \<subseteq> {0..<clength * scale}"
  unfolding bad_query_indices_def query_sample_space_def query_sample_space_size_def
  by auto

lemma index_less_domain:
  "index x < clength * scale"
proof -
  have max_lt: "Max (set [0..<powers]) < clength"
  proof -
    have "Max (set [0..<powers]) = powers - 1"
      using powers_pos by (intro Max_eqI) auto
    also have "... < clength"
      using powers_pos powers_le_clength by simp
    finally show ?thesis .
  qed
  have mod_pos: "0 < clength * scale - Max (set [0..<powers]) * scale"
    using max_lt scale_pos
    by (simp add: diff_mult_distrib2)
  have "index x < clength * scale - Max (set [0..<powers]) * scale"
    unfolding index_def using mod_pos by simp
  moreover have "clength * scale - Max (set [0..<powers]) * scale \<le> clength * scale"
    by simp
  ultimately show ?thesis
    by linarith
qed

lemma query_sample_space_size_pos:
  "0 < query_sample_space_size"
proof -
  have max_lt: "Max (set [0..<powers]) < clength"
  proof -
    have "Max (set [0..<powers]) = powers - 1"
      using powers_pos by (intro Max_eqI) auto
    also have "... < clength"
      using powers_pos powers_le_clength by simp
    finally show ?thesis .
  qed
  show ?thesis
    unfolding query_sample_space_size_def
    using max_lt scale_pos by (simp add: diff_mult_distrib2)
qed

lemma index_less_query_sample_space:
  "index x < query_sample_space_size"
  unfolding index_def query_sample_space_size_def
  using query_sample_space_size_pos[unfolded query_sample_space_size_def] by simp

lemma query_sample_space_size_le_domain:
  "query_sample_space_size \<le> clength * scale"
  unfolding query_sample_space_size_def by simp

lemma query_sample_spaceD:
  assumes "idx \<in> query_sample_space"
  shows "idx < query_sample_space_size"
  using assms unfolding query_sample_space_def by simp

lemma finite_query_sample_space[simp]:
  "finite query_sample_space"
  unfolding query_sample_space_def by simp

lemma card_query_sample_space[simp]:
  "card query_sample_space = query_sample_space_size"
  unfolding query_sample_space_def by simp

lemma query_error_bound_query_sample_space:
  "query_error_bound =
    nnreal query_agreement_bound / nnreal (card query_sample_space)"
  unfolding query_error_bound_def by simp

lemma query_sample_space_less_domain:
  assumes "idx \<in> query_sample_space"
  shows "idx < clength * scale"
  using query_sample_spaceD[OF assms] query_sample_space_size_le_domain
  by linarith

lemma query_sample_space_powers_scaled_bound:
  assumes idx_in: "idx \<in> query_sample_space"
    and i_in: "i \<in> set (powers_scaled idx)"
  shows "i < clength * scale"
proof -
  obtain k where k_bound: "k < powers" and i_eq: "i = idx + k * scale"
    using i_in unfolding powers_scaled_def by auto
  have max_eq: "Max (set [0..<powers]) = powers - 1"
    using powers_pos by (intro Max_eqI) auto
  have k_le_max: "k \<le> Max (set [0..<powers])"
    using k_bound unfolding max_eq by simp
  have idx_bound:
    "idx < clength * scale - Max (set [0..<powers]) * scale"
    using query_sample_spaceD[OF idx_in]
    unfolding query_sample_space_size_def .
  have "idx + k * scale \<le> idx + Max (set [0..<powers]) * scale"
    using k_le_max by simp
  also have "... < clength * scale"
    using idx_bound by simp
  finally show ?thesis
    unfolding i_eq .
qed

definition query_sample_domain :: "'f list"
  where "query_sample_domain = map (\<lambda>idx. h ^ idx * shift) [0..<query_sample_space_size]"

lemma eval_domain_length:
  "length eval_domain = clength * scale"
  unfolding eval_domain_def H_def by simp

lemma eval_domain_nth:
  assumes "i < clength * scale"
  shows "eval_domain ! i = h ^ i * shift"
  using assms
  unfolding eval_domain_def H_def
  by (simp add: mult.commute)

lemma h_nonzero:
  "h \<noteq> 0"
  unfolding h_def using omega_nonzero_derived by simp

lemma h_power_inj_on_eval_domain:
  assumes i_bound: "i < clength * scale"
    and j_bound: "j < clength * scale"
    and eq: "h ^ i = h ^ j"
  shows "i = j"
proof (rule ccontr)
  let ?N = "clength * scale"
  assume neq: "i \<noteq> j"
  consider "i < j" | "j < i"
    using neq by linarith
  then show False
  proof cases
    case 1
    have diff_pos: "0 < j - i"
      using 1 by simp
    have diff_lt: "j - i < ?N"
      using j_bound by simp
    have hi_nonzero: "h ^ i \<noteq> 0"
      using h_nonzero by simp
    have j_decomp: "j = i + (j - i)"
      using 1 by simp
    have mult_eq: "h ^ j = h ^ i * h ^ (j - i)"
      by (subst j_decomp) (simp add: power_add)
    have cancel_eq: "h ^ i * 1 = h ^ i * h ^ (j - i)"
      using eq mult_eq by simp
    have "h ^ i = 0 \<or> 1 = h ^ (j - i)"
      using cancel_eq by (simp only: mult_cancel_left)
    then have "h ^ (j - i) = 1"
      using hi_nonzero by auto
    then show False
      using h_exact_order diff_pos diff_lt unfolding exact_order_def by blast
  next
    case 2
    have diff_pos: "0 < i - j"
      using 2 by simp
    have diff_lt: "i - j < ?N"
      using i_bound by simp
    have hj_nonzero: "h ^ j \<noteq> 0"
      using h_nonzero by simp
    have i_decomp: "i = j + (i - j)"
      using 2 by simp
    have mult_eq: "h ^ i = h ^ j * h ^ (i - j)"
      by (subst i_decomp) (simp add: power_add)
    have cancel_eq: "h ^ j * 1 = h ^ j * h ^ (i - j)"
      using eq mult_eq by simp
    have "h ^ j = 0 \<or> 1 = h ^ (i - j)"
      using cancel_eq by (simp only: mult_cancel_left)
    then have "h ^ (i - j) = 1"
      using hj_nonzero by auto
    then show False
      using h_exact_order diff_pos diff_lt unfolding exact_order_def by blast
  qed
qed

lemma H_distinct:
  "distinct H"
proof -
  have inj: "inj_on ((^) h) (set [0..<scale * clength])"
  proof (intro inj_onI)
    fix x y
    assume x_in: "x \<in> set [0..<scale * clength]"
      and y_in: "y \<in> set [0..<scale * clength]"
      and eq: "h ^ x = h ^ y"
    have x_bound: "x < clength * scale"
      using x_in by (simp add: mult.commute)
    have y_bound: "y < clength * scale"
      using y_in by (simp add: mult.commute)
    show "x = y"
      by (rule h_power_inj_on_eval_domain[OF x_bound y_bound eq])
  qed
  show ?thesis
    unfolding H_def using inj by (simp add: distinct_map)
qed

lemma eval_domain_distinct:
  "distinct eval_domain"
proof -
  have inj: "inj_on ((*) shift) (set H)"
    using shift_nonzero by (auto intro!: inj_onI)
  show ?thesis
    unfolding eval_domain_def
    using H_distinct inj by (simp add: distinct_map)
qed

lemma card_set_eval_domain:
  "card (set eval_domain) = clength * scale"
  using eval_domain_distinct eval_domain_length
  by (simp add: distinct_card)

lemma poly_eq_on_eval_domainI:
  assumes deg_p: "degree p < clength * scale"
    and deg_q: "degree q < clength * scale"
    and agree:
      "\<And>idx. idx < clength * scale \<Longrightarrow>
        poly p (h ^ idx * shift) = poly q (h ^ idx * shift)"
  shows "p = q"
proof (rule poly_eqI_degree[where A = "set eval_domain"])
  fix x
  assume x_in: "x \<in> set eval_domain"
  then obtain idx where idx_bound: "idx < clength * scale"
    and x_eq: "x = h ^ idx * shift"
    unfolding eval_domain_def H_def
    by (auto simp: mult.commute)
  show "poly p x = poly q x"
    using agree[OF idx_bound] x_eq by simp
next
  show "degree p < card (set eval_domain)"
    using deg_p card_set_eval_domain by simp
next
  show "degree q < card (set eval_domain)"
    using deg_q card_set_eval_domain by simp
qed

lemma query_sample_domain_distinct:
  "distinct query_sample_domain"
proof -
  have inj: "inj_on (\<lambda>idx. h ^ idx * shift) (set [0..<query_sample_space_size])"
  proof (intro inj_onI)
    fix i j
    assume i_in: "i \<in> set [0..<query_sample_space_size]"
      and j_in: "j \<in> set [0..<query_sample_space_size]"
      and eq: "h ^ i * shift = h ^ j * shift"
    have i_bound: "i < clength * scale"
      using i_in query_sample_space_size_le_domain by simp
    have j_bound: "j < clength * scale"
      using j_in query_sample_space_size_le_domain by simp
    have "h ^ i = h ^ j"
      using eq shift_nonzero by simp
    then show "i = j"
      by (rule h_power_inj_on_eval_domain[OF i_bound j_bound])
  qed
  show ?thesis
    unfolding query_sample_domain_def using inj by (simp add: distinct_map)
qed

lemma card_set_query_sample_domain:
  "card (set query_sample_domain) = query_sample_space_size"
proof -
  have "card (set query_sample_domain) = length query_sample_domain"
    using query_sample_domain_distinct by (simp add: distinct_card)
  also have "... = query_sample_space_size"
    unfolding query_sample_domain_def by simp
  finally show ?thesis .
qed

lemma poly_eq_on_query_sample_domainI:
  assumes deg_p: "degree p < query_sample_space_size"
    and deg_q: "degree q < query_sample_space_size"
    and agree:
      "\<And>idx. idx \<in> query_sample_space \<Longrightarrow>
        poly p (h ^ idx * shift) = poly q (h ^ idx * shift)"
  shows "p = q"
proof (rule poly_eqI_degree[where A = "set query_sample_domain"])
  fix x
  assume x_in: "x \<in> set query_sample_domain"
  then obtain idx where idx_bound: "idx < query_sample_space_size"
    and x_eq: "x = h ^ idx * shift"
    unfolding query_sample_domain_def by auto
  have idx_in: "idx \<in> query_sample_space"
    using idx_bound unfolding query_sample_space_def by simp
  show "poly p x = poly q x"
    using agree[OF idx_in] x_eq by simp
next
  show "degree p < card (set query_sample_domain)"
    using deg_p card_set_query_sample_domain by simp
next
  show "degree q < card (set query_sample_domain)"
    using deg_q card_set_query_sample_domain by simp
qed

lemma prod_fold_acc:
  fixes roots :: "'f list"
  shows "fold (\<lambda>s acc. (XP 1 - CP s) * acc) roots acc =
    fold (\<lambda>s acc. (XP 1 - CP s) * acc) roots (1 :: 'f poly) * acc"
proof (induction roots arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons r roots)
  let ?F = "\<lambda>s acc. (XP 1 - CP s) * acc"
  let ?fac = "XP 1 - CP r"
  have lhs:
    "fold ?F (r # roots) acc =
      fold ?F roots 1 * (?fac * acc)"
    using Cons.IH[of "?fac * acc"] by simp
  have "fold ?F (r # roots) acc =
      (fold ?F roots 1 * ?fac) * acc"
    using lhs by (simp only: mult.assoc)
  also have "... = fold ?F roots ?fac * acc"
    using Cons.IH[of ?fac, symmetric] by simp
  also have "... = fold ?F (r # roots) 1 * acc"
    by simp
  finally show ?case .
qed

lemma prod_Cons:
  fixes r :: 'f and roots :: "'f list"
  shows "prod (r # roots) = (XP 1 - CP r) * (prod roots :: 'f poly)"
proof -
  let ?F = "\<lambda>s acc. (XP 1 - CP s) * acc"
  have "prod (r # roots) = fold ?F roots ((XP 1 - CP r) * 1)"
    unfolding prod_def by simp
  also have "... = fold ?F roots 1 * ((XP 1 - CP r) * 1)"
    by (rule prod_fold_acc)
  also have "... = (prod roots :: 'f poly) * (XP 1 - CP r)"
    unfolding prod_def by simp
  also have "... = (XP 1 - CP r) * (prod roots :: 'f poly)"
    by (rule mult.commute)
  finally show ?thesis .
qed

lemma prod_append:
  fixes xs ys :: "'f list"
  shows "prod (xs @ ys) = (prod xs :: 'f poly) * prod ys"
proof (induction xs)
  case Nil
  then show ?case
    unfolding prod_def by simp
next
  case (Cons x xs)
  then show ?case
    by (simp add: prod_Cons algebra_simps)
qed

lemma prod_alt:
  fixes roots :: "'f list"
  shows "prod roots =
    prod_list (map (\<lambda>r. XP 1 - CP r) roots :: 'f poly list)"
proof (induction roots)
  case Nil
  then show ?case
    unfolding prod_def by simp
next
  case (Cons r roots)
  then show ?case
    by (simp add: prod_Cons)
qed

lemma degree_prod_le_length:
  fixes roots :: "'f list"
  shows "degree (prod roots :: 'f poly) \<le> length roots"
proof (induction roots)
  case Nil
  then show ?case
    unfolding prod_def by simp
next
  case (Cons r roots)
  have factor: "degree (XP 1 - CP r :: 'f poly) \<le> 1"
  proof -
    have deg_x: "degree (Polynomial.monom (1::'f) 1) \<le> 1"
      by (rule degree_monom_le)
    have deg_c: "degree (Polynomial.monom r 0) \<le> 1"
    proof -
      have "degree (Polynomial.monom r 0) \<le> 0"
        by (rule degree_monom_le)
      then show ?thesis by simp
    qed
    show ?thesis
      unfolding XP_def CP_def
      by (rule degree_diff_le[OF deg_x deg_c])
  qed
  have "degree (prod (r # roots) :: 'f poly) =
      degree ((XP 1 - CP r) * (prod roots :: 'f poly))"
    by (simp add: prod_Cons)
  also have "... \<le>
      degree (XP 1 - CP r :: 'f poly) + degree (prod roots :: 'f poly)"
    by (rule degree_mult_le)
  also have "... \<le> Suc (length roots)"
    using factor Cons.IH by simp
  finally show ?case by simp
qed

lemma degree_sum_list_less:
  fixes ps :: "'f poly list"
  assumes "\<And>p. p \<in> set ps \<Longrightarrow> degree p < n"
    and "0 < n"
  shows "degree (sum_list ps) < n"
  using assms
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  have p_lt: "degree p < n"
    using Cons.prems by simp
  have ps_lt: "degree (sum_list ps) < n"
    by (rule Cons.IH) (use Cons.prems in auto)
  show ?case
    using degree_add_less[OF p_lt ps_lt] by simp
qed

lemma degree_sum_list_le:
  fixes ps :: "'f poly list"
  assumes "\<And>p. p \<in> set ps \<Longrightarrow> degree p \<le> n"
  shows "degree (sum_list ps) \<le> n"
  using assms
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  have p_le: "degree p \<le> n"
    using Cons.prems by simp
  have ps_le: "degree (sum_list ps) \<le> n"
    by (rule Cons.IH) (use Cons.prems in auto)
  show ?case
  proof -
    have "degree (p + sum_list ps) \<le> max (degree p) (degree (sum_list ps))"
      by (rule degree_add_le_max)
    also have "... \<le> n"
      using p_le ps_le by simp
    finally show ?thesis by simp
  qed
qed

lemma prod_mset_eq:
  fixes xs ys :: "'f list"
  assumes "mset xs = mset ys"
  shows "prod xs = (prod ys :: 'f poly)"
  using assms
  by (simp add: prod_alt flip: prod_mset_prod_list)

lemma prod_eval_nonzero:
  fixes roots :: "'f list"
  assumes "x \<notin> set roots"
  shows "poly (prod roots :: 'f poly) x \<noteq> 0"
  using assms
proof (induction roots)
  case Nil
  then show ?case
    unfolding prod_def by simp
next
  case (Cons r roots)
  have x_ne: "x \<noteq> r"
    using Cons.prems by simp
  have x_notin: "x \<notin> set roots"
    using Cons.prems by simp
  have "poly (prod (r # roots) :: 'f poly) x =
      (x - r) * poly (prod roots :: 'f poly) x"
    unfolding prod_Cons XP_def CP_def
    by (simp add: poly_monom)
  then show ?case
    using x_ne Cons.IH[OF x_notin] by simp
qed

lemma prod_eval_zero:
  fixes roots :: "'f list"
  assumes "x \<in> set roots"
  shows "poly (prod roots :: 'f poly) x = 0"
  using assms
proof (induction roots)
  case Nil
  then show ?case by simp
next
  case (Cons r roots)
  show ?case
  proof (cases "x = r")
    case True
    then show ?thesis
      unfolding prod_Cons XP_def CP_def
      by (simp add: poly_monom)
  next
    case False
    then have "x \<in> set roots"
      using Cons.prems by simp
    then show ?thesis
      using Cons.IH
      unfolding prod_Cons XP_def CP_def
      by (simp add: poly_monom)
  qed
qed

lemma query_denominator_nonzero:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
    and idx_bound: "idx < clength * scale"
  shows "poly (prod (g_map roots)) (h ^ idx * shift) \<noteq> 0"
proof -
  have "h ^ idx * shift \<notin> set (g_map roots)"
    by (rule query_domain_disjoint[OF spec_entry idx_bound])
  then show ?thesis
    by (rule prod_eval_nonzero)
qed

lemma common_denominator_nonzero_on_eval_domain:
  assumes idx_bound: "idx < clength * scale"
  shows "poly common_denominator_poly (h ^ idx * shift) \<noteq> 0"
proof -
  have notin: "h ^ idx * shift \<notin> set all_constraint_roots"
  proof
    assume in_roots: "h ^ idx * shift \<in> set all_constraint_roots"
    then obtain c roots d where spec_entry: "(c, roots, d) \<in> set spec"
      and in_g_map: "h ^ idx * shift \<in> set (g_map roots)"
      unfolding all_constraint_roots_def by (auto split: prod.splits)
    have "h ^ idx * shift \<notin> set (g_map roots)"
      by (rule query_domain_disjoint[OF spec_entry idx_bound])
    then show False
      using in_g_map by simp
  qed
  then show ?thesis
    unfolding common_denominator_poly_def
    by (rule prod_eval_nonzero)
qed

lemma g_power_in_g_map:
  assumes "r \<in> set roots"
  shows "g ^ r \<in> set (g_map roots)"
  using assms unfolding g_map_def by simp

lemma all_constraint_roots_distinct[simp]:
  "distinct all_constraint_roots"
  unfolding all_constraint_roots_def by simp

lemma g_map_subset_all_constraint_roots:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
  shows "set (g_map roots) \<subseteq> set all_constraint_roots"
  using spec_entry
  unfolding all_constraint_roots_def
  by (auto split: prod.splits)

lemma common_denominator_factor:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
  shows
    "common_denominator_poly =
      prod (g_map roots) * constraint_root_cofactor roots"
proof -
  let ?rest = "filter (\<lambda>x. x \<notin> set (g_map roots)) all_constraint_roots"
  have subset: "set (g_map roots) \<subseteq> set all_constraint_roots"
    by (rule g_map_subset_all_constraint_roots[OF spec_entry])
  have distinct_roots: "distinct (g_map roots)"
    by (rule g_map_distinct[OF spec_entry])
  have distinct_all: "distinct all_constraint_roots"
    by simp
  have distinct_split: "distinct (g_map roots @ ?rest)"
    using distinct_roots distinct_all subset by auto
  have set_split: "set (g_map roots @ ?rest) = set all_constraint_roots"
    using subset by auto
  have mset_eq:
    "mset all_constraint_roots = mset (g_map roots @ ?rest)"
    using distinct_all distinct_split set_split
    by (metis set_eq_iff_mset_eq_distinct)
  have "common_denominator_poly = prod all_constraint_roots"
    unfolding common_denominator_poly_def by simp
  also have "... = prod (g_map roots @ ?rest)"
    by (rule prod_mset_eq[OF mset_eq])
  also have "... = prod (g_map roots) * prod ?rest"
    by (rule prod_append)
  finally show ?thesis
    unfolding constraint_root_cofactor_def .
qed

lemma declared_quotient_degree_le_maxDegree:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
  shows "d * (clength - 1) - length roots \<le> maxDegree"
proof -
  have deg_set:
    "{d * (clength - 1) - length rs | a rs d. (a, rs, d) \<in> set spec} =
      (\<lambda>(a, rs, d). d * (clength - 1) - length rs) ` set spec"
    by force
  have finite_degrees: "finite (degrees clength spec)"
    unfolding degrees_def deg_set by simp
  have entry_degree:
    "d * (clength - 1) - length roots \<in> degrees clength spec"
    using spec_entry unfolding degrees_def by blast
  show ?thesis
    unfolding maxDegree_def
    by (rule Max_ge[OF finite_degrees entry_degree])
qed

lemma constraint_roots_length_le_all_constraint_roots:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
  shows "length roots \<le> length all_constraint_roots"
proof -
  have subset: "set (g_map roots) \<subseteq> set all_constraint_roots"
    by (rule g_map_subset_all_constraint_roots[OF spec_entry])
  have distinct_roots: "distinct (g_map roots)"
    by (rule g_map_distinct[OF spec_entry])
  have card_le:
    "card (set (g_map roots)) \<le> card (set all_constraint_roots)"
    by (rule card_mono) (use subset in auto)
  have "length roots = length (g_map roots)"
    unfolding g_map_def by simp
  also have "... = card (set (g_map roots))"
    using distinct_roots by (simp add: distinct_card)
  also have "... \<le> card (set all_constraint_roots)"
    by (rule card_le)
  also have "... = length all_constraint_roots"
    by (simp add: distinct_card)
  finally show ?thesis .
qed

lemma constraint_root_cofactor_degree_le:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
  shows
    "degree (constraint_root_cofactor roots) \<le>
      length all_constraint_roots - length roots"
proof -
  let ?rest = "filter (\<lambda>x. x \<notin> set (g_map roots)) all_constraint_roots"
  have subset: "set (g_map roots) \<subseteq> set all_constraint_roots"
    by (rule g_map_subset_all_constraint_roots[OF spec_entry])
  have distinct_roots: "distinct (g_map roots)"
    by (rule g_map_distinct[OF spec_entry])
  have distinct_rest: "distinct ?rest"
    by simp
  have rest_set: "set ?rest = set all_constraint_roots - set (g_map roots)"
    by auto
  have rest_len:
    "length ?rest = length all_constraint_roots - length roots"
  proof -
    have "length ?rest = card (set ?rest)"
      using distinct_card[OF distinct_rest] by simp
    also have "... = card (set all_constraint_roots - set (g_map roots))"
      using rest_set by simp
    also have "... =
        card (set all_constraint_roots) - card (set (g_map roots))"
      by (rule card_Diff_subset) (use subset in auto)
    also have "... = length all_constraint_roots - length roots"
    proof -
      have "card (set (g_map roots)) = length (g_map roots)"
        using distinct_roots by (simp add: distinct_card)
      also have "... = length roots"
        unfolding g_map_def by simp
      finally show ?thesis
        by (simp add: distinct_card)
    qed
    finally show ?thesis .
  qed
  have "degree (constraint_root_cofactor roots) \<le> length ?rest"
    unfolding constraint_root_cofactor_def by (rule degree_prod_le_length)
  then show ?thesis
    unfolding rest_len .
qed

lemma common_denominator_poly_degree_le:
  "degree common_denominator_poly \<le> length all_constraint_roots"
  unfolding common_denominator_poly_def
  by (rule degree_prod_le_length)

lemma common_denominator_numerator_term_degree_lt:
  assumes wf: "spec_degree_wellformed"
    and deg_f: "degree f < clength"
    and spec_entry: "(c, roots, d) \<in> set spec"
  shows
    "degree (common_denominator_numerator_term f (a, (c, roots, d))) <
      query_sample_space_size"
proof -
  let ?dc = "d * (clength - 1)"
  let ?all = "length all_constraint_roots"
  have deg_c:
    "degree (c (trace_powers_of f)) \<le> ?dc"
    by (rule spec_degree_wellformed_constraint_degree
        [OF wf deg_f spec_entry])
  have deg_cofactor:
    "degree (constraint_root_cofactor roots) \<le> ?all - length roots"
    by (rule constraint_root_cofactor_degree_le[OF spec_entry])
  have deg_cp: "degree (CP a :: 'f poly) \<le> 0"
    unfolding CP_def by (rule degree_monom_le)
  have term_le:
    "degree (CP a * c (trace_powers_of f) *
        constraint_root_cofactor roots) \<le>
      ?dc + (?all - length roots)"
  proof -
    have "degree (CP a * c (trace_powers_of f) *
        constraint_root_cofactor roots) \<le>
      degree (CP a * c (trace_powers_of f)) +
        degree (constraint_root_cofactor roots)"
      by (rule degree_mult_le)
    also have "... \<le>
      degree (CP a :: 'f poly) + degree (c (trace_powers_of f)) +
        degree (constraint_root_cofactor roots)"
      using degree_mult_le[of "CP a :: 'f poly" "c (trace_powers_of f)"]
      by linarith
    also have "... \<le> ?dc + (?all - length roots)"
      using deg_cp deg_c deg_cofactor by linarith
    finally show ?thesis .
  qed
  have roots_le_all: "length roots \<le> ?all"
    by (rule constraint_roots_length_le_all_constraint_roots[OF spec_entry])
  have quotient_le:
    "?dc - length roots \<le> maxDegree"
    by (rule declared_quotient_degree_le_maxDegree[OF spec_entry])
  have arith:
    "?dc + (?all - length roots) \<le> maxDegree + ?all"
    using roots_le_all quotient_le by linarith
  have margin: "maxDegree + ?all < query_sample_space_size"
    using spec_degree_wellformed_query_margin[OF wf]
    unfolding query_agreement_bound_def by simp
  show ?thesis
    using term_le arith margin
    unfolding common_denominator_numerator_term_def
    by simp
qed

lemma common_denominator_numerator_degree_lt:
  assumes wf: "spec_degree_wellformed"
    and deg_f: "degree f < clength"
  shows "degree (common_denominator_numerator f as) < query_sample_space_size"
proof -
  have term_lt:
    "\<And>p. p \<in>
      set (map (common_denominator_numerator_term f) (zip as spec)) \<Longrightarrow>
      degree p < query_sample_space_size"
  proof -
    fix p
    assume p_in:
      "p \<in> set (map (common_denominator_numerator_term f) (zip as spec))"
    then obtain z where
      z_in: "z \<in> set (zip as spec)"
      and p_eq: "p = common_denominator_numerator_term f z"
      by auto
    obtain a entry where z_eq: "z = (a, entry)"
      by (cases z) auto
    obtain c roots d where entry_eq: "entry = (c, roots, d)"
      by (cases entry) auto
    have spec_entry: "(c, roots, d) \<in> set spec"
      using z_in unfolding z_eq entry_eq by (auto simp: set_zip)
    show "degree p < query_sample_space_size"
      unfolding p_eq z_eq entry_eq
      by (rule common_denominator_numerator_term_degree_lt
          [OF wf deg_f spec_entry])
  qed
  show ?thesis
    unfolding common_denominator_numerator_def
    by (rule degree_sum_list_less[OF term_lt query_sample_space_size_pos])
qed

lemma common_denominator_product_degree_lt:
  assumes wf: "spec_degree_wellformed"
    and deg_q: "degree q \<le> maxDegree"
  shows "degree (common_denominator_poly * q) < query_sample_space_size"
proof -
  have "degree (common_denominator_poly * q) \<le>
      degree common_denominator_poly + degree q"
    by (rule degree_mult_le)
  also have "... \<le> length all_constraint_roots + maxDegree"
    using common_denominator_poly_degree_le deg_q by linarith
  also have "... = maxDegree + length all_constraint_roots"
    by simp
  also have "... < query_sample_space_size"
    using spec_degree_wellformed_query_margin[OF wf]
    unfolding query_agreement_bound_def by simp
  finally show ?thesis .
qed

lemma common_denominator_numerator_term_degree_le_bound:
  assumes deg_f: "degree f < clength"
    and spec_entry: "(c, roots, d) \<in> set spec"
  shows
    "degree (common_denominator_numerator_term f (a, (c, roots, d))) \<le>
      query_agreement_bound"
proof -
  let ?dc = "d * (clength - 1)"
  let ?all = "length all_constraint_roots"
  have deg_c:
    "degree (c (trace_powers_of f)) \<le> ?dc"
    by (rule constraint_degree_wellformed[OF deg_f spec_entry])
  have deg_cofactor:
    "degree (constraint_root_cofactor roots) \<le> ?all - length roots"
    by (rule constraint_root_cofactor_degree_le[OF spec_entry])
  have deg_cp: "degree (CP a :: 'f poly) \<le> 0"
    unfolding CP_def by (rule degree_monom_le)
  have term_le:
    "degree (CP a * c (trace_powers_of f) *
        constraint_root_cofactor roots) \<le>
      ?dc + (?all - length roots)"
  proof -
    have "degree (CP a * c (trace_powers_of f) *
        constraint_root_cofactor roots) \<le>
      degree (CP a * c (trace_powers_of f)) +
        degree (constraint_root_cofactor roots)"
      by (rule degree_mult_le)
    also have "... \<le>
      degree (CP a :: 'f poly) + degree (c (trace_powers_of f)) +
        degree (constraint_root_cofactor roots)"
      using degree_mult_le[of "CP a :: 'f poly" "c (trace_powers_of f)"]
      by linarith
    also have "... \<le> ?dc + (?all - length roots)"
      using deg_cp deg_c deg_cofactor by linarith
    finally show ?thesis .
  qed
  have roots_le_all: "length roots \<le> ?all"
    by (rule constraint_roots_length_le_all_constraint_roots[OF spec_entry])
  have quotient_le:
    "?dc - length roots \<le> maxDegree"
    by (rule declared_quotient_degree_le_maxDegree[OF spec_entry])
  have "?dc + (?all - length roots) \<le> maxDegree + ?all"
    using roots_le_all quotient_le by linarith
  then show ?thesis
    using term_le unfolding common_denominator_numerator_term_def
      query_agreement_bound_def
    by simp
qed

lemma common_denominator_numerator_degree_le_bound:
  assumes deg_f: "degree f < clength"
  shows "degree (common_denominator_numerator f as) \<le> query_agreement_bound"
proof -
  have term_le:
    "\<And>p. p \<in>
      set (map (common_denominator_numerator_term f) (zip as spec)) \<Longrightarrow>
      degree p \<le> query_agreement_bound"
  proof -
    fix p
    assume p_in:
      "p \<in> set (map (common_denominator_numerator_term f) (zip as spec))"
    then obtain z where
      z_in: "z \<in> set (zip as spec)"
      and p_eq: "p = common_denominator_numerator_term f z"
      by auto
    obtain a entry where z_eq: "z = (a, entry)"
      by (cases z) auto
    obtain c roots d where entry_eq: "entry = (c, roots, d)"
      by (cases entry) auto
    have spec_entry: "(c, roots, d) \<in> set spec"
      using z_in unfolding z_eq entry_eq by (auto simp: set_zip)
    show "degree p \<le> query_agreement_bound"
      unfolding p_eq z_eq entry_eq
      by (rule common_denominator_numerator_term_degree_le_bound
          [OF deg_f spec_entry])
  qed
  show ?thesis
    unfolding common_denominator_numerator_def
    by (rule degree_sum_list_le[OF term_le])
qed

lemma common_denominator_product_degree_le_bound:
  assumes deg_q: "degree q \<le> maxDegree"
  shows "degree (common_denominator_poly * q) \<le> query_agreement_bound"
proof -
  have "degree (common_denominator_poly * q) \<le>
      degree common_denominator_poly + degree q"
    by (rule degree_mult_le)
  also have "... \<le> length all_constraint_roots + maxDegree"
    using common_denominator_poly_degree_le deg_q by linarith
  also have "... = query_agreement_bound"
    unfolding query_agreement_bound_def by simp
  finally show ?thesis .
qed

lemma common_denominator_residual_degree_le_bound:
  assumes deg_f: "degree f < clength"
    and deg_q: "degree q \<le> maxDegree"
  shows
    "degree (common_denominator_numerator f as - common_denominator_poly * q)
      \<le> query_agreement_bound"
proof -
  have num_le:
    "degree (common_denominator_numerator f as) \<le> query_agreement_bound"
    by (rule common_denominator_numerator_degree_le_bound[OF deg_f])
  have prod_le:
    "degree (common_denominator_poly * q) \<le> query_agreement_bound"
    by (rule common_denominator_product_degree_le_bound[OF deg_q])
  show ?thesis
    using degree_diff_le[OF num_le prod_le] .
qed

lemma common_denominator_degree_bounds_from_spec_degree_wellformed:
  assumes wf: "spec_degree_wellformed"
    and deg_f: "degree f < clength"
  shows "common_denominator_degree_bounds f as"
  unfolding common_denominator_degree_bounds_def
  using common_denominator_numerator_degree_lt[OF wf deg_f]
    common_denominator_product_degree_lt[OF wf]
  by simp

lemma common_denominator_vanishes_on_constraint_root:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
    and r_in: "r \<in> set roots"
  shows "poly common_denominator_poly (g ^ r) = 0"
proof -
  have factor:
    "common_denominator_poly =
      prod (g_map roots) * constraint_root_cofactor roots"
    by (rule common_denominator_factor[OF spec_entry])
  have root_in: "g ^ r \<in> set (g_map roots)"
    by (rule g_power_in_g_map[OF r_in])
  have "poly (prod (g_map roots)) (g ^ r) = 0"
    by (rule prod_eval_zero[OF root_in])
  then show ?thesis
    using factor by simp
qed

lemma g_power_notin_g_map_if_root_notin:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
    and r_bound: "r < clength"
    and r_notin: "r \<notin> set roots"
  shows "g ^ r \<notin> set (g_map roots)"
proof
  assume "g ^ r \<in> set (g_map roots)"
  then obtain r' where r'_in: "r' \<in> set roots"
    and eq: "g ^ r = g ^ r'"
    unfolding g_map_def by auto
  have r'_bound: "r' < clength"
    by (rule spec_roots_in_range[OF spec_entry r'_in])
  have "r = r'"
    by (rule g_power_inj_on_range[OF r_bound r'_bound eq])
  then show False
    using r_notin r'_in by simp
qed

lemma constraint_root_cofactor_eval_nonzero:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
    and r_in: "r \<in> set roots"
  shows "poly (constraint_root_cofactor roots) (g ^ r) \<noteq> 0"
proof -
  have root_in: "g ^ r \<in> set (g_map roots)"
    by (rule g_power_in_g_map[OF r_in])
  have "g ^ r \<notin>
      set (filter (\<lambda>x. x \<notin> set (g_map roots)) all_constraint_roots)"
    using root_in by auto
  then show ?thesis
    unfolding constraint_root_cofactor_def
    by (rule prod_eval_nonzero)
qed

lemma constraint_root_cofactor_kills_other_root:
  assumes root_spec: "(c0, roots0, d0) \<in> set spec"
    and r_in0: "r \<in> set roots0"
    and spec_entry: "(c, roots, d) \<in> set spec"
    and r_notin: "r \<notin> set roots"
  shows "poly (constraint_root_cofactor roots) (g ^ r) = 0"
proof -
  have r_bound: "r < clength"
    by (rule spec_roots_in_range[OF root_spec r_in0])
  have root_in_all: "g ^ r \<in> set all_constraint_roots"
    using g_map_subset_all_constraint_roots[OF root_spec]
      g_power_in_g_map[OF r_in0]
    by auto
  have root_notin_entry: "g ^ r \<notin> set (g_map roots)"
    by (rule g_power_notin_g_map_if_root_notin
        [OF spec_entry r_bound r_notin])
  have "g ^ r \<in>
      set (filter (\<lambda>x. x \<notin> set (g_map roots)) all_constraint_roots)"
    using root_in_all root_notin_entry by simp
  then show ?thesis
    unfolding constraint_root_cofactor_def
    by (rule prod_eval_zero)
qed

lemma common_denominator_residual_coefficient_nonzero:
  assumes spec_entry: "(c, roots, d) \<in> set spec"
    and r_in: "r \<in> set roots"
    and nonzero:
      "poly (c (trace_powers_of f)) (g ^ r) \<noteq> 0"
  shows
    "poly (c (trace_powers_of f)) (g ^ r) *
      poly (constraint_root_cofactor roots) (g ^ r) \<noteq> 0"
  using nonzero constraint_root_cofactor_eval_nonzero[OF spec_entry r_in]
  by simp

lemma common_denominator_numerator_root_eval:
  assumes len: "length as = length spec"
    and root_spec: "(c0, roots0, d0) \<in> set spec"
    and r_in0: "r \<in> set roots0"
  shows
    "poly (common_denominator_numerator f as) (g ^ r) =
      common_denominator_composition_root_residual f as r"
proof -
  have lhs:
    "poly (common_denominator_numerator f as) (g ^ r) =
      (\<Sum>i \<in> {0..<length spec}.
        poly
          (case spec ! i of (c, roots, d) \<Rightarrow>
            CP (as ! i) * c (trace_powers_of f) *
              constraint_root_cofactor roots)
          (g ^ r))"
    using len
    unfolding common_denominator_numerator_def
    by (simp add: sum_list_sum_nth poly_sum
        common_denominator_numerator_term_def split_beta' case_prod_unfold
        CP_def poly_monom algebra_simps)
  have rhs:
    "common_denominator_composition_root_residual f as r =
      (\<Sum>i \<in> {0..<length spec}.
        common_denominator_constraint_root_residual f r
          (as ! i, spec ! i))"
    using len
    unfolding common_denominator_composition_root_residual_def
    by (simp add: sum_list_sum_nth split_beta')
  have pointwise:
    "\<And>i. i \<in> {0..<length spec} \<Longrightarrow>
      poly
        (case spec ! i of (c, roots, d) \<Rightarrow>
          CP (as ! i) * c (trace_powers_of f) *
            constraint_root_cofactor roots)
        (g ^ r) =
      common_denominator_constraint_root_residual f r
        (as ! i, spec ! i)"
  proof -
    fix i
    assume i_in: "i \<in> {0..<length spec}"
    then have i_bound: "i < length spec"
      by simp
    obtain c roots d where spec_i: "spec ! i = (c, roots, d)"
      by (cases "spec ! i") auto
    have spec_entry: "(c, roots, d) \<in> set spec"
      using nth_mem[OF i_bound] spec_i by simp
    show
      "poly
        (case spec ! i of (c, roots, d) \<Rightarrow>
          CP (as ! i) * c (trace_powers_of f) *
            constraint_root_cofactor roots)
        (g ^ r) =
      common_denominator_constraint_root_residual f r
        (as ! i, spec ! i)"
    proof (cases "r \<in> set roots")
      case True
      then show ?thesis
        using spec_i
        unfolding common_denominator_constraint_root_residual_def
        by (simp add: CP_def poly_monom)
    next
      case False
      have kill:
        "poly (constraint_root_cofactor roots) (g ^ r) = 0"
        by (rule constraint_root_cofactor_kills_other_root
            [OF root_spec r_in0 spec_entry False])
      show ?thesis
        using spec_i False kill
        unfolding common_denominator_constraint_root_residual_def
        by (simp add: CP_def poly_monom)
    qed
  qed
  show ?thesis
    unfolding lhs rhs
    by (intro sum.cong refl pointwise) simp
qed

lemma common_denominator_mult_composition_spec_eval:
  assumes denom_nonzero:
    "\<And>c roots d. (c, roots, d) \<in> set spec \<Longrightarrow>
      poly (prod (g_map roots)) x \<noteq> 0"
  shows
    "poly common_denominator_poly x * composition_spec_eval f as x =
      poly (common_denominator_numerator f as) x"
proof -
  let ?D = "poly common_denominator_poly x"
  have term_eval:
    "\<And>z. z \<in> set (zip as spec) \<Longrightarrow>
      ?D * composition_spec_eval_term f x z =
      poly (common_denominator_numerator_term f z) x"
  proof -
    fix z
    assume z_in: "z \<in> set (zip as spec)"
    obtain a entry where z_eq: "z = (a, entry)"
      by (cases z) auto
    obtain c roots d where entry_eq: "entry = (c, roots, d)"
      by (cases entry) auto
    have entry_in: "entry \<in> set spec"
    proof -
      obtain i where i_bound: "i < length as" "i < length spec"
        and z_i: "z = (as ! i, spec ! i)"
        using z_in by (auto simp: set_zip)
      have "entry = spec ! i"
        using z_eq z_i by simp
      then show ?thesis
        using nth_mem[OF i_bound(2)] by simp
    qed
    have spec_entry: "(c, roots, d) \<in> set spec"
      using entry_in entry_eq by simp
    have factor:
      "?D =
        poly (prod (g_map roots)) x *
        poly (constraint_root_cofactor roots) x"
      using common_denominator_factor[OF spec_entry]
      by simp
    have denom: "poly (prod (g_map roots)) x \<noteq> 0"
      by (rule denom_nonzero[OF spec_entry])
    show
      "?D * composition_spec_eval_term f x z =
        poly (common_denominator_numerator_term f z) x"
      using z_eq entry_eq factor denom
      unfolding composition_spec_eval_term_def
        common_denominator_numerator_term_def
      by (simp add: field_simps CP_def poly_monom)
  qed
  have mult_sum:
    "?D * sum_list (map (composition_spec_eval_term f x) (zip as spec)) =
      sum_list
        (map (\<lambda>z. poly (common_denominator_numerator_term f z) x)
          (zip as spec))"
  proof -
    have "?D * sum_list (map (composition_spec_eval_term f x) (zip as spec)) =
        sum_list
          (map (\<lambda>z. ?D * composition_spec_eval_term f x z)
            (zip as spec))"
      by (simp add: sum_list_const_mult algebra_simps)
    also have "... =
        sum_list
          (map (\<lambda>z. poly (common_denominator_numerator_term f z) x)
            (zip as spec))"
      using term_eval by (intro arg_cong[where f=sum_list] map_cong) auto
    finally show ?thesis .
  qed
  have rhs:
    "poly (common_denominator_numerator f as) x =
      sum_list
        (map (\<lambda>z. poly (common_denominator_numerator_term f z) x)
          (zip as spec))"
    unfolding common_denominator_numerator_def
    apply (simp add: poly_sum_list)
    apply (intro arg_cong[where f=sum_list] map_cong refl)
    apply (auto simp: common_denominator_numerator_term_def
        split_beta' case_prod_unfold algebra_simps CP_def poly_monom
        split: prod.splits)
    done
  show ?thesis
    unfolding composition_spec_eval_def
    using mult_sum rhs by simp
qed

lemma common_denominator_composition_root_residual_sum_nth:
  assumes len: "length as = length spec"
  shows
    "common_denominator_composition_root_residual f as r =
      (\<Sum>i \<in> {0..<length spec}.
        common_denominator_constraint_root_residual f r (as ! i, spec ! i))"
proof -
  have "common_denominator_composition_root_residual f as r =
      sum_list
        (map (common_denominator_constraint_root_residual f r) (zip as spec))"
    by (simp add: common_denominator_composition_root_residual_def)
  also have "... =
      (\<Sum>i \<in> {0..<length (zip as spec)}.
        map (common_denominator_constraint_root_residual f r) (zip as spec) ! i)"
    by (simp add: sum_list_sum_nth)
  also have "... =
      (\<Sum>i \<in> {0..<length spec}.
        common_denominator_constraint_root_residual f r (as ! i, spec ! i))"
    using len by (intro sum.cong) auto
  finally show ?thesis .
qed

lemma common_denominator_composition_root_residual_split_index:
  assumes len: "length as = length spec"
    and i_bound: "i < length spec"
  shows
    "common_denominator_composition_root_residual f as r =
      common_denominator_constraint_root_residual f r (as ! i, spec ! i) +
      (\<Sum>j \<in> {0..<length spec} - {i}.
        common_denominator_constraint_root_residual f r (as ! j, spec ! j))"
proof -
  let ?F =
    "\<lambda>j. common_denominator_constraint_root_residual f r (as ! j, spec ! j)"
  have "common_denominator_composition_root_residual f as r =
      (\<Sum>j \<in> {0..<length spec}. ?F j)"
    by (rule common_denominator_composition_root_residual_sum_nth[OF len])
  also have "... = ?F i + (\<Sum>j \<in> {0..<length spec} - {i}. ?F j)"
    using i_bound by (simp add: sum.remove)
  finally show ?thesis .
qed

lemma common_denominator_composition_root_residual_zero_unique_nth:
  fixes as bs :: "'f list"
  assumes len_as: "length as = length spec"
    and len_bs: "length bs = length spec"
    and i_bound: "i < length spec"
    and spec_i: "spec ! i = (c, roots, d)"
    and r_in: "r \<in> set roots"
    and nonzero:
      "poly (c (trace_powers_of f)) (g ^ r) \<noteq> 0"
    and outside:
      "\<And>j. j < length spec \<Longrightarrow> j \<noteq> i \<Longrightarrow> as ! j = bs ! j"
    and zero_as: "common_denominator_composition_root_residual f as r = 0"
    and zero_bs: "common_denominator_composition_root_residual f bs r = 0"
  shows "as ! i = bs ! i"
proof -
  let ?C =
    "poly (c (trace_powers_of f)) (g ^ r) *
      poly (constraint_root_cofactor roots) (g ^ r)"
  let ?B =
    "(\<Sum>j \<in> {0..<length spec} - {i}.
      common_denominator_constraint_root_residual f r (as ! j, spec ! j))"
  have spec_entry: "(c, roots, d) \<in> set spec"
    using nth_mem[OF i_bound] spec_i by simp
  have C_nonzero: "?C \<noteq> 0"
    by (rule common_denominator_residual_coefficient_nonzero
        [OF spec_entry r_in nonzero])
  have B_eq:
    "(\<Sum>j \<in> {0..<length spec} - {i}.
      common_denominator_constraint_root_residual f r (bs ! j, spec ! j)) = ?B"
    by (intro sum.cong) (use outside in auto)
  have as_eq:
    "common_denominator_composition_root_residual f as r =
      ?C * (as ! i) + ?B"
    using common_denominator_composition_root_residual_split_index
        [OF len_as i_bound]
      spec_i r_in
    unfolding common_denominator_constraint_root_residual_def
    by (simp add: algebra_simps)
  have bs_eq:
    "common_denominator_composition_root_residual f bs r =
      ?C * (bs ! i) + ?B"
    using common_denominator_composition_root_residual_split_index
        [OF len_bs i_bound]
      spec_i r_in B_eq
    unfolding common_denominator_constraint_root_residual_def
    by (simp add: algebra_simps)
  show ?thesis
  proof (rule linear_equation_solution_unique[OF C_nonzero])
    show "?C * (as ! i) + ?B = 0"
      using as_eq zero_as by simp
    show "?C * (bs ! i) + ?B = 0"
      using bs_eq zero_bs by simp
  qed
qed

lemma random_combination_common_denominator_hides_violations_unique_nth:
  fixes as bs :: "'f list"
  assumes len_as: "length as = length spec"
    and len_bs: "length bs = length spec"
    and i_bound: "i < length spec"
    and spec_i: "spec ! i = (c, roots, d)"
    and violated: "(c, roots, d) \<in> violated_constraints f"
    and r_in: "r \<in> set roots"
    and nonzero:
      "poly (c (trace_powers_of f)) (g ^ r) \<noteq> 0"
    and outside:
      "\<And>j. j < length spec \<Longrightarrow> j \<noteq> i \<Longrightarrow> as ! j = bs ! j"
    and hides_as: "random_combination_common_denominator_hides_violations f as"
    and hides_bs: "random_combination_common_denominator_hides_violations f bs"
  shows "as ! i = bs ! i"
proof -
  have zero_as:
    "common_denominator_composition_root_residual f as r = 0"
    using hides_as violated r_in
    unfolding random_combination_common_denominator_hides_violations_def
    by auto
  have zero_bs:
    "common_denominator_composition_root_residual f bs r = 0"
    using hides_bs violated r_in
    unfolding random_combination_common_denominator_hides_violations_def
    by auto
  show ?thesis
    by (rule common_denominator_composition_root_residual_zero_unique_nth
        [OF len_as len_bs i_bound spec_i r_in nonzero outside zero_as zero_bs])
qed

lemma violated_constraints_has_common_denominator_coefficient:
  assumes violated: "violated_constraints f \<noteq> {}"
  obtains i c roots d r
  where "i < length spec"
    and "spec ! i = (c, roots, d)"
    and "(c, roots, d) \<in> violated_constraints f"
    and "r \<in> set roots"
    and
      "poly (c (trace_powers_of f)) (g ^ r) *
        poly (constraint_root_cofactor roots) (g ^ r) \<noteq> 0"
proof -
  from violated_constraints_has_remainder_bad[OF violated]
  obtain entry where entry0:
    "entry \<in> violated_constraints f"
    "constraint_remainder_bad f entry"
    by blast
  obtain c roots d where entry_eq: "entry = (c, roots, d)"
    by (cases entry) auto
  have entry:
    "(c, roots, d) \<in> violated_constraints f"
    "constraint_remainder_bad f (c, roots, d)"
    using entry0 unfolding entry_eq by simp_all
  then obtain r where r:
    "r \<in> set roots"
    "poly (c (trace_powers_of f)) (g ^ r) \<noteq> 0"
    unfolding constraint_remainder_bad_def by auto
  have spec_entry: "(c, roots, d) \<in> set spec"
    using entry(1) unfolding violated_constraints_def by auto
  then obtain i where i:
    "i < length spec"
    "spec ! i = (c, roots, d)"
    by (auto simp: in_set_conv_nth)
  have coeff:
    "poly (c (trace_powers_of f)) (g ^ r) *
      poly (constraint_root_cofactor roots) (g ^ r) \<noteq> 0"
    by (rule common_denominator_residual_coefficient_nonzero
        [OF spec_entry r(1) r(2)])
  show ?thesis
    by (rule that[OF i entry(1) r(1) coeff])
qed

lemma random_combination_common_denominator_hides_has_coefficient:
  assumes hides: "random_combination_common_denominator_hides_violations f as"
  obtains i c roots d r
  where "i < length spec"
    and "spec ! i = (c, roots, d)"
    and "(c, roots, d) \<in> violated_constraints f"
    and "r \<in> set roots"
    and
      "poly (c (trace_powers_of f)) (g ^ r) *
        poly (constraint_root_cofactor roots) (g ^ r) \<noteq> 0"
proof -
  have violated: "violated_constraints f \<noteq> {}"
    using hides
    unfolding random_combination_common_denominator_hides_violations_def
    by simp
  show ?thesis
    by (rule violated_constraints_has_common_denominator_coefficient[OF violated])
      (rule that)
qed

definition alpha_space :: "'f list set"
  where "alpha_space = {as. length as = length spec}"

definition common_denominator_hiding_alpha_space :: "'f poly \<Rightarrow> 'f list set"
  where
    "common_denominator_hiding_alpha_space f =
      {as \<in> alpha_space.
        random_combination_common_denominator_hides_violations f as}"

lemma finite_length_lists_UNIV:
  "finite {xs :: 'f list. length xs = n}"
proof -
  have "{xs :: 'f list. length xs = n} =
      {xs. set xs \<subseteq> (UNIV :: 'f set) \<and> length xs = n}"
    by auto
  then show ?thesis
    using finite_lists_length_eq[of "UNIV :: 'f set" n] by simp
qed

lemma card_length_lists_UNIV:
  "card {xs :: 'f list. length xs = n} = CARD('f) ^ n"
proof -
  have "{xs :: 'f list. length xs = n} =
      {xs. set xs \<subseteq> (UNIV :: 'f set) \<and> length xs = n}"
    by auto
  then show ?thesis
    using card_lists_length_eq[of "UNIV :: 'f set" n] by simp
qed

definition fri_challenge_space :: "nat \<Rightarrow> 'f list set"
  where "fri_challenge_space n = {bs. length bs = n}"

lemma finite_fri_challenge_space[simp]:
  "finite (fri_challenge_space n)"
  unfolding fri_challenge_space_def
  by (rule finite_length_lists_UNIV)

lemma card_fri_challenge_space:
  "card (fri_challenge_space n) = CARD('f) ^ n"
  unfolding fri_challenge_space_def
  by (rule card_length_lists_UNIV)

lemma card_alpha_space[simp]:
  "card alpha_space = CARD('f) ^ length spec"
  unfolding alpha_space_def by (rule card_length_lists_UNIV)

lemma common_denominator_hiding_alpha_space_card_bound:
  "card (common_denominator_hiding_alpha_space f) \<le>
    (if length spec = 0 then 0 else CARD('f) ^ (length spec - 1))"
proof (cases "common_denominator_hiding_alpha_space f = {}")
  case True
  then show ?thesis by simp
next
  case False
  let ?S = "common_denominator_hiding_alpha_space f"
  from False obtain as0 where as0_in: "as0 \<in> ?S"
    by auto
  have hides0: "random_combination_common_denominator_hides_violations f as0"
    using as0_in unfolding common_denominator_hiding_alpha_space_def by simp
  from random_combination_common_denominator_hides_has_coefficient[OF hides0]
  obtain i c roots d r where
    i_bound: "i < length spec"
    and spec_i: "spec ! i = (c, roots, d)"
    and violated: "(c, roots, d) \<in> violated_constraints f"
    and r_in: "r \<in> set roots"
    and coeff_nonzero:
      "poly (c (trace_powers_of f)) (g ^ r) *
        poly (constraint_root_cofactor roots) (g ^ r) \<noteq> 0"
    by blast
  have nonzero: "poly (c (trace_powers_of f)) (g ^ r) \<noteq> 0"
    using coeff_nonzero by auto
  let ?key = "\<lambda>xs :: 'f list. (take i xs, drop (Suc i) xs)"
  have inj: "inj_on ?key ?S"
  proof (rule inj_onI)
    fix xs ys
    assume xs_in: "xs \<in> ?S"
      and ys_in: "ys \<in> ?S"
      and key_eq: "?key xs = ?key ys"
    have len_xs: "length xs = length spec"
      using xs_in
      unfolding common_denominator_hiding_alpha_space_def alpha_space_def
      by simp
    have len_ys: "length ys = length spec"
      using ys_in
      unfolding common_denominator_hiding_alpha_space_def alpha_space_def
      by simp
    have hides_xs:
      "random_combination_common_denominator_hides_violations f xs"
      using xs_in unfolding common_denominator_hiding_alpha_space_def by simp
    have hides_ys:
      "random_combination_common_denominator_hides_violations f ys"
      using ys_in unfolding common_denominator_hiding_alpha_space_def by simp
    have take_eq: "take i xs = take i ys"
      using key_eq by simp
    have drop_eq: "drop (Suc i) xs = drop (Suc i) ys"
      using key_eq by simp
    have outside:
      "\<And>j. j < length spec \<Longrightarrow> j \<noteq> i \<Longrightarrow> xs ! j = ys ! j"
    proof -
      fix j
      assume j_bound: "j < length spec"
        and j_ne: "j \<noteq> i"
      show "xs ! j = ys ! j"
      proof (cases "j < i")
        case True
        have "xs ! j = take i xs ! j"
          using True by simp
        also have "... = take i ys ! j"
          using take_eq by simp
        also have "... = ys ! j"
          using True by simp
        finally show ?thesis .
      next
        case False
        then have i_lt_j: "i < j"
          using j_ne by linarith
        have j_decomp: "j = Suc i + (j - Suc i)"
          using i_lt_j by simp
        have drop_idx_bound_xs: "j - Suc i < length (drop (Suc i) xs)"
          using j_bound i_lt_j len_xs by simp
        have drop_idx_bound_ys: "j - Suc i < length (drop (Suc i) ys)"
          using j_bound i_lt_j len_ys by simp
        have "xs ! j = drop (Suc i) xs ! (j - Suc i)"
          using drop_idx_bound_xs j_decomp by simp
        also have "... = drop (Suc i) ys ! (j - Suc i)"
          using drop_eq by simp
        also have "... = ys ! j"
          using drop_idx_bound_ys j_decomp by simp
        finally show ?thesis .
      qed
    qed
    have nth_i: "xs ! i = ys ! i"
      by (rule random_combination_common_denominator_hides_violations_unique_nth
          [OF len_xs len_ys i_bound spec_i violated r_in nonzero outside
            hides_xs hides_ys])
    show "xs = ys"
    proof (rule nth_equalityI)
      show "length xs = length ys"
        using len_xs len_ys by simp
    next
      fix j
      assume j_bound: "j < length xs"
      then have j_spec: "j < length spec"
        using len_xs by simp
      show "xs ! j = ys ! j"
      proof (cases "j = i")
        case True
        then show ?thesis
          using nth_i by simp
      next
        case False
        then show ?thesis
          by (rule outside[OF j_spec])
      qed
    qed
  qed
  let ?A = "{xs :: 'f list. length xs = i}"
  let ?B = "{xs :: 'f list. length xs = length spec - Suc i}"
  have image_subset: "?key ` ?S \<subseteq> ?A \<times> ?B"
  proof
    fix x
    assume "x \<in> ?key ` ?S"
    then obtain xs where xs_in: "xs \<in> ?S" and x_eq: "x = ?key xs"
      by auto
    have len_xs: "length xs = length spec"
      using xs_in
      unfolding common_denominator_hiding_alpha_space_def alpha_space_def
      by simp
    show "x \<in> ?A \<times> ?B"
      using len_xs i_bound unfolding x_eq by simp
  qed
  have finite_A: "finite ?A"
    by (rule finite_length_lists_UNIV)
  have finite_B: "finite ?B"
    by (rule finite_length_lists_UNIV)
  have finite_prod: "finite (?A \<times> ?B)"
    using finite_A finite_B by simp
  have finite_alpha: "finite alpha_space"
    unfolding alpha_space_def by (rule finite_length_lists_UNIV)
  have finite_S: "finite ?S"
    unfolding common_denominator_hiding_alpha_space_def
    using finite_alpha by simp
  have card_image_le: "card (?key ` ?S) \<le> card (?A \<times> ?B)"
    by (rule card_mono[OF finite_prod image_subset])
  have card_S: "card ?S = card (?key ` ?S)"
    using card_image[OF inj] by simp
  have card_prod:
    "card (?A \<times> ?B) =
      CARD('f) ^ i * CARD('f) ^ (length spec - Suc i)"
    using finite_A finite_B by (simp add: card_length_lists_UNIV)
  have exp_eq:
    "i + (length spec - Suc i) = length spec - 1"
    using i_bound by simp
  have "card ?S \<le> CARD('f) ^ i * CARD('f) ^ (length spec - Suc i)"
    using card_image_le card_S card_prod by simp
  also have "... = CARD('f) ^ (length spec - 1)"
    using exp_eq by (simp add: power_add[symmetric])
  finally have bound:
    "card ?S \<le> CARD('f) ^ (length spec - 1)" .
  have "length spec \<noteq> 0"
    using i_bound by auto
  then show ?thesis
    using bound by simp
qed

lemma nnreal_nat_divide_right_mono:
  assumes "a \<le> b"
  shows "nnreal a / nnreal c \<le> nnreal b / nnreal c"
  using assms
  by transfer (simp add: divide_right_mono)

lemma nnreal_nat_divide_self:
  assumes "k \<noteq> 0"
  shows "nnreal k / nnreal k = 1"
  using assms by transfer simp

lemma nnreal_power_fraction_cancel:
  assumes "k \<noteq> 0"
  shows "nnreal (k ^ n) / nnreal (k ^ Suc n) = 1 / nnreal k"
  using assms
  by transfer (simp add: power_Suc field_simps)

lemma common_denominator_hiding_alpha_space_fraction_bound:
  "nnreal (card (common_denominator_hiding_alpha_space f)) /
    nnreal (CARD('f) ^ length spec) \<le> composition_error_bound"
proof (cases "length spec")
  case 0
  then have "card (common_denominator_hiding_alpha_space f) = 0"
    using common_denominator_hiding_alpha_space_card_bound[of f] by simp
  then show ?thesis
    unfolding composition_error_bound_def by simp
next
  case (Suc n)
  have card_le:
    "card (common_denominator_hiding_alpha_space f) \<le> CARD('f) ^ n"
    using common_denominator_hiding_alpha_space_card_bound[of f]
    unfolding Suc by simp
  have field_nonzero: "CARD('f) \<noteq> 0"
    by simp
  have "nnreal (card (common_denominator_hiding_alpha_space f)) /
      nnreal (CARD('f) ^ length spec) \<le>
      nnreal (CARD('f) ^ n) / nnreal (CARD('f) ^ Suc n)"
    unfolding Suc
    using card_le
    by (rule nnreal_nat_divide_right_mono)
  also have "... = 1 / nnreal (CARD('f))"
    by (rule nnreal_power_fraction_cancel[OF field_nonzero])
  also have "... = composition_error_bound"
    using size_card unfolding composition_error_bound_def by simp
  finally show ?thesis .
qed

lemma low_degree_trace_table_unique:
  assumes deg_f: "degree f < clength"
    and deg_q: "degree q < clength"
    and table_eq: "map (poly f) eval_domain = map (poly q) eval_domain"
  shows "f = q"
proof -
  have clength_le_domain: "clength \<le> clength * scale"
    using scale_pos by simp
  have deg_f_domain: "degree f < clength * scale"
    using deg_f clength_le_domain by linarith
  have deg_q_domain: "degree q < clength * scale"
    using deg_q clength_le_domain by linarith
  show ?thesis
  proof (rule poly_eq_on_eval_domainI[OF deg_f_domain deg_q_domain])
    fix idx
    assume idx_bound: "idx < clength * scale"
    have idx_len: "idx < length eval_domain"
      using idx_bound eval_domain_length by simp
    have "map (poly f) eval_domain ! idx = map (poly q) eval_domain ! idx"
      using table_eq idx_len by simp
    then show "poly f (h ^ idx * shift) = poly q (h ^ idx * shift)"
      using idx_len idx_bound eval_domain_nth by simp
  qed
qed

definition low_degree_trace_witness :: "'f list \<Rightarrow> 'f poly"
  where
    "low_degree_trace_witness trace_table =
      (SOME f. degree f < clength \<and>
        trace_table = map (poly f) eval_domain)"

lemma low_degree_trace_witness_eq:
  assumes deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
  shows "low_degree_trace_witness trace_table = f"
  unfolding low_degree_trace_witness_def
proof (rule some_equality)
  show "degree f < clength \<and> trace_table = map (poly f) eval_domain"
    using deg_f trace_table by simp
next
  fix q
  assume q:
    "degree q < clength \<and> trace_table = map (poly q) eval_domain"
  then have table_eq: "map (poly f) eval_domain = map (poly q) eval_domain"
    using trace_table by simp
  show "q = f"
    using low_degree_trace_table_unique[OF deg_f conjunct1[OF q] table_eq]
    by simp
qed

definition composition_trace_bad_alpha_space :: "'f list \<Rightarrow> 'f list set"
  where
    "composition_trace_bad_alpha_space trace_table =
      (let f = low_degree_trace_witness trace_table in
        if degree f < clength \<and>
           trace_table = map (poly f) eval_domain \<and>
           violated_constraints f \<noteq> {}
        then
          {as \<in> common_denominator_hiding_alpha_space f.
            common_denominator_degree_bounds f as}
        else {})"

lemma finite_alpha_space:
  "finite alpha_space"
  unfolding alpha_space_def by (rule finite_length_lists_UNIV)

lemma common_denominator_hiding_alpha_space_subset_alpha_space:
  "common_denominator_hiding_alpha_space f \<subseteq> alpha_space"
  unfolding common_denominator_hiding_alpha_space_def by auto

lemma finite_common_denominator_hiding_alpha_space:
  "finite (common_denominator_hiding_alpha_space f)"
  using finite_alpha_space
  unfolding common_denominator_hiding_alpha_space_def by simp

lemma composition_trace_bad_alpha_space_subset_alpha_space:
  "composition_trace_bad_alpha_space trace_table \<subseteq> alpha_space"
proof -
  let ?f = "low_degree_trace_witness trace_table"
  have "composition_trace_bad_alpha_space trace_table \<subseteq>
      common_denominator_hiding_alpha_space ?f"
    unfolding composition_trace_bad_alpha_space_def Let_def by auto
  also have "... \<subseteq> alpha_space"
    by (rule common_denominator_hiding_alpha_space_subset_alpha_space)
  finally show ?thesis .
qed

lemma composition_trace_bad_alpha_space_fraction_bound:
  "nnreal (card (composition_trace_bad_alpha_space trace_table)) /
    nnreal (CARD('f) ^ length spec) \<le> composition_error_bound"
proof -
  let ?f = "low_degree_trace_witness trace_table"
  have subset:
    "composition_trace_bad_alpha_space trace_table \<subseteq>
      common_denominator_hiding_alpha_space ?f"
    unfolding composition_trace_bad_alpha_space_def Let_def by auto
  have card_le:
    "card (composition_trace_bad_alpha_space trace_table) \<le>
      card (common_denominator_hiding_alpha_space ?f)"
    by (rule card_mono[OF finite_common_denominator_hiding_alpha_space subset])
  have "nnreal (card (composition_trace_bad_alpha_space trace_table)) /
      nnreal (CARD('f) ^ length spec) \<le>
      nnreal (card (common_denominator_hiding_alpha_space ?f)) /
        nnreal (CARD('f) ^ length spec)"
    by (rule nnreal_nat_divide_right_mono[OF card_le])
  also have "... \<le> composition_error_bound"
    by (rule common_denominator_hiding_alpha_space_fraction_bound)
  finally show ?thesis .
qed

lemma composition_trace_bad_alpha_space_fraction_bound_alpha_space:
  "nnreal (card (composition_trace_bad_alpha_space trace_table)) /
    nnreal (card alpha_space) \<le> composition_error_bound"
  using composition_trace_bad_alpha_space_fraction_bound[of trace_table]
  by simp

lemma composition_trace_bad_alpha_space_card_bound:
  "card (composition_trace_bad_alpha_space trace_table) \<le>
    (if length spec = 0 then 0 else CARD('f) ^ (length spec - 1))"
proof -
  let ?f = "low_degree_trace_witness trace_table"
  have subset:
    "composition_trace_bad_alpha_space trace_table \<subseteq>
      common_denominator_hiding_alpha_space ?f"
    unfolding composition_trace_bad_alpha_space_def Let_def by auto
  have card_le:
    "card (composition_trace_bad_alpha_space trace_table) \<le>
      card (common_denominator_hiding_alpha_space ?f)"
    by (rule card_mono[OF finite_common_denominator_hiding_alpha_space subset])
  also have "... \<le>
      (if length spec = 0 then 0 else CARD('f) ^ (length spec - 1))"
    by (rule common_denominator_hiding_alpha_space_card_bound)
  finally show ?thesis .
qed

lemma trace_powers_of_eval_nth:
  assumes "k < powers"
  shows "poly (trace_powers_of f ! k) x = poly f (g ^ k * x)"
  using assms
  unfolding trace_powers_of_def XP_def
  by (simp add: poly_pcompose poly_monom)

lemma query_trace_power_eval_nth:
  assumes k_bound: "k < powers"
    and idx_bound: "idx + k * scale < clength * scale"
  shows
    "map (poly f) eval_domain ! (idx + k * scale) =
      poly (trace_powers_of f ! k) (h ^ idx * shift)"
proof -
  have eval:
    "map (poly f) eval_domain ! (idx + k * scale) =
      poly f (h ^ (idx + k * scale) * shift)"
    using eval_domain_nth[OF idx_bound] idx_bound eval_domain_length by simp
  have arg:
    "g ^ k * (h ^ idx * shift) = h ^ (idx + k * scale) * shift"
  proof -
    have gpow: "g ^ k = h ^ (scale * k)"
      using domain_alignment by (simp add: power_mult)
    have "g ^ k * (h ^ idx * shift) =
        h ^ (scale * k) * h ^ idx * shift"
      using gpow by (simp add: algebra_simps)
    also have "... = h ^ (idx + k * scale) * shift"
      by (simp add: power_add algebra_simps mult.commute)
    finally show ?thesis .
  qed
  show ?thesis
    using eval trace_powers_of_eval_nth[OF k_bound, of f "h ^ idx * shift"] arg
    by simp
qed

lemma query_values_trace_powers:
  assumes trace_table: "trace_table = map (poly f) eval_domain"
    and scaled_bound:
      "\<And>i. i \<in> set (powers_scaled idx) \<Longrightarrow> i < clength * scale"
  shows
    "map ((!) trace_table) (powers_scaled idx) =
      map (\<lambda>q. poly q (h ^ idx * shift)) (trace_powers_of f)"
proof (rule nth_equalityI)
  show "length (map ((!) trace_table) (powers_scaled idx)) =
    length (map (\<lambda>q. poly q (h ^ idx * shift)) (trace_powers_of f))"
    unfolding powers_scaled_def by simp
next
  fix k
  assume k_bound:
    "k < length (map ((!) trace_table) (powers_scaled idx))"
  then have k_lt: "k < powers"
    unfolding powers_scaled_def by simp
  have scaled_idx_in:
    "idx + k * scale \<in> set (powers_scaled idx)"
    using k_lt unfolding powers_scaled_def by auto
  have idx_bound: "idx + k * scale < clength * scale"
    by (rule scaled_bound[OF scaled_idx_in])
  have left:
    "map ((!) trace_table) (powers_scaled idx) ! k =
      trace_table ! (idx + k * scale)"
    using k_lt unfolding powers_scaled_def by simp
  have right:
    "map (\<lambda>q. poly q (h ^ idx * shift)) (trace_powers_of f) ! k =
      poly (trace_powers_of f ! k) (h ^ idx * shift)"
    using k_lt by simp
  show
    "map ((!) trace_table) (powers_scaled idx) ! k =
      map (\<lambda>q. poly q (h ^ idx * shift)) (trace_powers_of f) ! k"
    using query_trace_power_eval_nth[OF k_lt idx_bound] left right trace_table
    by simp
qed

lemma query_consistent_at_trace_powers:
  assumes qc: "query_consistent_at trace_table composition_table as idx"
    and trace_table: "trace_table = map (poly f) eval_domain"
  shows
    "composition_table ! idx =
      cp_eval as (map (\<lambda>q. poly q (h ^ idx * shift)) (trace_powers_of f))
        (h ^ idx * shift)"
proof -
  have qc_unfolded:
    "idx < clength * scale \<and>
     length trace_table = clength * scale \<and>
     length composition_table = clength * scale \<and>
     (\<forall>i \<in> set (powers_scaled idx). i < length trace_table) \<and>
     composition_table ! idx =
       cp_eval as (map ((!) trace_table) (powers_scaled idx)) (h ^ idx * shift)"
    using qc unfolding query_consistent_at_def .
  have trace_len: "length trace_table = clength * scale"
    using qc_unfolded by blast
  have scaled_bound:
    "\<And>i. i \<in> set (powers_scaled idx) \<Longrightarrow> i < clength * scale"
  proof -
    fix i
    assume i_in: "i \<in> set (powers_scaled idx)"
    have "i < length trace_table"
      using qc_unfolded i_in by blast
    then show "i < clength * scale"
      using trace_len by simp
  qed
  have vals_eq:
    "map ((!) trace_table) (powers_scaled idx) =
      map (\<lambda>q. poly q (h ^ idx * shift)) (trace_powers_of f)"
    by (rule query_values_trace_powers[OF trace_table scaled_bound])
  have comp:
    "composition_table ! idx =
      cp_eval as (map ((!) trace_table) (powers_scaled idx)) (h ^ idx * shift)"
    using qc_unfolded by blast
  have cp_eq:
    "cp_eval as (map ((!) trace_table) (powers_scaled idx)) (h ^ idx * shift) =
      cp_eval as (map (\<lambda>q. poly q (h ^ idx * shift)) (trace_powers_of f))
        (h ^ idx * shift)"
    using vals_eq by (rule arg_cong)
  show ?thesis
    using comp cp_eq by simp
qed

lemma fold_add_sum_list:
  fixes f :: "'x \<Rightarrow> 'b::comm_monoid_add"
  shows "fold (\<lambda>x acc. f x + acc) xs acc = sum_list (map f xs) + acc"
proof (induction xs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (simp add: ac_simps)
qed

lemma cp_eval_agrees_with_spec_lists:
  fixes specs :: "(('f poly list \<Rightarrow> 'f poly) \<times> nat list \<times> nat) list"
    and spec2s :: "(('f list \<Rightarrow> 'f) \<times> nat list) list"
    and qs :: "'f poly list"
  assumes len: "length spec2s = length specs"
    and zip_subset: "set (zip specs spec2s) \<subseteq> set (zip spec spec2)"
    and qs_len: "powers \<le> length qs"
  shows
    "fold
      (\<lambda>(a, (c2, roots2)).
        (+) (a * (c2 (map (\<lambda>q. poly q x) qs) /
          poly (prod (g_map roots2)) x)))
      (zip as spec2s) vacc =
    sum_list
      (map
        (\<lambda>(a, (c, roots, d)).
          a * (poly (c qs) x / poly (prod (g_map roots)) x))
        (zip as specs)) + vacc"
proof -
  let ?vterm =
    "\<lambda>z. case z of (a, entry) \<Rightarrow>
      case entry of (c2, roots2) \<Rightarrow>
        a * (c2 (map (\<lambda>q. poly q x) qs) /
          poly (prod (g_map roots2)) x)"
  let ?sterm =
    "\<lambda>z. case z of (a, entry) \<Rightarrow>
      case entry of (c, roots, d) \<Rightarrow>
        a * (poly (c qs) x / poly (prod (g_map roots)) x)"
  have terms_eq:
    "map ?vterm (zip as spec2s) = map ?sterm (zip as specs)"
  proof (rule nth_equalityI)
    show "length (map ?vterm (zip as spec2s)) =
      length (map ?sterm (zip as specs))"
      using len by simp
  next
    fix i
    assume i_bound: "i < length (map ?vterm (zip as spec2s))"
    then have i_as: "i < length as"
      by simp
    have i_spec2: "i < length spec2s"
      using i_bound by simp
    have i_specs: "i < length specs"
      using i_spec2 len by simp
    obtain c roots d where specs_i: "specs ! i = (c, roots, d)"
      by (cases "specs ! i") auto
    obtain c2 roots2 where spec2s_i: "spec2s ! i = (c2, roots2)"
      by (cases "spec2s ! i") auto
    have pair_in:
      "((c, roots, d), (c2, roots2)) \<in> set (zip spec spec2)"
    proof -
      have "(specs ! i, spec2s ! i) \<in> set (zip specs spec2s)"
      proof -
        have "i < length (zip specs spec2s)"
          using i_specs i_spec2 by simp
        then have "zip specs spec2s ! i \<in> set (zip specs spec2s)"
          by (rule nth_mem)
        then show ?thesis
          using i_specs i_spec2 by simp
      qed
      then show ?thesis
        using zip_subset specs_i spec2s_i by auto
    qed
    have roots_eq: "roots2 = roots"
      and raw_eq:
        "c2 (map (\<lambda>q. poly q x) qs) = poly (c qs) x"
      using specs_agree[OF pair_in qs_len, of x] by simp_all
    show "map ?vterm (zip as spec2s) ! i =
      map ?sterm (zip as specs) ! i"
      using i_as i_spec2 i_specs specs_i spec2s_i roots_eq raw_eq
      by simp
  qed
  have fold_eq:
    "fold
      (\<lambda>(a, (c2, roots2)).
        (+) (a * (c2 (map (\<lambda>q. poly q x) qs) /
          poly (prod (g_map roots2)) x)))
      (zip as spec2s) vacc =
    fold (\<lambda>z acc. ?vterm z + acc) (zip as spec2s) vacc"
    by (rule fold_cong) (auto simp: fun_eq_iff split: prod.splits)
  have
    "fold
      (\<lambda>(a, (c2, roots2)).
        (+) (a * (c2 (map (\<lambda>q. poly q x) qs) /
          poly (prod (g_map roots2)) x)))
      (zip as spec2s) vacc =
    sum_list (map ?vterm (zip as spec2s)) + vacc"
    unfolding fold_eq
    by (rule fold_add_sum_list)
  also have "... =
    sum_list
      (map
        (\<lambda>(a, (c, roots, d)).
          a * (poly (c qs) x / poly (prod (g_map roots)) x))
        (zip as specs)) + vacc"
    using terms_eq by simp
  finally show ?thesis .
qed

lemma cp_eval_trace_powers_agrees_with_spec:
  "cp_eval as (map (\<lambda>q. poly q x) (trace_powers_of f)) x =
    composition_spec_eval f as x"
proof -
  have aligned:
    "fold
      (\<lambda>(a, (c2, roots2)).
        (+) (a * (c2
          (map (\<lambda>q. poly q x) (trace_powers_of f)) /
          poly (prod (g_map roots2)) x)))
      (zip as spec2) 0 =
    sum_list
      (map
        (\<lambda>(a, (c, roots, d)).
          a * (poly (c (trace_powers_of f)) x /
            poly (prod (g_map roots)) x))
        (zip as spec)) + 0"
    by (rule cp_eval_agrees_with_spec_lists[OF spec2_length subset_refl])
      simp
  have spec_sum:
    "sum_list
      (map
        (\<lambda>(a, (c, roots, d)).
          a * (poly (c (trace_powers_of f)) x /
            poly (prod (g_map roots)) x))
        (zip as spec)) =
      sum_list (map (composition_spec_eval_term f x) (zip as spec))"
    apply (intro arg_cong[where f=sum_list] map_cong refl)
    apply (auto simp: composition_spec_eval_term_def split_beta'
        case_prod_unfold split: prod.splits)
    done
  show ?thesis
    unfolding cp_eval_def composition_spec_eval_def
    using aligned spec_sum by simp
qed

lemma common_denominator_mult_cp_eval_trace_powers:
  assumes idx_bound: "idx < clength * scale"
  shows
    "poly common_denominator_poly (h ^ idx * shift) *
      cp_eval as
        (map (\<lambda>q. poly q (h ^ idx * shift)) (trace_powers_of f))
        (h ^ idx * shift) =
      poly (common_denominator_numerator f as) (h ^ idx * shift)"
proof -
  have denom:
    "\<And>c roots d. (c, roots, d) \<in> set spec \<Longrightarrow>
      poly (prod (g_map roots)) (h ^ idx * shift) \<noteq> 0"
  proof -
    fix c roots d
    assume spec_entry: "(c, roots, d) \<in> set spec"
    show "poly (prod (g_map roots)) (h ^ idx * shift) \<noteq> 0"
      by (rule query_denominator_nonzero[OF spec_entry idx_bound])
  qed
  have mult:
    "poly common_denominator_poly (h ^ idx * shift) *
      composition_spec_eval f as (h ^ idx * shift) =
      poly (common_denominator_numerator f as) (h ^ idx * shift)"
    by (rule common_denominator_mult_composition_spec_eval[OF denom])
  show ?thesis
    using mult cp_eval_trace_powers_agrees_with_spec[of as "h ^ idx * shift" f]
    by simp
qed

lemma common_denominator_numerator_identity_residual_zero:
  assumes len: "length as = length spec"
    and identity:
      "common_denominator_numerator f as = common_denominator_poly * q"
    and spec_entry: "(c, roots, d) \<in> set spec"
    and r_in: "r \<in> set roots"
  shows "common_denominator_composition_root_residual f as r = 0"
proof -
  have numerator_eval:
    "poly (common_denominator_numerator f as) (g ^ r) =
      common_denominator_composition_root_residual f as r"
    by (rule common_denominator_numerator_root_eval[OF len spec_entry r_in])
  have root_zero: "poly common_denominator_poly (g ^ r) = 0"
    by (rule common_denominator_vanishes_on_constraint_root
        [OF spec_entry r_in])
  have "poly (common_denominator_numerator f as) (g ^ r) = 0"
    using identity root_zero by simp
  then show ?thesis
    using numerator_eval by simp
qed

lemma common_denominator_numerator_identity_hides_violations:
  assumes len: "length as = length spec"
    and violated: "violated_constraints f \<noteq> {}"
    and identity:
      "common_denominator_numerator f as = common_denominator_poly * q"
  shows "random_combination_common_denominator_hides_violations f as"
proof -
  have residual_zero:
    "\<And>c roots d r.
      (c, roots, d) \<in> violated_constraints f \<Longrightarrow>
      r \<in> set roots \<Longrightarrow>
      common_denominator_composition_root_residual f as r = 0"
  proof -
    fix c roots d r
    assume entry: "(c, roots, d) \<in> violated_constraints f"
      and r_in: "r \<in> set roots"
    have spec_entry: "(c, roots, d) \<in> set spec"
      using entry unfolding violated_constraints_def by simp
    show "common_denominator_composition_root_residual f as r = 0"
      by (rule common_denominator_numerator_identity_residual_zero
          [OF len identity spec_entry r_in])
  qed
  show ?thesis
    using violated residual_zero
    unfolding random_combination_common_denominator_hides_violations_def
    by auto
qed

lemma composition_table_agrees_with_rational_expression:
  assumes composition_low:
      "composition_table_low_degree maxDegree composition_table"
    and trace_table: "trace_table = map (poly f) eval_domain"
    and all_queries: "all_queries_consistent trace_table composition_table as"
  obtains q where
    "degree q \<le> maxDegree"
    and "\<And>idx. idx \<in> query_sample_space \<Longrightarrow>
      poly q (h ^ idx * shift) =
        cp_eval as (map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f))
          (h ^ idx * shift)"
proof -
  from composition_low obtain q where deg_q: "degree q \<le> maxDegree"
    and table_q: "composition_table = map (poly q) eval_domain"
    unfolding composition_table_low_degree_def by blast
  have agree:
    "\<And>idx. idx \<in> query_sample_space \<Longrightarrow>
      poly q (h ^ idx * shift) =
        cp_eval as (map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f))
          (h ^ idx * shift)"
  proof -
    fix idx
    assume idx_in: "idx \<in> query_sample_space"
    have idx_bound: "idx < clength * scale"
      by (rule query_sample_space_less_domain[OF idx_in])
    have qc: "query_consistent_at trace_table composition_table as idx"
      using all_queries idx_in unfolding all_queries_consistent_def by simp
    have comp_value:
      "composition_table ! idx = poly q (h ^ idx * shift)"
      using table_q eval_domain_nth[OF idx_bound] idx_bound eval_domain_length
      by simp
    show "poly q (h ^ idx * shift) =
        cp_eval as (map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f))
          (h ^ idx * shift)"
      using query_consistent_at_trace_powers[OF qc trace_table] comp_value
      by simp
  qed
  show ?thesis
    by (rule that[OF deg_q agree])
qed

lemma common_denominator_numerator_identity_from_queries:
  assumes composition_low:
      "composition_table_low_degree maxDegree composition_table"
    and trace_table: "trace_table = map (poly f) eval_domain"
    and all_queries: "all_queries_consistent trace_table composition_table as"
    and num_deg:
      "degree (common_denominator_numerator f as) < query_sample_space_size"
    and prod_deg:
      "\<And>q. degree q \<le> maxDegree \<Longrightarrow>
        degree (common_denominator_poly * q) < query_sample_space_size"
  obtains q where
    "degree q \<le> maxDegree"
    and "common_denominator_numerator f as = common_denominator_poly * q"
proof -
  from composition_table_agrees_with_rational_expression
      [OF composition_low trace_table all_queries]
  obtain q where deg_q: "degree q \<le> maxDegree"
    and agree:
      "\<And>idx. idx \<in> query_sample_space \<Longrightarrow>
        poly q (h ^ idx * shift) =
          cp_eval as
            (map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f))
            (h ^ idx * shift)"
    by blast
  have eval_agree:
    "\<And>idx. idx \<in> query_sample_space \<Longrightarrow>
      poly (common_denominator_numerator f as) (h ^ idx * shift) =
      poly (common_denominator_poly * q) (h ^ idx * shift)"
  proof -
    fix idx
    assume idx_in: "idx \<in> query_sample_space"
    have idx_bound: "idx < clength * scale"
      by (rule query_sample_space_less_domain[OF idx_in])
    have mult:
      "poly common_denominator_poly (h ^ idx * shift) *
        cp_eval as
          (map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f))
          (h ^ idx * shift) =
        poly (common_denominator_numerator f as) (h ^ idx * shift)"
      by (rule common_denominator_mult_cp_eval_trace_powers[OF idx_bound])
    have "poly (common_denominator_poly * q) (h ^ idx * shift) =
      poly common_denominator_poly (h ^ idx * shift) *
        poly q (h ^ idx * shift)"
      by simp
    also have "... =
      poly common_denominator_poly (h ^ idx * shift) *
        cp_eval as
          (map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f))
          (h ^ idx * shift)"
      using agree[OF idx_in] by simp
    also have "... = poly (common_denominator_numerator f as) (h ^ idx * shift)"
      using mult by simp
    finally show
      "poly (common_denominator_numerator f as) (h ^ idx * shift) =
        poly (common_denominator_poly * q) (h ^ idx * shift)"
      by simp
  qed
  have identity:
    "common_denominator_numerator f as = common_denominator_poly * q"
    by (rule poly_eq_on_query_sample_domainI[OF num_deg prod_deg[OF deg_q]])
      (rule eval_agree)
  show ?thesis
    by (rule that[OF deg_q identity])
qed

lemma common_denominator_numerator_identity_from_queries_bounds:
  assumes composition_low:
      "composition_table_low_degree maxDegree composition_table"
    and trace_table: "trace_table = map (poly f) eval_domain"
    and all_queries: "all_queries_consistent trace_table composition_table as"
    and bounds: "common_denominator_degree_bounds f as"
  obtains q where
    "degree q \<le> maxDegree"
    and "common_denominator_numerator f as = common_denominator_poly * q"
proof -
  have num_deg:
    "degree (common_denominator_numerator f as) < query_sample_space_size"
    using bounds unfolding common_denominator_degree_bounds_def by simp
  have prod_deg:
    "\<And>q. degree q \<le> maxDegree \<Longrightarrow>
      degree (common_denominator_poly * q) < query_sample_space_size"
    using bounds unfolding common_denominator_degree_bounds_def by simp
  from common_denominator_numerator_identity_from_queries
      [OF composition_low trace_table all_queries num_deg prod_deg]
  obtain q where deg_q: "degree q \<le> maxDegree"
    and identity:
      "common_denominator_numerator f as = common_denominator_poly * q"
    by blast
  show ?thesis
    by (rule that[OF deg_q identity])
qed

lemma random_combination_common_denominator_hides_from_queries:
  assumes len_as: "length as = length spec"
    and false_statement: "\<not> exists_valid_trace"
    and deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    and composition_low:
      "composition_table_low_degree maxDegree composition_table"
    and all_queries: "all_queries_consistent trace_table composition_table as"
    and bounds: "common_denominator_degree_bounds f as"
  shows "random_combination_common_denominator_hides_violations f as"
proof -
  have violated: "violated_constraints f \<noteq> {}"
    by (rule false_statement_violated_constraints[OF false_statement deg_f])
  from common_denominator_numerator_identity_from_queries_bounds
      [OF composition_low trace_table all_queries bounds]
  obtain q where
    "degree q \<le> maxDegree"
    and identity:
      "common_denominator_numerator f as = common_denominator_poly * q"
    by blast
  show ?thesis
    by (rule common_denominator_numerator_identity_hides_violations
        [OF len_as violated identity])
qed

lemma all_queries_consistent_iff_no_bad_queries:
  "all_queries_consistent trace_table composition_table as \<longleftrightarrow>
    bad_query_indices trace_table composition_table as = {}"
  unfolding all_queries_consistent_def bad_query_indices_def by auto

lemma query_disagreement_indices_nonempty_iff:
  "query_disagreement_indices trace_table composition_table as \<noteq> {} \<longleftrightarrow>
    \<not> all_queries_consistent trace_table composition_table as"
  unfolding query_disagreement_indices_def
  using all_queries_consistent_iff_no_bad_queries by simp

lemma query_consistent_at_from_common_denominator_residual_zero:
  assumes trace_table: "trace_table = map (poly f) eval_domain"
    and composition_table: "composition_table = map (poly q) eval_domain"
    and residual_zero:
      "common_denominator_numerator f as - common_denominator_poly * q = 0"
    and idx_in: "idx \<in> query_sample_space"
  shows "query_consistent_at trace_table composition_table as idx"
proof -
  have idx_bound: "idx < clength * scale"
    by (rule query_sample_space_less_domain[OF idx_in])
  have trace_len: "length trace_table = clength * scale"
    using trace_table eval_domain_length by simp
  have comp_len: "length composition_table = clength * scale"
    using composition_table eval_domain_length by simp
  have powers_bound:
    "\<forall>i \<in> set (powers_scaled idx). i < length trace_table"
  proof
    fix i
    assume i_in: "i \<in> set (powers_scaled idx)"
    show "i < length trace_table"
      using query_sample_space_powers_scaled_bound[OF idx_in i_in] trace_len
      by simp
  qed
  have comp_value:
    "composition_table ! idx = poly q (h ^ idx * shift)"
    using composition_table eval_domain_nth[OF idx_bound] idx_bound eval_domain_length
    by simp
  have trace_powers:
    "map ((!) trace_table) (powers_scaled idx) =
      map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f)"
    by (rule query_values_trace_powers[OF trace_table])
      (rule query_sample_space_powers_scaled_bound[OF idx_in])
  have mult:
    "poly common_denominator_poly (h ^ idx * shift) *
      cp_eval as
        (map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f))
        (h ^ idx * shift) =
      poly (common_denominator_numerator f as) (h ^ idx * shift)"
    by (rule common_denominator_mult_cp_eval_trace_powers[OF idx_bound])
  have denom_nonzero:
    "poly common_denominator_poly (h ^ idx * shift) \<noteq> 0"
    by (rule common_denominator_nonzero_on_eval_domain[OF idx_bound])
  have residual_eval:
    "poly (common_denominator_numerator f as) (h ^ idx * shift) =
      poly common_denominator_poly (h ^ idx * shift) *
        poly q (h ^ idx * shift)"
    using residual_zero by simp
  have cp_eq:
    "cp_eval as
        (map (\<lambda>p. poly p (h ^ idx * shift)) (trace_powers_of f))
        (h ^ idx * shift) =
      poly q (h ^ idx * shift)"
    using mult residual_eval denom_nonzero by simp
  show ?thesis
    unfolding query_consistent_at_def
    using idx_bound trace_len comp_len powers_bound comp_value trace_powers cp_eq
    by simp
qed

lemma all_queries_consistent_from_common_denominator_residual_zero:
  assumes trace_table: "trace_table = map (poly f) eval_domain"
    and composition_table: "composition_table = map (poly q) eval_domain"
    and residual_zero:
      "common_denominator_numerator f as - common_denominator_poly * q = 0"
  shows "all_queries_consistent trace_table composition_table as"
  unfolding all_queries_consistent_def
  using query_consistent_at_from_common_denominator_residual_zero
    [OF trace_table composition_table residual_zero]
  by blast

lemma common_denominator_residual_nonzero_from_query_disagreement:
  assumes trace_table: "trace_table = map (poly f) eval_domain"
    and composition_table: "composition_table = map (poly q) eval_domain"
    and not_all: "\<not> all_queries_consistent trace_table composition_table as"
  shows "common_denominator_numerator f as - common_denominator_poly * q \<noteq> 0"
proof
  assume zero:
    "common_denominator_numerator f as - common_denominator_poly * q = 0"
  have "all_queries_consistent trace_table composition_table as"
    by (rule all_queries_consistent_from_common_denominator_residual_zero
        [OF trace_table composition_table zero])
  then show False
    using not_all by simp
qed

lemma query_agreement_indices_card_bound:
  assumes trace_low: "trace_table_low_degree trace_table"
    and composition_low:
      "composition_table_low_degree maxDegree composition_table"
    and not_all:
      "\<not> all_queries_consistent trace_table composition_table as"
  shows "card (query_agreement_indices trace_table composition_table as) \<le>
    query_agreement_bound"
proof -
  from trace_low obtain f where deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    unfolding trace_table_low_degree_def by blast
  from composition_low obtain q where deg_q: "degree q \<le> maxDegree"
    and composition_table: "composition_table = map (poly q) eval_domain"
    unfolding composition_table_low_degree_def by blast
  let ?A = "query_agreement_indices trace_table composition_table as"
  let ?R = "common_denominator_numerator f as - common_denominator_poly * q"
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
  have residual_nonzero:
    "?R \<noteq> 0"
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
    have "poly (common_denominator_numerator f as) (h ^ idx * shift) =
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
    by (rule card_mono[OF poly_roots_finite[OF residual_nonzero] image_subset])
  also have "... \<le> degree ?R"
    by (rule card_poly_roots_bound[OF residual_nonzero])
  also have "... \<le> query_agreement_bound"
    by (rule common_denominator_residual_degree_le_bound[OF deg_f deg_q])
  finally show ?thesis .
qed

end

end
