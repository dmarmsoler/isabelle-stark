theory Soundness_FRI_Robust_Decoded_Semantics
  imports
    Stark.Soundness_FRI_Robust_Multiround
    Stark.Soundness_FRI_RO_Actual_Query_Trace_Composition_Boundary
    Stark.Soundness_FRI_Conditioned_Trace_Composition_Padding_Agreement
begin

context soundness
begin

definition decoded_trace_error_indices ::
  "'f list \<Rightarrow> 'f list \<Rightarrow> nat set"
where
  "decoded_trace_error_indices fri_table decoded =
    {idx \<in> query_sample_space. fri_table ! idx \<noteq> decoded ! idx}"

lemma finite_decoded_trace_error_indices[simp]:
  "finite (decoded_trace_error_indices fri_table decoded)"
  unfolding decoded_trace_error_indices_def query_sample_space_def by simp

lemma trace_composition_accepted_indices_decode_subset:
  "trace_composition_accepted_indices original fri_table composition as \<subseteq>
    trace_composition_accepted_indices original decoded composition as \<union>
      decoded_trace_error_indices fri_table decoded"
proof
  fix idx
  assume accepted:
    "idx \<in> trace_composition_accepted_indices
      original fri_table composition as"
  then have sample: "idx \<in> query_sample_space"
    and original_fri: "original ! idx = fri_table ! idx"
    and consistent: "query_consistent_at original composition as idx"
    unfolding trace_composition_accepted_indices_def
      trace_table_base_agreement_indices_def
    by auto
  show "idx \<in>
      trace_composition_accepted_indices original decoded composition as \<union>
      decoded_trace_error_indices fri_table decoded"
  proof (cases "fri_table ! idx = decoded ! idx")
    case True
    then have "original ! idx = decoded ! idx"
      using original_fri by simp
    then have
      "idx \<in> trace_table_base_agreement_indices original decoded"
      using sample unfolding trace_table_base_agreement_indices_def by simp
    then have
      "idx \<in> trace_composition_accepted_indices
        original decoded composition as"
      using consistent unfolding trace_composition_accepted_indices_def
      by simp
    then show ?thesis by simp
  next
    case False
    then have "idx \<in> decoded_trace_error_indices fri_table decoded"
      using sample unfolding decoded_trace_error_indices_def by simp
    then show ?thesis by simp
  qed
qed

lemma trace_composition_accepted_indices_decode_card_bound:
  assumes lengths: "length original = length decoded"
    and trace_low: "trace_table_low_degree decoded"
    and composition_low:
      "composition_table_low_degree maxDegree composition"
    and not_all:
      "\<not> all_queries_consistent decoded composition as"
  shows
    "card (trace_composition_accepted_indices
        original fri_table composition as)
      \<le> trace_composition_query_index_bound +
        card (decoded_trace_error_indices fri_table decoded)"
proof -
  let ?source =
    "trace_composition_accepted_indices original fri_table composition as"
  let ?decoded =
    "trace_composition_accepted_indices original decoded composition as"
  let ?errors = "decoded_trace_error_indices fri_table decoded"
  have subset: "?source \<subseteq> ?decoded \<union> ?errors"
    by (rule trace_composition_accepted_indices_decode_subset)
  have finite_decoded: "finite ?decoded"
    using trace_composition_accepted_indices_subset_query_sample_space
    by (rule finite_subset[OF _ finite_query_sample_space])
  have finite_union: "finite (?decoded \<union> ?errors)"
    using finite_decoded by simp
  have source_le: "card ?source \<le> card (?decoded \<union> ?errors)"
    by (rule card_mono[OF finite_union subset])
  have union_le: "card (?decoded \<union> ?errors) \<le> card ?decoded + card ?errors"
    by (rule card_Un_le)
  have decoded_le:
      "card ?decoded \<le> trace_composition_query_index_bound"
    by (rule trace_composition_accepted_indices_card_bound[
      OF lengths trace_low composition_low not_all])
  show ?thesis
    using source_le union_le decoded_le by linarith
qed

lemma trace_composition_accepted_indices_two_decodes_subset:
  assumes composition_lengths:
    "length composition_table = length decoded_composition"
  shows
    "trace_composition_accepted_indices
        original fri_table composition_table as \<subseteq>
      trace_composition_accepted_indices
        original decoded_trace decoded_composition as \<union>
      decoded_trace_error_indices fri_table decoded_trace \<union>
      decoded_trace_error_indices composition_table decoded_composition"
proof
  fix idx
  assume accepted:
    "idx \<in> trace_composition_accepted_indices
      original fri_table composition_table as"
  then have sample: "idx \<in> query_sample_space"
    and original_fri: "original ! idx = fri_table ! idx"
    and consistent:
      "query_consistent_at original composition_table as idx"
    unfolding trace_composition_accepted_indices_def
      trace_table_base_agreement_indices_def
    by auto
  show
    "idx \<in>
      trace_composition_accepted_indices
        original decoded_trace decoded_composition as \<union>
      decoded_trace_error_indices fri_table decoded_trace \<union>
      decoded_trace_error_indices composition_table decoded_composition"
  proof (cases "fri_table ! idx = decoded_trace ! idx")
    case False
    then have "idx \<in> decoded_trace_error_indices fri_table decoded_trace"
      using sample unfolding decoded_trace_error_indices_def by simp
    then show ?thesis by simp
  next
    case trace_equal: True
    show ?thesis
    proof (cases "composition_table ! idx = decoded_composition ! idx")
      case False
      then have
        "idx \<in> decoded_trace_error_indices
          composition_table decoded_composition"
        using sample unfolding decoded_trace_error_indices_def by simp
      then show ?thesis by simp
    next
      case composition_equal: True
      have original_decoded: "original ! idx = decoded_trace ! idx"
        using original_fri trace_equal by simp
      have decoded_consistent:
          "query_consistent_at original decoded_composition as idx"
      proof -
        have equivalence:
            "query_consistent_at original composition_table as idx \<longleftrightarrow>
             query_consistent_at original decoded_composition as idx"
          by (rule query_consistent_at_cong_opened_values)
            (use composition_lengths composition_equal in simp_all)
        show ?thesis using consistent equivalence by simp
      qed
      have base:
          "idx \<in> trace_table_base_agreement_indices original decoded_trace"
        using sample original_decoded
        unfolding trace_table_base_agreement_indices_def by simp
      have
          "idx \<in> trace_composition_accepted_indices
            original decoded_trace decoded_composition as"
        using base decoded_consistent
        unfolding trace_composition_accepted_indices_def by simp
      then show ?thesis by simp
    qed
  qed
qed

lemma trace_composition_accepted_indices_two_decodes_card_bound:
  assumes trace_lengths: "length original = length decoded_trace"
    and composition_lengths:
      "length composition_table = length decoded_composition"
    and trace_low: "trace_table_low_degree decoded_trace"
    and composition_low:
      "composition_table_low_degree maxDegree decoded_composition"
    and not_all:
      "\<not> all_queries_consistent decoded_trace decoded_composition as"
  shows
    "card (trace_composition_accepted_indices
        original fri_table composition_table as)
      \<le> trace_composition_query_index_bound +
        card (decoded_trace_error_indices fri_table decoded_trace) +
        card (decoded_trace_error_indices
          composition_table decoded_composition)"
proof -
  let ?source =
    "trace_composition_accepted_indices
      original fri_table composition_table as"
  let ?decoded =
    "trace_composition_accepted_indices
      original decoded_trace decoded_composition as"
  let ?trace_errors =
    "decoded_trace_error_indices fri_table decoded_trace"
  let ?composition_errors =
    "decoded_trace_error_indices composition_table decoded_composition"
  have subset:
      "?source \<subseteq> ?decoded \<union> ?trace_errors \<union> ?composition_errors"
    by (rule trace_composition_accepted_indices_two_decodes_subset[
      OF composition_lengths])
  have finite_decoded: "finite ?decoded"
    using trace_composition_accepted_indices_subset_query_sample_space
    by (rule finite_subset[OF _ finite_query_sample_space])
  have finite_union:
      "finite (?decoded \<union> ?trace_errors \<union> ?composition_errors)"
    using finite_decoded by simp
  have source_le:
      "card ?source \<le> card (?decoded \<union> ?trace_errors \<union> ?composition_errors)"
    by (rule card_mono[OF finite_union subset])
  have union_le:
      "card (?decoded \<union> ?trace_errors \<union> ?composition_errors)
        \<le> card ?decoded + card ?trace_errors + card ?composition_errors"
  proof -
    have
      "card (?decoded \<union> ?trace_errors \<union> ?composition_errors)
        \<le> card (?decoded \<union> ?trace_errors) + card ?composition_errors"
      by (rule card_Un_le)
    also have "... \<le>
        (card ?decoded + card ?trace_errors) + card ?composition_errors"
      using card_Un_le[of ?decoded ?trace_errors] by linarith
    finally show ?thesis .
  qed
  have decoded_le:
      "card ?decoded \<le> trace_composition_query_index_bound"
    by (rule trace_composition_accepted_indices_card_bound[
      OF trace_lengths trace_low composition_low not_all])
  show ?thesis
    using source_le union_le decoded_le by linarith
qed


lemma trace_composition_accepted_indices_two_decodes_padded_card_bound:
  assumes trace_lengths: "length original = length decoded_trace"
    and composition_lengths:
      "length composition_table = length decoded_composition"
    and trace_low: "trace_table_low_degree decoded_trace"
    and composition_low:
      "composition_table_low_degree composition_degree_bound
        decoded_composition"
    and composition_bad:
      "\<not> composition_table_low_degree maxDegree decoded_composition"
  shows
    "card (trace_composition_accepted_indices
        original fri_table composition_table as)
      \<le> trace_composition_query_index_bound_for composition_degree_bound +
        card (decoded_trace_error_indices fri_table decoded_trace) +
        card (decoded_trace_error_indices
          composition_table decoded_composition)"
proof -
  let ?source =
    "trace_composition_accepted_indices
      original fri_table composition_table as"
  let ?decoded =
    "trace_composition_accepted_indices
      original decoded_trace decoded_composition as"
  let ?trace_errors =
    "decoded_trace_error_indices fri_table decoded_trace"
  let ?composition_errors =
    "decoded_trace_error_indices composition_table decoded_composition"
  have subset:
      "?source \<subseteq> ?decoded \<union> ?trace_errors \<union> ?composition_errors"
    by (rule trace_composition_accepted_indices_two_decodes_subset[
      OF composition_lengths])
  have finite_decoded: "finite ?decoded"
    using trace_composition_accepted_indices_subset_query_sample_space
    by (rule finite_subset[OF _ finite_query_sample_space])
  have finite_union:
      "finite (?decoded \<union> ?trace_errors \<union> ?composition_errors)"
    using finite_decoded by simp
  have source_le:
      "card ?source \<le> card (?decoded \<union> ?trace_errors \<union> ?composition_errors)"
    by (rule card_mono[OF finite_union subset])
  have union_le:
      "card (?decoded \<union> ?trace_errors \<union> ?composition_errors)
        \<le> card ?decoded + card ?trace_errors + card ?composition_errors"
  proof -
    have
      "card (?decoded \<union> ?trace_errors \<union> ?composition_errors)
        \<le> card (?decoded \<union> ?trace_errors) + card ?composition_errors"
      by (rule card_Un_le)
    also have "... \<le>
        (card ?decoded + card ?trace_errors) + card ?composition_errors"
      using card_Un_le[of ?decoded ?trace_errors] by linarith
    finally show ?thesis .
  qed
  have decoded_le:
      "card ?decoded \<le>
        trace_composition_query_index_bound_for composition_degree_bound"
    by (rule trace_composition_accepted_indices_card_bound_for[
      OF trace_lengths trace_low composition_low composition_bad])
  show ?thesis
    using source_le union_le decoded_le by linarith
qed


definition fri_canonical_decoded_table :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list"
where
  "fri_canonical_decoded_table d table =
    map (fri_canonical_table_decoder d 0 table) [0..<length eval_domain]"

lemma length_fri_canonical_decoded_table[simp]:
  "length (fri_canonical_decoded_table d table) = length eval_domain"
  unfolding fri_canonical_decoded_table_def by simp

lemma fri_canonical_decoded_table_nth:
  assumes "i < length eval_domain"
  shows "fri_canonical_decoded_table d table ! i =
    fri_canonical_table_decoder d 0 table i"
  using assms unfolding fri_canonical_decoded_table_def by simp

lemma fri_canonical_decoded_table_code:
  "fri_canonical_decoded_table d table \<in>
    fri_rs_code_tables (fri_padded_degree_bound d) eval_domain"
proof -
  have decoder_code:
      "fri_canonical_table_decoder d 0 table \<in>
        fri_rs_code_functions (fri_padded_degree_bound d) eval_domain"
    unfolding fri_canonical_table_decoder_def fri_canonical_domain_at_0
    by (simp add: fri_rs_canonical_decoder_code)
  from decoder_code obtain code_table where
    code_table:
      "code_table \<in>
        fri_rs_code_tables (fri_padded_degree_bound d) eval_domain"
    and decoder_eq:
      "fri_canonical_table_decoder d 0 table = nth code_table"
    unfolding fri_rs_code_functions_def by blast
  have code_length: "length code_table = length eval_domain"
    by (rule fri_rs_code_tables_length[OF code_table])
  have decoded_eq: "fri_canonical_decoded_table d table = code_table"
  proof (rule nth_equalityI)
    show "length (fri_canonical_decoded_table d table) = length code_table"
      using code_length by simp
  next
    fix i
    assume i_bound: "i < length (fri_canonical_decoded_table d table)"
    then have eval_bound: "i < length eval_domain"
      by simp
    show "fri_canonical_decoded_table d table ! i = code_table ! i"
      unfolding fri_canonical_decoded_table_nth[OF eval_bound] decoder_eq
      by simp
  qed
  show ?thesis
    unfolding decoded_eq by (rule code_table)
qed

lemma fri_canonical_decoded_table_composition_low_degree:
  "composition_table_low_degree (fri_padded_degree_bound d)
    (fri_canonical_decoded_table d table)"
proof -
  from fri_canonical_decoded_table_code[
      of d table]
  obtain p where
    degree: "degree p \<le> fri_padded_degree_bound d"
    and table:
      "fri_canonical_decoded_table d table = map (poly p) eval_domain"
    unfolding fri_rs_code_tables_def by blast
  show ?thesis
    unfolding composition_table_low_degree_def
    using degree table by blast
qed

lemma fri_canonical_decoded_trace_table_low_degree:
  "trace_table_low_degree
    (fri_canonical_decoded_table (clength - 1) table)"
proof -
  from fri_canonical_decoded_table_code[
      of "clength - 1" table]
  obtain p where
    degree: "degree p \<le> fri_padded_degree_bound (clength - 1)"
    and table:
      "fri_canonical_decoded_table (clength - 1) table =
        map (poly p) eval_domain"
    unfolding fri_rs_code_tables_def by blast
  have padded:
      "fri_padded_degree_bound (clength - 1) = clength - 1"
    by (rule fri_padded_degree_bound_clength_pred)
  have degree_lt: "degree p < clength"
    using degree clength_pos unfolding padded by linarith
  show ?thesis
    unfolding trace_table_low_degree_def
    using degree_lt table by blast
qed

lemma card_decoded_trace_error_indices_canonical_le_distance:
  "card (decoded_trace_error_indices
      table (fri_canonical_decoded_table d table))
    \<le> fri_rs_distance_to_code (fri_padded_degree_bound d)
        eval_domain (nth table)"
proof -
  let ?decoder = "fri_canonical_table_decoder d 0 table"
  let ?errors =
    "decoded_trace_error_indices
      table (fri_canonical_decoded_table d table)"
  let ?global =
    "code_disagreement_indices {..<length eval_domain} (nth table) ?decoder"
  have subset: "?errors \<subseteq> ?global"
  proof
    fix i
    assume i_error: "i \<in> ?errors"
    then have sample: "i \<in> query_sample_space"
      and differs:
        "table ! i \<noteq> fri_canonical_decoded_table d table ! i"
      unfolding decoded_trace_error_indices_def by blast+
    have i_bound: "i < length eval_domain"
      using query_sample_space_less_domain[OF sample] eval_domain_length
      by simp
    have decoder_at:
        "fri_canonical_decoded_table d table ! i = ?decoder i"
      by (rule fri_canonical_decoded_table_nth[OF i_bound])
    show "i \<in> ?global"
      using i_bound differs decoder_at
      unfolding code_disagreement_indices_def by simp
  qed
  have finite_global: "finite ?global"
    by (rule finite_code_disagreement_indices) simp
  have card_le: "card ?errors \<le> card ?global"
    by (rule card_mono[OF finite_global subset])
  have exact:
      "card ?global =
        fri_rs_distance_to_code (fri_padded_degree_bound d)
          eval_domain (nth table)"
    using fri_rs_canonical_decoder_spec[
      of "fri_padded_degree_bound d" eval_domain "nth table"]
    unfolding fri_canonical_table_decoder_def fri_canonical_domain_at_0
    by simp
  show ?thesis
    using card_le exact by simp
qed

lemma card_decoded_trace_error_indices_canonical_le_radius:
  assumes close:
    "fri_rs_distance_to_code (fri_padded_degree_bound d)
      eval_domain (nth table) \<le> radius"
  shows
    "card (decoded_trace_error_indices
      table (fri_canonical_decoded_table d table)) \<le> radius"
  by (rule order_trans[
    OF card_decoded_trace_error_indices_canonical_le_distance close])


theorem robust_two_decodes_semantic_trichotomy:
  assumes original_length: "length original = length eval_domain"
    and composition_length: "length composition_table = length eval_domain"
    and trace_close:
      "fri_rs_distance_to_code (fri_padded_degree_bound (clength - 1))
        eval_domain (nth fri_table) \<le> trace_radius"
    and composition_close:
      "fri_rs_distance_to_code (fri_padded_degree_bound d)
        eval_domain (nth composition_table) \<le> composition_radius"
  defines
    "decoded_trace \<equiv>
      fri_canonical_decoded_table (clength - 1) fri_table"
    and
    "decoded_composition \<equiv>
      fri_canonical_decoded_table d composition_table"
  shows
    "(\<not> composition_table_low_degree maxDegree decoded_composition \<and>
       card (trace_composition_accepted_indices
          original fri_table composition_table as)
        \<le> trace_composition_query_index_bound_for
            (fri_padded_degree_bound d) +
          trace_radius + composition_radius) \<or>
     (composition_table_low_degree maxDegree decoded_composition \<and>
       \<not> all_queries_consistent decoded_trace decoded_composition as \<and>
       card (trace_composition_accepted_indices
          original fri_table composition_table as)
        \<le> trace_composition_query_index_bound +
          trace_radius + composition_radius) \<or>
     (composition_table_low_degree maxDegree decoded_composition \<and>
       all_queries_consistent decoded_trace decoded_composition as)"
proof -
  have trace_length:
      "length original = length decoded_trace"
    unfolding decoded_trace_def using original_length by simp
  have composition_lengths:
      "length composition_table = length decoded_composition"
    unfolding decoded_composition_def using composition_length by simp
  have trace_low: "trace_table_low_degree decoded_trace"
    unfolding decoded_trace_def
    by (rule fri_canonical_decoded_trace_table_low_degree)
  have composition_padded:
      "composition_table_low_degree (fri_padded_degree_bound d)
        decoded_composition"
    unfolding decoded_composition_def
    by (rule fri_canonical_decoded_table_composition_low_degree)
  have trace_errors:
      "card (decoded_trace_error_indices fri_table decoded_trace) \<le>
        trace_radius"
    unfolding decoded_trace_def
    by (rule card_decoded_trace_error_indices_canonical_le_radius[
      OF trace_close])
  have composition_errors:
      "card (decoded_trace_error_indices
        composition_table decoded_composition) \<le> composition_radius"
    unfolding decoded_composition_def
    by (rule card_decoded_trace_error_indices_canonical_le_radius[
      OF composition_close])
  show ?thesis
  proof (cases
      "composition_table_low_degree maxDegree decoded_composition")
    case False
    have accepted:
        "card (trace_composition_accepted_indices
            original fri_table composition_table as)
          \<le> trace_composition_query_index_bound_for
              (fri_padded_degree_bound d) +
            card (decoded_trace_error_indices fri_table decoded_trace) +
            card (decoded_trace_error_indices
              composition_table decoded_composition)"
      by (rule trace_composition_accepted_indices_two_decodes_padded_card_bound[
        OF trace_length composition_lengths trace_low composition_padded
          False])
    have
        "card (trace_composition_accepted_indices
            original fri_table composition_table as)
          \<le> trace_composition_query_index_bound_for
              (fri_padded_degree_bound d) +
            trace_radius + composition_radius"
      using accepted trace_errors composition_errors by linarith
    then show ?thesis
      using False by blast
  next
    case composition_low: True
    show ?thesis
    proof (cases
        "all_queries_consistent decoded_trace decoded_composition as")
      case True
      then show ?thesis
        using composition_low by blast
    next
      case False
      have accepted:
          "card (trace_composition_accepted_indices
              original fri_table composition_table as)
            \<le> trace_composition_query_index_bound +
              card (decoded_trace_error_indices fri_table decoded_trace) +
              card (decoded_trace_error_indices
                composition_table decoded_composition)"
        by (rule trace_composition_accepted_indices_two_decodes_card_bound[
          OF trace_length composition_lengths trace_low composition_low
            False])
      have
          "card (trace_composition_accepted_indices
              original fri_table composition_table as)
            \<le> trace_composition_query_index_bound +
              trace_radius + composition_radius"
        using accepted trace_errors composition_errors by linarith
      then show ?thesis
        using composition_low False by blast
    qed
  qed
qed


end
end
