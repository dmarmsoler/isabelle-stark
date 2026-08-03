(*  Title:      Stark/Soundness_Conceptual_Query_Prefix.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Conceptual_Query_Prefix
  imports Soundness_Conceptual_Table
begin

text \<open>
  Prefix-fixed conceptual tables.

  These tables are built from a staged query-prefix state, i.e. after the
  transcript prefix and earlier query rounds have been processed, but before
  the next query-index challenge is sampled.  This is the state selection
  needed for later dynamic query-target bounds.
\<close>

context soundness
begin

definition query_prefix_trace_conceptual_table
  :: "'f staged_query_prefix_data \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list"
where
  "query_prefix_trace_conceptual_table prefix s =
    conceptual_table s (sqp_trace_root prefix) (scale * clength)"

definition query_prefix_composition_conceptual_table
  :: "'f staged_query_prefix_data \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list"
where
  "query_prefix_composition_conceptual_table prefix s =
    conceptual_table s (hd (sqp_composition_fri_roots prefix))
      (scale * clength)"

definition query_prefix_trace_conceptual_table_with_default
  :: "'f staged_query_prefix_data \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list \<Rightarrow> 'f list"
where
  "query_prefix_trace_conceptual_table_with_default prefix s default_table =
    conceptual_table_with_default s (sqp_trace_root prefix)
      (scale * clength) default_table"

definition query_prefix_composition_conceptual_table_with_default
  :: "'f staged_query_prefix_data \<Rightarrow>
      ('f, 'a) protocol_channel_scheme \<Rightarrow> 'f list \<Rightarrow> 'f list"
where
  "query_prefix_composition_conceptual_table_with_default prefix s
      default_table =
    conceptual_table_with_default s (hd (sqp_composition_fri_roots prefix))
      (scale * clength) default_table"

lemma length_query_prefix_trace_conceptual_table[simp]:
  "length (query_prefix_trace_conceptual_table prefix s) = scale * clength"
  unfolding query_prefix_trace_conceptual_table_def by simp

lemma length_query_prefix_composition_conceptual_table[simp]:
  "length (query_prefix_composition_conceptual_table prefix s) =
    scale * clength"
  unfolding query_prefix_composition_conceptual_table_def by simp

lemma length_query_prefix_trace_conceptual_table_with_default[simp]:
  "length
    (query_prefix_trace_conceptual_table_with_default prefix s
      default_table) = scale * clength"
  unfolding query_prefix_trace_conceptual_table_with_default_def by simp

lemma length_query_prefix_composition_conceptual_table_with_default[simp]:
  "length
    (query_prefix_composition_conceptual_table_with_default prefix s
      default_table) = scale * clength"
  unfolding query_prefix_composition_conceptual_table_with_default_def
  by simp

lemma query_prefix_trace_conceptual_table_agrees_with_authenticated_opening:
  assumes clean: "\<not> hash_map_output_collision s"
    and auth: "authenticated_opening_in s opn"
    and root: "opening_root opn = sqp_trace_root prefix"
    and len_eq: "opening_length opn = scale * clength"
    and idx_bound: "opening_index opn < scale * clength"
  shows
    "query_prefix_trace_conceptual_table prefix s ! opening_index opn =
      opening_value opn"
  unfolding query_prefix_trace_conceptual_table_def
  by (rule conceptual_table_agrees_with_authenticated_opening
      [OF clean auth root len_eq idx_bound])

lemma query_prefix_composition_conceptual_table_agrees_with_authenticated_opening:
  assumes clean: "\<not> hash_map_output_collision s"
    and auth: "authenticated_opening_in s opn"
    and roots_nonempty: "sqp_composition_fri_roots prefix \<noteq> []"
    and root: "opening_root opn = hd (sqp_composition_fri_roots prefix)"
    and len_eq: "opening_length opn = scale * clength"
    and idx_bound: "opening_index opn < scale * clength"
  shows
    "query_prefix_composition_conceptual_table prefix s !
      opening_index opn = opening_value opn"
  unfolding query_prefix_composition_conceptual_table_def
  by (rule conceptual_table_agrees_with_authenticated_opening
      [OF clean auth root len_eq idx_bound])

lemma
  query_prefix_trace_conceptual_table_with_default_agrees_with_authenticated_opening:
  assumes clean: "\<not> hash_map_output_collision s"
    and auth: "authenticated_opening_in s opn"
    and root: "opening_root opn = sqp_trace_root prefix"
    and len_eq: "opening_length opn = scale * clength"
    and idx_bound: "opening_index opn < scale * clength"
  shows
    "query_prefix_trace_conceptual_table_with_default prefix s
      default_table ! opening_index opn =
      opening_value opn"
proof -
  have v:
    "authenticated_value_at s (sqp_trace_root prefix) (scale * clength)
      (opening_index opn) (opening_value opn)"
    by (rule authenticated_value_atI[OF auth root len_eq refl refl])
  have
    "query_prefix_trace_conceptual_table_with_default prefix s
      default_table ! opening_index opn =
      conceptual_opening_value_with_default s (sqp_trace_root prefix)
        (scale * clength) (default_table ! opening_index opn)
        (opening_index opn)"
    unfolding query_prefix_trace_conceptual_table_with_default_def
    by (rule conceptual_table_with_default_nth[OF idx_bound])
  also have "... = opening_value opn"
    by (rule conceptual_opening_value_with_default_eq_if_authenticated
        [OF clean v])
  finally show ?thesis .
qed

lemma
  query_prefix_composition_conceptual_table_with_default_agrees_with_authenticated_opening:
  assumes clean: "\<not> hash_map_output_collision s"
    and auth: "authenticated_opening_in s opn"
    and root: "opening_root opn = hd (sqp_composition_fri_roots prefix)"
    and len_eq: "opening_length opn = scale * clength"
    and idx_bound: "opening_index opn < scale * clength"
  shows
    "query_prefix_composition_conceptual_table_with_default prefix s
      default_table ! opening_index opn =
      opening_value opn"
proof -
  have v:
    "authenticated_value_at s (hd (sqp_composition_fri_roots prefix))
      (scale * clength) (opening_index opn) (opening_value opn)"
    by (rule authenticated_value_atI[OF auth root len_eq refl refl])
  have
    "query_prefix_composition_conceptual_table_with_default prefix s
      default_table ! opening_index opn =
      conceptual_opening_value_with_default s
        (hd (sqp_composition_fri_roots prefix)) (scale * clength)
        (default_table ! opening_index opn) (opening_index opn)"
    unfolding query_prefix_composition_conceptual_table_with_default_def
    by (rule conceptual_table_with_default_nth[OF idx_bound])
  also have "... = opening_value opn"
    by (rule conceptual_opening_value_with_default_eq_if_authenticated
        [OF clean v])
  finally show ?thesis .
qed

lemma query_prefix_trace_conceptual_table_agrees_with_partial_authenticated_table:
  assumes clean: "\<not> hash_map_output_collision s"
    and table:
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) openings s"
    and opn_in: "opn \<in> set openings"
  shows
    "query_prefix_trace_conceptual_table prefix s ! opening_index opn =
      opening_value opn"
  unfolding query_prefix_trace_conceptual_table_def
  by (rule conceptual_table_agrees_with_partial_authenticated_table
      [OF clean table opn_in])

lemma
  query_prefix_composition_conceptual_table_agrees_with_partial_authenticated_table:
  assumes clean: "\<not> hash_map_output_collision s"
    and table:
      "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) openings s"
    and opn_in: "opn \<in> set openings"
  shows
    "query_prefix_composition_conceptual_table prefix s ! opening_index opn =
      opening_value opn"
  unfolding query_prefix_composition_conceptual_table_def
  by (rule conceptual_table_agrees_with_partial_authenticated_table
      [OF clean table opn_in])

lemma
  query_prefix_trace_conceptual_table_with_default_agrees_with_partial_authenticated_table:
  assumes clean: "\<not> hash_map_output_collision s"
    and table:
      "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) openings s"
    and opn_in: "opn \<in> set openings"
  shows
    "query_prefix_trace_conceptual_table_with_default prefix s
      default_table ! opening_index opn =
      opening_value opn"
proof -
  have auth: "authenticated_opening_in s opn"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have root: "opening_root opn = sqp_trace_root prefix"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have len_eq: "opening_length opn = scale * clength"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have idx_bound: "opening_index opn < scale * clength"
    using auth len_eq unfolding authenticated_opening_in_def by simp
  show ?thesis
    by (rule
        query_prefix_trace_conceptual_table_with_default_agrees_with_authenticated_opening
        [OF clean auth root len_eq idx_bound])
qed

lemma
  query_prefix_composition_conceptual_table_with_default_agrees_with_partial_authenticated_table:
  assumes clean: "\<not> hash_map_output_collision s"
    and table:
      "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) openings s"
    and opn_in: "opn \<in> set openings"
  shows
    "query_prefix_composition_conceptual_table_with_default prefix s
      default_table ! opening_index opn =
      opening_value opn"
proof -
  have auth: "authenticated_opening_in s opn"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have root: "opening_root opn = hd (sqp_composition_fri_roots prefix)"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have len_eq: "opening_length opn = scale * clength"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have idx_bound: "opening_index opn < scale * clength"
    using auth len_eq unfolding authenticated_opening_in_def by simp
  show ?thesis
    by (rule
        query_prefix_composition_conceptual_table_with_default_agrees_with_authenticated_opening
          [OF clean auth root len_eq idx_bound])
qed

lemma query_prefix_trace_conceptual_table_with_default_eq_default_if_agrees_with_authenticated_values:
  assumes clean: "\<not> hash_map_output_collision s"
    and len_eq: "length default_table = scale * clength"
    and agrees:
      "\<And>i v. i < scale * clength \<Longrightarrow>
        authenticated_value_at s (sqp_trace_root prefix)
          (scale * clength) i v \<Longrightarrow>
        default_table ! i = v"
  shows
    "query_prefix_trace_conceptual_table_with_default prefix s
      default_table = default_table"
  unfolding query_prefix_trace_conceptual_table_with_default_def
  by (rule conceptual_table_with_default_eq_if_agrees_with_authenticated_values
      [OF clean len_eq agrees])

lemma query_prefix_composition_conceptual_table_with_default_eq_default_if_agrees_with_authenticated_values:
  assumes clean: "\<not> hash_map_output_collision s"
    and len_eq: "length default_table = scale * clength"
    and agrees:
      "\<And>i v. i < scale * clength \<Longrightarrow>
        authenticated_value_at s (hd (sqp_composition_fri_roots prefix))
          (scale * clength) i v \<Longrightarrow>
        default_table ! i = v"
  shows
    "query_prefix_composition_conceptual_table_with_default prefix s
      default_table = default_table"
  unfolding query_prefix_composition_conceptual_table_with_default_def
  by (rule conceptual_table_with_default_eq_if_agrees_with_authenticated_values
      [OF clean len_eq agrees])

lemma query_prefix_trace_conceptual_table_partial_trace_candidate:
  assumes clean: "\<not> hash_map_output_collision s"
    and len: "length trace_openings = rounds"
    and tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table (sqp_trace_root prefix)
          (scale * clength) (trace_openings ! i) s"
  shows
    "partial_trace_table_candidate
      (query_prefix_trace_conceptual_table prefix s) trace_openings"
  unfolding partial_trace_table_candidate_def
proof (intro conjI allI impI)
  show "length (query_prefix_trace_conceptual_table prefix s) =
    scale * clength"
    by simp
next
  show "length trace_openings = rounds"
    by (rule len)
next
  fix i
  assume i_bound: "i < rounds"
  show
    "table_agrees_with_authenticated_openings
      (query_prefix_trace_conceptual_table prefix s) (scale * clength)
      (trace_openings ! i)"
    unfolding table_agrees_with_authenticated_openings_def
  proof (intro conjI ballI)
    show "length (query_prefix_trace_conceptual_table prefix s) =
      scale * clength"
      by simp
  next
    fix opn
    assume opn_in: "opn \<in> set (trace_openings ! i)"
    have table: "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) (trace_openings ! i) s"
      by (rule tables[OF i_bound])
    show "opening_index opn < scale * clength"
      using table opn_in
      unfolding partial_authenticated_table_def authenticated_opening_in_def
      by auto
  next
    fix opn
    assume opn_in: "opn \<in> set (trace_openings ! i)"
    have table: "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) (trace_openings ! i) s"
      by (rule tables[OF i_bound])
    show
      "query_prefix_trace_conceptual_table prefix s ! opening_index opn =
        opening_value opn"
      by (rule
          query_prefix_trace_conceptual_table_agrees_with_partial_authenticated_table
          [OF clean table opn_in])
  qed
qed

lemma query_prefix_trace_conceptual_table_with_default_partial_trace_candidate:
  assumes clean: "\<not> hash_map_output_collision s"
    and len: "length trace_openings = rounds"
    and tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table (sqp_trace_root prefix)
          (scale * clength) (trace_openings ! i) s"
  shows
    "partial_trace_table_candidate
      (query_prefix_trace_conceptual_table_with_default prefix s
        default_table) trace_openings"
  unfolding partial_trace_table_candidate_def
proof (intro conjI allI impI)
  show
    "length
      (query_prefix_trace_conceptual_table_with_default prefix s
        default_table) =
      scale * clength"
    by simp
next
  show "length trace_openings = rounds"
    by (rule len)
next
  fix i
  assume i_bound: "i < rounds"
  show
    "table_agrees_with_authenticated_openings
      (query_prefix_trace_conceptual_table_with_default prefix s
        default_table)
      (scale * clength) (trace_openings ! i)"
    unfolding table_agrees_with_authenticated_openings_def
  proof (intro conjI ballI)
    show
      "length
        (query_prefix_trace_conceptual_table_with_default prefix s
          default_table) =
        scale * clength"
      by simp
  next
    fix opn
    assume opn_in: "opn \<in> set (trace_openings ! i)"
    have table: "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) (trace_openings ! i) s"
      by (rule tables[OF i_bound])
    show "opening_index opn < scale * clength"
      using table opn_in
      unfolding partial_authenticated_table_def authenticated_opening_in_def
      by auto
  next
    fix opn
    assume opn_in: "opn \<in> set (trace_openings ! i)"
    have table: "partial_authenticated_table (sqp_trace_root prefix)
        (scale * clength) (trace_openings ! i) s"
      by (rule tables[OF i_bound])
    show
      "query_prefix_trace_conceptual_table_with_default prefix s
        default_table ! opening_index opn =
        opening_value opn"
      by (rule
          query_prefix_trace_conceptual_table_with_default_agrees_with_partial_authenticated_table
          [OF clean table opn_in])
  qed
qed

lemma query_prefix_composition_conceptual_table_partial_composition_candidate:
  assumes clean: "\<not> hash_map_output_collision s"
    and len: "length composition_openings = rounds"
    and tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
          (scale * clength) (composition_openings ! i) s"
  shows
    "partial_composition_table_candidate
      (query_prefix_composition_conceptual_table prefix s)
      composition_openings"
  unfolding partial_composition_table_candidate_def
proof (intro conjI allI impI)
  show
    "length (query_prefix_composition_conceptual_table prefix s) =
      scale * clength"
    by simp
next
  show "length composition_openings = rounds"
    by (rule len)
next
  fix i
  assume i_bound: "i < rounds"
  show
    "table_agrees_with_authenticated_openings
      (query_prefix_composition_conceptual_table prefix s)
      (scale * clength) (composition_openings ! i)"
    unfolding table_agrees_with_authenticated_openings_def
  proof (intro conjI ballI)
    show
      "length (query_prefix_composition_conceptual_table prefix s) =
        scale * clength"
      by simp
  next
    fix opn
    assume opn_in: "opn \<in> set (composition_openings ! i)"
    have table:
      "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) (composition_openings ! i) s"
      by (rule tables[OF i_bound])
    show "opening_index opn < scale * clength"
      using table opn_in
      unfolding partial_authenticated_table_def authenticated_opening_in_def
      by auto
  next
    fix opn
    assume opn_in: "opn \<in> set (composition_openings ! i)"
    have table:
      "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) (composition_openings ! i) s"
      by (rule tables[OF i_bound])
    show
      "query_prefix_composition_conceptual_table prefix s !
        opening_index opn = opening_value opn"
      by (rule
          query_prefix_composition_conceptual_table_agrees_with_partial_authenticated_table
          [OF clean table opn_in])
  qed
qed

lemma
  query_prefix_composition_conceptual_table_with_default_partial_composition_candidate:
  assumes clean: "\<not> hash_map_output_collision s"
    and len: "length composition_openings = rounds"
    and tables:
      "\<And>i. i < rounds \<Longrightarrow>
        partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
          (scale * clength) (composition_openings ! i) s"
  shows
    "partial_composition_table_candidate
      (query_prefix_composition_conceptual_table_with_default prefix s
        default_table)
      composition_openings"
  unfolding partial_composition_table_candidate_def
proof (intro conjI allI impI)
  show
    "length
      (query_prefix_composition_conceptual_table_with_default prefix s
        default_table) =
      scale * clength"
    by simp
next
  show "length composition_openings = rounds"
    by (rule len)
next
  fix i
  assume i_bound: "i < rounds"
  show
    "table_agrees_with_authenticated_openings
      (query_prefix_composition_conceptual_table_with_default prefix s
        default_table)
      (scale * clength) (composition_openings ! i)"
    unfolding table_agrees_with_authenticated_openings_def
  proof (intro conjI ballI)
    show
      "length
        (query_prefix_composition_conceptual_table_with_default prefix s
          default_table) =
        scale * clength"
      by simp
  next
    fix opn
    assume opn_in: "opn \<in> set (composition_openings ! i)"
    have table:
      "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) (composition_openings ! i) s"
      by (rule tables[OF i_bound])
    show "opening_index opn < scale * clength"
      using table opn_in
      unfolding partial_authenticated_table_def authenticated_opening_in_def
      by auto
  next
    fix opn
    assume opn_in: "opn \<in> set (composition_openings ! i)"
    have table:
      "partial_authenticated_table (hd (sqp_composition_fri_roots prefix))
        (scale * clength) (composition_openings ! i) s"
      by (rule tables[OF i_bound])
    show
      "query_prefix_composition_conceptual_table_with_default prefix s
        default_table ! opening_index opn =
        opening_value opn"
      by (rule
          query_prefix_composition_conceptual_table_with_default_agrees_with_partial_authenticated_table
          [OF clean table opn_in])
  qed
qed

end

end
