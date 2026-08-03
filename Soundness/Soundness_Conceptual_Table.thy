(*  Title:      Stark/Soundness_Conceptual_Table.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Conceptual_Table
  imports Soundness_Partial_Merkle
begin

text \<open>
  Conceptual Merkle tables.

  This layer deliberately does not reconstruct a complete \<^term>\<open>created_tree\<close>
  witness from sampled openings.  Instead it records the value that is uniquely
  authenticated for a root, length, and index in a hash-map state.  Values at
  unauthenticated indices are arbitrary Hilbert-choice defaults; later proofs
  must only use them after showing agreement with authenticated openings or
  charging disagreement to a Merkle/hash side event.

  The intended prefix-fixed use is to build these tables from the query-prefix
  oracle state, before the query-index challenge is sampled.  Later openings
  checked by the verifier are handled in a downstream layer via pullback or
  controlled collision/inconsistency events.
\<close>

context soundness
begin

definition authenticated_value_at
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f \<Rightarrow> bool"
where
  "authenticated_value_at s r len i v \<longleftrightarrow>
    (\<exists>opn :: 'f authenticated_opening.
      authenticated_opening_in s opn \<and>
      opening_root opn = r \<and>
      opening_length opn = len \<and>
      opening_index opn = i \<and>
      opening_value opn = v)"

lemma authenticated_value_atI:
  assumes "authenticated_opening_in s opn"
    and "opening_root opn = r"
    and "opening_length opn = len"
    and "opening_index opn = i"
    and "opening_value opn = v"
  shows "authenticated_value_at s r len i v"
  using assms unfolding authenticated_value_at_def by blast

lemma authenticated_value_atE:
  assumes "authenticated_value_at s r len i v"
  obtains opn where
    "authenticated_opening_in s opn"
    "opening_root opn = r"
    "opening_length opn = len"
    "opening_index opn = i"
    "opening_value opn = v"
  using assms unfolding authenticated_value_at_def by blast

lemma authenticated_value_at_unique_if_clean:
  assumes clean: "\<not> hash_map_output_collision s"
    and v: "authenticated_value_at s r len i v"
    and v': "authenticated_value_at s r len i v'"
  shows "v = v'"
proof -
  from authenticated_value_atE[OF v] obtain opn where
    auth: "authenticated_opening_in s opn"
    and root: "opening_root opn = r"
    and len_eq: "opening_length opn = len"
    and idx: "opening_index opn = i"
    and val: "opening_value opn = v"
    by blast
  from authenticated_value_atE[OF v'] obtain opn' where
    auth': "authenticated_opening_in s opn'"
    and root': "opening_root opn' = r"
    and len_eq': "opening_length opn' = len"
    and idx': "opening_index opn' = i"
    and val': "opening_value opn' = v'"
    by blast
  show ?thesis
  proof (rule ccontr)
    assume "v \<noteq> v'"
    then have diff: "opening_value opn \<noteq> opening_value opn'"
      using val val' by simp
    have collision: "hash_map_output_collision s"
      by (rule inconsistent_authenticated_openings_imp_hash_collision
          [OF auth auth'])
        (use root root' len_eq len_eq' idx idx' diff in simp_all)
    then show False
      using clean by contradiction
  qed
qed

lemma authenticated_value_at_mono:
  assumes v: "authenticated_value_at s r len i x"
    and ext: "s \<le> t"
  shows "authenticated_value_at t r len i x"
proof -
  from authenticated_value_atE[OF v] obtain opn where
    auth: "authenticated_opening_in s opn"
    and root: "opening_root opn = r"
    and len_eq: "opening_length opn = len"
    and idx: "opening_index opn = i"
    and val: "opening_value opn = x"
    by blast
  have "authenticated_opening_in t opn"
    by (rule authenticated_opening_in_mono[OF auth ext])
  then show ?thesis
    by (rule authenticated_value_atI[OF _ root len_eq idx val])
qed

definition conceptual_opening_value
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f"
where
  "conceptual_opening_value s r len i =
    (THE v. authenticated_value_at s r len i v)"

lemma conceptual_opening_value_eq_if_authenticated:
  assumes clean: "\<not> hash_map_output_collision s"
    and v: "authenticated_value_at s r len i x"
  shows "conceptual_opening_value s r len i = x"
  unfolding conceptual_opening_value_def
proof (rule the_equality)
  show "authenticated_value_at s r len i x"
    by (rule v)
next
  fix y
  assume "authenticated_value_at s r len i y"
  then show "y = x"
    using authenticated_value_at_unique_if_clean[OF clean _ v] by blast
qed

definition conceptual_table
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> 'f list"
where
  "conceptual_table s r len =
    map (conceptual_opening_value s r len) [0..<len]"

definition conceptual_opening_value_with_default
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow>
      'f \<Rightarrow> nat \<Rightarrow> 'f"
where
  "conceptual_opening_value_with_default s r len dflt i =
    (if \<exists>v. authenticated_value_at s r len i v
     then conceptual_opening_value s r len i
     else dflt)"

definition conceptual_table_with_default
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> 'f list"
where
  "conceptual_table_with_default s r len default_table =
    map (\<lambda>i. conceptual_opening_value_with_default s r len
      (default_table ! i) i) [0..<len]"

lemma length_conceptual_table[simp]:
  "length (conceptual_table s r len) = len"
  unfolding conceptual_table_def by simp

lemma length_conceptual_table_with_default[simp]:
  "length (conceptual_table_with_default s r len default_table) = len"
  unfolding conceptual_table_with_default_def by simp

lemma conceptual_table_nth:
  assumes "i < len"
  shows "conceptual_table s r len ! i = conceptual_opening_value s r len i"
  using assms unfolding conceptual_table_def by simp

lemma conceptual_table_with_default_nth:
  assumes "i < len"
  shows
    "conceptual_table_with_default s r len default_table ! i =
      conceptual_opening_value_with_default s r len (default_table ! i) i"
  using assms unfolding conceptual_table_with_default_def by simp

lemma conceptual_opening_value_with_default_eq_if_authenticated:
  assumes clean: "\<not> hash_map_output_collision s"
    and v: "authenticated_value_at s r len i x"
  shows "conceptual_opening_value_with_default s r len dflt i = x"
proof -
  have ex: "\<exists>v. authenticated_value_at s r len i v"
    using v by blast
  show ?thesis
    using ex conceptual_opening_value_eq_if_authenticated[OF clean v]
    unfolding conceptual_opening_value_with_default_def by simp
qed

lemma conceptual_opening_value_with_default_eq_default_if_not_authenticated:
  assumes "\<not> (\<exists>v. authenticated_value_at s r len i v)"
  shows "conceptual_opening_value_with_default s r len dflt i = dflt"
  using assms unfolding conceptual_opening_value_with_default_def
  by (auto split: if_splits)

lemma conceptual_table_with_default_eq_if_agrees_with_authenticated_values:
  assumes clean: "\<not> hash_map_output_collision s"
    and len_eq: "length default_table = len"
    and agrees:
      "\<And>i v. i < len \<Longrightarrow> authenticated_value_at s r len i v \<Longrightarrow>
        default_table ! i = v"
  shows "conceptual_table_with_default s r len default_table = default_table"
proof (rule nth_equalityI)
  show "length (conceptual_table_with_default s r len default_table) =
      length default_table"
    using len_eq by simp
next
  fix i
  assume i_bound:
    "i < length (conceptual_table_with_default s r len default_table)"
  then have i_len: "i < len"
    by simp
  show "conceptual_table_with_default s r len default_table ! i =
      default_table ! i"
  proof (cases "\<exists>v. authenticated_value_at s r len i v")
    case True
    then obtain v where v: "authenticated_value_at s r len i v"
      by blast
    have
      "conceptual_table_with_default s r len default_table ! i =
        conceptual_opening_value_with_default s r len (default_table ! i) i"
      by (rule conceptual_table_with_default_nth[OF i_len])
    also have "... = v"
      by (rule conceptual_opening_value_with_default_eq_if_authenticated
          [OF clean v])
    also have "... = default_table ! i"
      using agrees[OF i_len v] by simp
    finally show ?thesis .
  next
    case False
    have
      "conceptual_table_with_default s r len default_table ! i =
        conceptual_opening_value_with_default s r len (default_table ! i) i"
      by (rule conceptual_table_with_default_nth[OF i_len])
    also have "... = default_table ! i"
      by (rule
          conceptual_opening_value_with_default_eq_default_if_not_authenticated
          [OF False])
    finally show ?thesis .
  qed
qed

lemma conceptual_table_agrees_with_authenticated_opening:
  assumes clean: "\<not> hash_map_output_collision s"
    and auth: "authenticated_opening_in s opn"
    and root: "opening_root opn = r"
    and len_eq: "opening_length opn = len"
    and idx_bound: "opening_index opn < len"
  shows
    "conceptual_table s r len ! opening_index opn = opening_value opn"
proof -
  have v:
    "authenticated_value_at s r len (opening_index opn)
      (opening_value opn)"
    by (rule authenticated_value_atI[OF auth root len_eq refl refl])
  have "conceptual_table s r len ! opening_index opn =
      conceptual_opening_value s r len (opening_index opn)"
    by (rule conceptual_table_nth[OF idx_bound])
  also have "... = opening_value opn"
    by (rule conceptual_opening_value_eq_if_authenticated[OF clean v])
  finally show ?thesis .
qed

lemma conceptual_table_agrees_with_partial_authenticated_table:
  assumes clean: "\<not> hash_map_output_collision s"
    and table: "partial_authenticated_table r len openings s"
    and opn_in: "opn \<in> set openings"
  shows
    "conceptual_table s r len ! opening_index opn = opening_value opn"
proof -
  have auth: "authenticated_opening_in s opn"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have root: "opening_root opn = r"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have len_eq: "opening_length opn = len"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have idx_bound: "opening_index opn < len"
    using auth len_eq unfolding authenticated_opening_in_def by simp
  show ?thesis
    by (rule conceptual_table_agrees_with_authenticated_opening
        [OF clean auth root len_eq idx_bound])
qed

end

end
