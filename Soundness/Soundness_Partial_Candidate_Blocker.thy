(*  Title:      Stark/Soundness_Partial_Candidate_Blocker.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Partial_Candidate_Blocker
  imports Soundness_Partial_Merkle
begin

text \<open>
  Diagnostic lemmas for the remaining query-bound route.

  Partial authenticated openings constrain only the opened indices.  Without a
  separate Merkle-binding/completion theorem, the corresponding partial table
  candidate sets are not singleton in general: unopened positions can be
  changed while preserving all partial-opening evidence.
\<close>

context soundness
begin

lemma table_agrees_with_authenticated_openings_update_unopened:
  assumes agrees:
      "table_agrees_with_authenticated_openings table len openings"
    and unopened:
      "\<And>opn. opn \<in> set openings \<Longrightarrow> opening_index opn \<noteq> j"
  shows
    "table_agrees_with_authenticated_openings (table[j := v]) len openings"
proof -
  have len: "len = length table"
    using agrees unfolding table_agrees_with_authenticated_openings_def
    by simp
  have vals:
    "\<And>opn. opn \<in> set openings \<Longrightarrow>
      opening_index opn < length table \<and>
      table ! opening_index opn = opening_value opn"
    using agrees unfolding table_agrees_with_authenticated_openings_def
    by blast
  have updated_values:
    "\<And>opn. opn \<in> set openings \<Longrightarrow>
      opening_index opn < length (table[j := v]) \<and>
      (table[j := v]) ! opening_index opn = opening_value opn"
  proof -
    fix opn
    assume opn_in: "opn \<in> set openings"
    have idx_bound: "opening_index opn < length table"
      using vals[OF opn_in] by simp
    have idx_ne: "opening_index opn \<noteq> j"
      by (rule unopened[OF opn_in])
    have "(table[j := v]) ! opening_index opn =
        table ! opening_index opn"
      using idx_bound idx_ne by simp
    then show
      "opening_index opn < length (table[j := v]) \<and>
        (table[j := v]) ! opening_index opn = opening_value opn"
      using vals[OF opn_in] by simp
  qed
  show ?thesis
    unfolding table_agrees_with_authenticated_openings_def
    using len updated_values by simp
qed

lemma table_agrees_with_authenticated_openings_eq_if_all_indices_opened:
  assumes agrees:
      "table_agrees_with_authenticated_openings table len openings"
    and agrees':
      "table_agrees_with_authenticated_openings table' len openings"
    and cover:
      "\<And>j. j < len \<Longrightarrow>
        \<exists>opn \<in> set openings. opening_index opn = j"
  shows "table = table'"
proof (rule nth_equalityI)
  show "length table = length table'"
    using agrees agrees'
    unfolding table_agrees_with_authenticated_openings_def by simp
next
  fix j
  assume j_bound: "j < length table"
  have len_eq: "length table = len"
    using agrees unfolding table_agrees_with_authenticated_openings_def
    by simp
  then obtain opn where opn_in: "opn \<in> set openings"
    and opn_idx: "opening_index opn = j"
    using cover j_bound by blast
  have table_val: "table ! j = opening_value opn"
    using agrees opn_in opn_idx
    unfolding table_agrees_with_authenticated_openings_def by blast
  have table'_val: "table' ! j = opening_value opn"
    using agrees' opn_in opn_idx
    unfolding table_agrees_with_authenticated_openings_def by blast
  show "table ! j = table' ! j"
    using table_val table'_val by simp
qed

lemma partial_trace_table_candidate_update_unopened:
  assumes cand: "partial_trace_table_candidate trace_table trace_openings"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow> opn \<in> set (trace_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
  shows
    "partial_trace_table_candidate (trace_table[j := v]) trace_openings"
proof -
  have len: "length (trace_table[j := v]) = scale * clength"
    using cand unfolding partial_trace_table_candidate_def by simp
  have rounds_len: "length trace_openings = rounds"
    using cand unfolding partial_trace_table_candidate_def by simp
  have agrees:
    "\<And>i. i < rounds \<Longrightarrow>
      table_agrees_with_authenticated_openings (trace_table[j := v])
        (scale * clength) (trace_openings ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have old:
      "table_agrees_with_authenticated_openings trace_table
        (scale * clength) (trace_openings ! i)"
      using cand i_bound unfolding partial_trace_table_candidate_def by blast
    show
      "table_agrees_with_authenticated_openings (trace_table[j := v])
        (scale * clength) (trace_openings ! i)"
      by (rule table_agrees_with_authenticated_openings_update_unopened
          [OF old])
        (use unopened[OF i_bound] in blast)
  qed
  show ?thesis
    unfolding partial_trace_table_candidate_def
    using len rounds_len agrees by simp
qed

lemma partial_trace_table_candidates_not_singleton_if_unopened:
  assumes cand: "partial_trace_table_candidate trace_table trace_openings"
    and j_bound: "j < scale * clength"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow> opn \<in> set (trace_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
  shows
    "\<not> (\<exists>table.
      partial_trace_table_candidates trace_openings \<subseteq> {table})"
proof
  assume unique:
    "\<exists>table. partial_trace_table_candidates trace_openings \<subseteq> {table}"
  let ?trace_table' = "trace_table[j := trace_table ! j + 1]"
  have cand_in:
    "trace_table \<in> partial_trace_table_candidates trace_openings"
    using cand unfolding partial_trace_table_candidates_def by simp
  have cand'_in:
    "?trace_table' \<in> partial_trace_table_candidates trace_openings"
    using partial_trace_table_candidate_update_unopened[OF cand unopened]
    unfolding partial_trace_table_candidates_def by simp
  from unique obtain table where subset:
    "partial_trace_table_candidates trace_openings \<subseteq> {table}"
    by blast
  have trace_eq: "trace_table = table"
    using subset cand_in by blast
  have trace'_eq: "?trace_table' = table"
    using subset cand'_in by blast
  have len: "length trace_table = scale * clength"
    using cand unfolding partial_trace_table_candidate_def by simp
  have changed: "?trace_table' ! j \<noteq> trace_table ! j"
    using j_bound len by simp
  show False
    using changed trace_eq trace'_eq by simp
qed

lemma partial_trace_table_candidate_eq_if_all_indices_opened:
  assumes cand: "partial_trace_table_candidate trace_table trace_openings"
    and cand':
      "partial_trace_table_candidate trace_table' trace_openings"
    and cover:
      "\<And>j. j < scale * clength \<Longrightarrow>
        \<exists>i < rounds. \<exists>opn \<in> set (trace_openings ! i).
          opening_index opn = j"
  shows "trace_table = trace_table'"
proof (rule nth_equalityI)
  show "length trace_table = length trace_table'"
    using cand cand' unfolding partial_trace_table_candidate_def by simp
next
  fix j
  assume j_bound: "j < length trace_table"
  have len: "length trace_table = scale * clength"
    using cand unfolding partial_trace_table_candidate_def by simp
  from cover[OF j_bound[unfolded len]]
  obtain i opn where i_bound: "i < rounds"
    and opn_in: "opn \<in> set (trace_openings ! i)"
    and opn_idx: "opening_index opn = j"
    by blast
  have table_val: "trace_table ! j = opening_value opn"
    using partial_trace_table_candidateD(3)[OF cand i_bound opn_in]
      opn_idx by simp
  have table'_val: "trace_table' ! j = opening_value opn"
    using partial_trace_table_candidateD(3)[OF cand' i_bound opn_in]
      opn_idx by simp
  show "trace_table ! j = trace_table' ! j"
    using table_val table'_val by simp
qed

lemma partial_trace_table_candidates_subset_singleton_if_all_indices_opened:
  assumes cand: "partial_trace_table_candidate trace_table trace_openings"
    and cover:
      "\<And>j. j < scale * clength \<Longrightarrow>
        \<exists>i < rounds. \<exists>opn \<in> set (trace_openings ! i).
          opening_index opn = j"
  shows "partial_trace_table_candidates trace_openings \<subseteq> {trace_table}"
proof
  fix trace_table'
  assume "trace_table' \<in> partial_trace_table_candidates trace_openings"
  then have cand':
    "partial_trace_table_candidate trace_table' trace_openings"
    unfolding partial_trace_table_candidates_def by simp
  have "trace_table' = trace_table"
    using partial_trace_table_candidate_eq_if_all_indices_opened
      [OF cand' cand cover] .
  then show "trace_table' \<in> {trace_table}"
    by simp
qed

lemma partial_composition_table_candidate_update_unopened:
  assumes cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow>
        opn \<in> set (composition_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
  shows
    "partial_composition_table_candidate
      (composition_table[j := v]) composition_openings"
proof -
  have len: "length (composition_table[j := v]) = scale * clength"
    using cand unfolding partial_composition_table_candidate_def by simp
  have rounds_len: "length composition_openings = rounds"
    using cand unfolding partial_composition_table_candidate_def by simp
  have agrees:
    "\<And>i. i < rounds \<Longrightarrow>
      table_agrees_with_authenticated_openings
        (composition_table[j := v]) (scale * clength)
        (composition_openings ! i)"
  proof -
    fix i
    assume i_bound: "i < rounds"
    have old:
      "table_agrees_with_authenticated_openings composition_table
        (scale * clength) (composition_openings ! i)"
      using cand i_bound
      unfolding partial_composition_table_candidate_def by blast
    show
      "table_agrees_with_authenticated_openings
        (composition_table[j := v]) (scale * clength)
        (composition_openings ! i)"
      by (rule table_agrees_with_authenticated_openings_update_unopened
          [OF old])
        (use unopened[OF i_bound] in blast)
  qed
  show ?thesis
    unfolding partial_composition_table_candidate_def
    using len rounds_len agrees by simp
qed

lemma partial_composition_table_candidates_not_singleton_if_unopened:
  assumes cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and j_bound: "j < scale * clength"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow>
        opn \<in> set (composition_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
  shows
    "\<not> (\<exists>table.
      partial_composition_table_candidates composition_openings \<subseteq>
        {table})"
proof
  assume unique:
    "\<exists>table. partial_composition_table_candidates composition_openings
      \<subseteq> {table}"
  let ?composition_table' =
    "composition_table[j := composition_table ! j + 1]"
  have cand_in:
    "composition_table \<in>
      partial_composition_table_candidates composition_openings"
    using cand unfolding partial_composition_table_candidates_def by simp
  have cand'_in:
    "?composition_table' \<in>
      partial_composition_table_candidates composition_openings"
    using partial_composition_table_candidate_update_unopened[OF cand unopened]
    unfolding partial_composition_table_candidates_def by simp
  from unique obtain table where subset:
    "partial_composition_table_candidates composition_openings \<subseteq>
      {table}"
    by blast
  have comp_eq: "composition_table = table"
    using subset cand_in by blast
  have comp'_eq: "?composition_table' = table"
    using subset cand'_in by blast
  have len: "length composition_table = scale * clength"
    using cand unfolding partial_composition_table_candidate_def by simp
  have changed: "?composition_table' ! j \<noteq> composition_table ! j"
    using j_bound len by simp
  show False
    using changed comp_eq comp'_eq by simp
qed

lemma partial_composition_table_candidate_eq_if_all_indices_opened:
  assumes cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and cand':
      "partial_composition_table_candidate composition_table'
        composition_openings"
    and cover:
      "\<And>j. j < scale * clength \<Longrightarrow>
        \<exists>i < rounds. \<exists>opn \<in> set (composition_openings ! i).
          opening_index opn = j"
  shows "composition_table = composition_table'"
proof (rule nth_equalityI)
  show "length composition_table = length composition_table'"
    using cand cand'
    unfolding partial_composition_table_candidate_def by simp
next
  fix j
  assume j_bound: "j < length composition_table"
  have len: "length composition_table = scale * clength"
    using cand unfolding partial_composition_table_candidate_def by simp
  from cover[OF j_bound[unfolded len]]
  obtain i opn where i_bound: "i < rounds"
    and opn_in: "opn \<in> set (composition_openings ! i)"
    and opn_idx: "opening_index opn = j"
    by blast
  have table_val: "composition_table ! j = opening_value opn"
    using partial_composition_table_candidateD(3)[OF cand i_bound opn_in]
      opn_idx by simp
  have table'_val: "composition_table' ! j = opening_value opn"
    using partial_composition_table_candidateD(3)[OF cand' i_bound opn_in]
      opn_idx by simp
  show "composition_table ! j = composition_table' ! j"
    using table_val table'_val by simp
qed

lemma partial_composition_table_candidates_subset_singleton_if_all_indices_opened:
  assumes cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and cover:
      "\<And>j. j < scale * clength \<Longrightarrow>
        \<exists>i < rounds. \<exists>opn \<in> set (composition_openings ! i).
          opening_index opn = j"
  shows
    "partial_composition_table_candidates composition_openings \<subseteq>
      {composition_table}"
proof
  fix composition_table'
  assume
    "composition_table' \<in>
      partial_composition_table_candidates composition_openings"
  then have cand':
    "partial_composition_table_candidate composition_table'
      composition_openings"
    unfolding partial_composition_table_candidates_def by simp
  have "composition_table' = composition_table"
    using partial_composition_table_candidate_eq_if_all_indices_opened
      [OF cand' cand cover] .
  then show "composition_table' \<in> {composition_table}"
    by simp
qed

end

end
