(*  Title:      Stark/Soundness_Alpha_Header_Candidate_Blocker.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Alpha_Header_Candidate_Blocker
  imports
    Soundness_Query_Partial_Candidate_Blocker
    Staged_Security_Experiment_Composition
begin

text \<open>
  Diagnostic lemmas for the alpha-header partial-candidate route.

  The staged composition proof uses
  \<^term>\<open>alpha_header_supported_partial_trace_table_candidates\<close>.  This
  candidate set is trace-only, but it has the same sparse-opening obstruction
  as the query-header partial-candidate set: sampled authenticated openings do
  not determine unopened trace-table positions.
\<close>

context soundness
begin

definition alpha_header_partial_candidate_not_prefix_bound
  :: "'f protocol_channel \<Rightarrow> ('f, 'a) protocol_channel_scheme \<Rightarrow>
      'f \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> bool"
where
  "alpha_header_partial_candidate_not_prefix_bound prefix_state s fr
      f_fri_roots f_final \<longleftrightarrow>
    (\<exists>trace_table \<in>
      alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
        f_final.
      trace_table \<notin> alpha_prefix_trace_table_candidates prefix_state fr)"

lemma alpha_header_partial_candidate_not_prefix_bound_iff_not_subset:
  "alpha_header_partial_candidate_not_prefix_bound prefix_state s fr
      f_fri_roots f_final \<longleftrightarrow>
    \<not> alpha_header_supported_partial_trace_table_candidates s fr
        f_fri_roots f_final \<subseteq>
      alpha_prefix_trace_table_candidates prefix_state fr"
  unfolding alpha_header_partial_candidate_not_prefix_bound_def by blast

lemma alpha_header_supported_partial_union_bad_sets_subset_prefix_union_if_bound:
  assumes bound:
      "\<not> alpha_header_partial_candidate_not_prefix_bound prefix_state s fr
        f_fri_roots f_final"
  shows
    "alpha_header_supported_partial_union_bad_sets s bad_sets fr f_fri_roots
      f_final \<subseteq> alpha_prefix_union_bad_sets prefix_state bad_sets fr"
  using bound
  unfolding alpha_header_partial_candidate_not_prefix_bound_def
    alpha_header_supported_partial_union_bad_sets_def
    alpha_prefix_union_bad_sets_def
  by blast

lemma alpha_header_partial_union_hit_not_prefix_hit_imp_not_prefix_bound:
  assumes hit:
      "as \<in>
        alpha_header_supported_partial_union_bad_sets s bad_sets fr
          f_fri_roots f_final"
    and not_prefix:
      "as \<notin> alpha_prefix_union_bad_sets prefix_state bad_sets fr"
  shows
    "alpha_header_partial_candidate_not_prefix_bound prefix_state s fr
      f_fri_roots f_final"
proof (rule ccontr)
  assume
    "\<not> alpha_header_partial_candidate_not_prefix_bound prefix_state s fr
      f_fri_roots f_final"
  then have
    "alpha_header_supported_partial_union_bad_sets s bad_sets fr
      f_fri_roots f_final \<subseteq>
      alpha_prefix_union_bad_sets prefix_state bad_sets fr"
    by (rule alpha_header_supported_partial_union_bad_sets_subset_prefix_union_if_bound)
  then show False
    using hit not_prefix by blast
qed

lemma alpha_header_supported_partial_trace_table_candidates_update_unopened:
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow> opn \<in> set (trace_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
  shows
    "trace_table[j := v] \<in>
      alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
        f_final"
proof -
  have candidate':
    "partial_trace_table_candidate (trace_table[j := v]) trace_openings"
    by (rule partial_trace_table_candidate_update_unopened
        [OF candidate unopened])
  show ?thesis
    unfolding alpha_header_supported_partial_trace_table_candidates_def
    using outcome partial candidate' header by blast
qed

lemma alpha_header_supported_partial_trace_table_candidates_not_singleton_if_trace_unopened:
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and j_bound: "j < scale * clength"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow> opn \<in> set (trace_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
  shows
    "\<not> (\<exists>trace_table0.
      alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
        f_final \<subseteq> {trace_table0})"
proof
  assume unique:
    "\<exists>trace_table0.
      alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
        f_final \<subseteq> {trace_table0}"
  let ?trace_table' = "trace_table[j := trace_table ! j + 1]"
  have candidate_in:
    "trace_table \<in>
      alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
        f_final"
    unfolding alpha_header_supported_partial_trace_table_candidates_def
    using outcome partial candidate header by blast
  have candidate'_in:
    "?trace_table' \<in>
      alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
        f_final"
    by (rule
        alpha_header_supported_partial_trace_table_candidates_update_unopened
        [OF outcome partial candidate header unopened])
  from unique obtain trace_table0 where subset:
    "alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
      f_final \<subseteq> {trace_table0}"
    by blast
  have trace_eq: "trace_table = trace_table0"
    using subset candidate_in by blast
  have trace'_eq: "?trace_table' = trace_table0"
    using subset candidate'_in by blast
  have len: "length trace_table = scale * clength"
    using candidate unfolding partial_trace_table_candidate_def by simp
  have changed: "?trace_table' ! j \<noteq> trace_table ! j"
    using j_bound len by simp
  show False
    using changed trace_eq trace'_eq by simp
qed

lemma alpha_header_supported_partial_trace_table_candidates_not_singleton_if_trace_sparse:
  assumes outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and sparse: "length (List.concat trace_openings) < scale * clength"
  shows
    "\<not> (\<exists>trace_table0.
      alpha_header_supported_partial_trace_table_candidates s fr f_fri_roots
        f_final \<subseteq> {trace_table0})"
proof -
  have rounds_len: "length trace_openings = rounds"
    using candidate unfolding partial_trace_table_candidate_def by simp
  obtain j where j_bound: "j < scale * clength"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow> opn \<in> set (trace_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
    using sparse_openings_obtain_unopened_index[OF rounds_len sparse]
    by blast
  show ?thesis
    by (rule
        alpha_header_supported_partial_trace_table_candidates_not_singleton_if_trace_unopened
        [OF outcome partial candidate header j_bound unopened])
qed

end

end
