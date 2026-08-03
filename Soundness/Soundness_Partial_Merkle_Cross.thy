(*  Title:      Stark/Soundness_Partial_Merkle_Cross.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Partial_Merkle_Cross
  imports Soundness_Partial_Merkle
begin

text \<open>
  Cross-state Merkle facts for partial authenticated openings.

  The broad query-header candidate relation can be supported by different
  verifier executions and therefore different final hash-map states.  These
  lemmas isolate the reusable binding fact available in the current model:
  two authenticated openings for the same root, length, and index cannot carry
  different values across compatible cleanly-merged states.
\<close>

context soundness
begin

definition partial_openings_cross_cover_all_indices
  :: "'f authenticated_opening list list \<Rightarrow>
      'f authenticated_opening list list \<Rightarrow> bool"
where
  "partial_openings_cross_cover_all_indices openings openings' \<longleftrightarrow>
    (\<forall>j < scale * clength.
      \<exists>i < rounds. \<exists>i' < rounds.
        \<exists>opn \<in> set (openings ! i).
          \<exists>opn' \<in> set (openings' ! i').
            opening_index opn = j \<and>
            opening_index opn' = j)"

lemma partial_openings_cross_cover_all_indicesD:
  assumes
    "partial_openings_cross_cover_all_indices openings openings'"
    and "j < scale * clength"
  obtains i i' opn opn' where
    "i < rounds"
    "i' < rounds"
    "opn \<in> set (openings ! i)"
    "opn' \<in> set (openings' ! i')"
    "opening_index opn = j"
    "opening_index opn' = j"
  using assms
  unfolding partial_openings_cross_cover_all_indices_def by blast

lemma partial_openings_cross_cover_all_indices_sym:
  assumes "partial_openings_cross_cover_all_indices openings openings'"
  shows "partial_openings_cross_cover_all_indices openings' openings"
  using assms
  unfolding partial_openings_cross_cover_all_indices_def by blast

lemma not_partial_openings_cross_cover_all_indicesE:
  assumes "\<not> partial_openings_cross_cover_all_indices openings openings'"
  obtains j where
    "j < scale * clength"
    "\<And>i i' opn opn'. i < rounds \<Longrightarrow> i' < rounds \<Longrightarrow>
      opn \<in> set (openings ! i) \<Longrightarrow>
      opn' \<in> set (openings' ! i') \<Longrightarrow>
      opening_index opn = j \<Longrightarrow> opening_index opn' \<noteq> j"
  using assms
  unfolding partial_openings_cross_cover_all_indices_def by blast

lemma partial_openings_cross_cover_all_indices_imp_left_cover:
  assumes cover:
      "partial_openings_cross_cover_all_indices openings openings'"
    and j_bound: "j < scale * clength"
  shows "\<exists>i < rounds. \<exists>opn \<in> set (openings ! i).
    opening_index opn = j"
  using partial_openings_cross_cover_all_indicesD[OF cover j_bound] by blast

lemma partial_openings_cross_cover_all_indices_imp_right_cover:
  assumes cover:
      "partial_openings_cross_cover_all_indices openings openings'"
    and j_bound: "j < scale * clength"
  shows "\<exists>i < rounds. \<exists>opn \<in> set (openings' ! i).
    opening_index opn = j"
  using partial_openings_cross_cover_all_indicesD[OF cover j_bound] by blast

lemma cross_sparse_openings_obtain_unopened_index:
  assumes rounds_len: "length openings = rounds"
    and sparse: "length (List.concat openings) < scale * clength"
  obtains j where
    "j < scale * clength"
    "\<And>i opn. i < rounds \<Longrightarrow> opn \<in> set (openings ! i) \<Longrightarrow>
      opening_index opn \<noteq> j"
proof -
  let ?N = "scale * clength"
  let ?I = "opening_index ` set (List.concat openings)"
  have finite_I: "finite ?I"
    by simp
  have card_I_le: "card ?I \<le> length (List.concat openings)"
  proof -
    have "card ?I \<le> card (set (List.concat openings))"
      by (rule card_image_le) simp
    also have "... \<le> length (List.concat openings)"
      by (rule card_length)
    finally show ?thesis .
  qed
  have not_all: "\<not> {0..<?N} \<subseteq> ?I"
  proof
    assume subset: "{0..<?N} \<subseteq> ?I"
    have "?N = card {0..<?N}"
      by simp
    also have "... \<le> card ?I"
      by (rule card_mono[OF finite_I subset])
    also have "... \<le> length (List.concat openings)"
      by (rule card_I_le)
    finally show False
      using sparse by simp
  qed
  from not_all obtain j where j_in: "j \<in> {0..<?N}" and j_notin: "j \<notin> ?I"
    by blast
  then have j_bound: "j < ?N"
    by simp
  have unopened:
    "\<And>i opn. i < rounds \<Longrightarrow> opn \<in> set (openings ! i) \<Longrightarrow>
      opening_index opn \<noteq> j"
  proof -
    fix i opn
    assume i_bound: "i < rounds"
      and opn_in: "opn \<in> set (openings ! i)"
    have "openings ! i \<in> set openings"
      using i_bound rounds_len by simp
    then have "opn \<in> set (List.concat openings)"
      using opn_in by auto
    then show "opening_index opn \<noteq> j"
      using j_notin by auto
  qed
  show ?thesis
    by (rule that[OF j_bound unopened])
qed

lemma partial_openings_cross_cover_all_indices_impossible_if_left_sparse:
  assumes rounds_len: "length openings = rounds"
    and sparse: "length (List.concat openings) < scale * clength"
  shows "\<not> partial_openings_cross_cover_all_indices openings openings'"
proof
  assume cover:
    "partial_openings_cross_cover_all_indices openings openings'"
  from cross_sparse_openings_obtain_unopened_index[OF rounds_len sparse]
  obtain j where j_bound: "j < scale * clength"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow> opn \<in> set (openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
    by blast
  from partial_openings_cross_cover_all_indices_imp_left_cover
      [OF cover j_bound]
  obtain i opn where i_bound: "i < rounds"
    and opn_in: "opn \<in> set (openings ! i)"
    and opn_idx: "opening_index opn = j"
    by blast
  show False
    using unopened[OF i_bound opn_in] opn_idx by simp
qed

lemma partial_openings_cross_cover_all_indices_impossible_if_right_sparse:
  assumes rounds_len: "length openings' = rounds"
    and sparse: "length (List.concat openings') < scale * clength"
  shows "\<not> partial_openings_cross_cover_all_indices openings openings'"
proof -
  have not_sym:
    "\<not> partial_openings_cross_cover_all_indices openings' openings"
    by (rule partial_openings_cross_cover_all_indices_impossible_if_left_sparse
        [OF rounds_len sparse])
  show ?thesis
  proof
    assume cover:
      "partial_openings_cross_cover_all_indices openings openings'"
    have "partial_openings_cross_cover_all_indices openings' openings"
      by (rule partial_openings_cross_cover_all_indices_sym[OF cover])
    then show False
      using not_sym by contradiction
  qed
qed

lemma merkle_path_bound_merkle_mono:
  assumes bound: "merkle_path_bound rt len idx v path s"
    and ext: "merkle_hash_extends s t"
  shows "merkle_path_bound rt len idx v path t"
  using bound
proof (induction path arbitrary: rt len idx)
  case Nil
  then show ?case
    using ext unfolding merkle_hash_extends_def by simp
next
  case (Cons sibling path)
  show ?case
  proof (cases "idx < len div 2")
    case True
    then obtain child where
      child:
        "merkle_path_bound child (len div 2) idx v path s"
      and lookup:
        "fmlookup (HashMap s) (MerkleNode child sibling) = Some rt"
      using Cons.prems by auto
    have child_t:
      "merkle_path_bound child (len div 2) idx v path t"
      by (rule Cons.IH[OF child])
    have lookup_t:
      "fmlookup (HashMap t) (MerkleNode child sibling) = Some rt"
      using ext lookup unfolding merkle_hash_extends_def by simp
    show ?thesis
      using True child_t lookup_t
      by (auto intro!: exI[of _ child])
  next
    case False
    then obtain child where
      child:
        "merkle_path_bound child (len div 2) (idx - len div 2)
          v path s"
      and lookup:
        "fmlookup (HashMap s) (MerkleNode sibling child) = Some rt"
      using Cons.prems by auto
    have child_t:
      "merkle_path_bound child (len div 2) (idx - len div 2)
        v path t"
      by (rule Cons.IH[OF child])
    have lookup_t:
      "fmlookup (HashMap t) (MerkleNode sibling child) = Some rt"
      using ext lookup unfolding merkle_hash_extends_def by simp
    show ?thesis
      using False child_t lookup_t
      by (auto intro!: exI[of _ child])
  qed
qed

lemma authenticated_opening_in_merkle_mono:
  assumes opn_auth: "authenticated_opening_in s opn"
    and ext: "merkle_hash_extends s t"
  shows "authenticated_opening_in t opn"
  using opn_auth merkle_path_bound_merkle_mono[OF _ ext]
  unfolding authenticated_opening_in_def by blast

lemma inconsistent_authenticated_openings_imp_merkle_conflict_or_merge_collision:
  assumes first: "authenticated_opening_in s opening"
    and second: "authenticated_opening_in t opening'"
    and same_root: "opening_root opening = opening_root opening'"
    and same_length: "opening_length opening = opening_length opening'"
    and same_index: "opening_index opening = opening_index opening'"
    and different_value: "opening_value opening \<noteq> opening_value opening'"
  shows
    "merkle_hash_value_conflict s t \<or>
      hash_map_output_collision (merkle_hash_state_merge s t)"
proof (cases "merkle_hash_value_conflict s t")
  case True
  then show ?thesis by simp
next
  case no_conflict: False
  have compatible: "merkle_hash_maps_compatible s t"
    using no_conflict
    unfolding merkle_hash_maps_compatible_iff_no_value_conflict .
  let ?u = "merkle_hash_state_merge s t"
  have s_ext: "merkle_hash_extends s ?u"
    by (rule merkle_hash_state_merge_extends_left_if_compatible
        [OF compatible])
  have t_ext: "merkle_hash_extends t ?u"
    by (rule merkle_hash_state_merge_extends_right)
  have first_u: "authenticated_opening_in ?u opening"
    by (rule authenticated_opening_in_merkle_mono[OF first s_ext])
  have second_u: "authenticated_opening_in ?u opening'"
    by (rule authenticated_opening_in_merkle_mono[OF second t_ext])
  have collision: "hash_map_output_collision ?u"
    by (rule inconsistent_authenticated_openings_imp_hash_collision
        [OF first_u second_u same_root same_length same_index
          different_value])
  then show ?thesis by simp
qed

lemma authenticated_openings_values_eq_if_no_merkle_conflict_clean_merge:
  assumes first: "authenticated_opening_in s opening"
    and second: "authenticated_opening_in t opening'"
    and same_root: "opening_root opening = opening_root opening'"
    and same_length: "opening_length opening = opening_length opening'"
    and same_index: "opening_index opening = opening_index opening'"
    and no_conflict: "\<not> merkle_hash_value_conflict s t"
    and clean_merge:
      "\<not> hash_map_output_collision (merkle_hash_state_merge s t)"
  shows "opening_value opening = opening_value opening'"
proof (rule ccontr)
  assume different:
    "opening_value opening \<noteq> opening_value opening'"
  have
    "merkle_hash_value_conflict s t \<or>
      hash_map_output_collision (merkle_hash_state_merge s t)"
    by (rule
        inconsistent_authenticated_openings_imp_merkle_conflict_or_merge_collision
        [OF first second same_root same_length same_index different])
  then show False
    using no_conflict clean_merge by blast
qed

lemma partial_authenticated_tables_values_eq_if_no_merkle_conflict_clean_merge:
  assumes table:
      "partial_authenticated_table rt len openings s"
    and table':
      "partial_authenticated_table rt len openings' t"
    and opn_in: "opn \<in> set openings"
    and opn'_in: "opn' \<in> set openings'"
    and same_index: "opening_index opn = opening_index opn'"
    and no_conflict: "\<not> merkle_hash_value_conflict s t"
    and clean_merge:
      "\<not> hash_map_output_collision (merkle_hash_state_merge s t)"
  shows "opening_value opn = opening_value opn'"
proof -
  have first: "authenticated_opening_in s opn"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have second: "authenticated_opening_in t opn'"
    using table' opn'_in unfolding partial_authenticated_table_def by blast
  have root: "opening_root opn = rt"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have root': "opening_root opn' = rt"
    using table' opn'_in unfolding partial_authenticated_table_def by blast
  have same_root: "opening_root opn = opening_root opn'"
    using root root' by simp
  have len: "opening_length opn = len"
    using table opn_in unfolding partial_authenticated_table_def by blast
  have len': "opening_length opn' = len"
    using table' opn'_in unfolding partial_authenticated_table_def by blast
  have same_length: "opening_length opn = opening_length opn'"
    using len len' by simp
  show ?thesis
    by (rule authenticated_openings_values_eq_if_no_merkle_conflict_clean_merge
        [OF first second same_root same_length same_index no_conflict
          clean_merge])
qed

lemma partial_trace_openings_values_eq_if_no_merkle_conflict_clean_merge:
  assumes partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    and partial':
      "accepted_with_partial_trace_openings s'
        (Some (result', final_state')) fr query_idxs' trace_openings'"
    and i_bound: "i < rounds"
    and i'_bound: "i' < rounds"
    and opn_in: "opn \<in> set (trace_openings ! i)"
    and opn'_in: "opn' \<in> set (trace_openings' ! i')"
    and same_index: "opening_index opn = opening_index opn'"
    and no_conflict:
      "\<not> merkle_hash_value_conflict final_state final_state'"
    and clean_merge:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
  shows "opening_value opn = opening_value opn'"
proof -
  have table:
    "partial_authenticated_table fr (scale * clength)
      (trace_openings ! i) final_state"
    using partial i_bound
    unfolding accepted_with_partial_trace_openings_def by blast
  have table':
    "partial_authenticated_table fr (scale * clength)
      (trace_openings' ! i') final_state'"
    using partial' i'_bound
    unfolding accepted_with_partial_trace_openings_def by blast
  show ?thesis
    by (rule
        partial_authenticated_tables_values_eq_if_no_merkle_conflict_clean_merge
        [OF table table' opn_in opn'_in same_index no_conflict
          clean_merge])
qed

lemma partial_composition_openings_values_eq_if_no_merkle_conflict_clean_merge:
  assumes partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) composition_root query_idxs
        composition_openings"
    and partial':
      "accepted_with_partial_composition_openings s'
        (Some (result', final_state')) composition_root query_idxs'
        composition_openings'"
    and i_bound: "i < rounds"
    and i'_bound: "i' < rounds"
    and opn_in: "opn \<in> set (composition_openings ! i)"
    and opn'_in: "opn' \<in> set (composition_openings' ! i')"
    and same_index: "opening_index opn = opening_index opn'"
    and no_conflict:
      "\<not> merkle_hash_value_conflict final_state final_state'"
    and clean_merge:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
  shows "opening_value opn = opening_value opn'"
proof -
  have table:
    "partial_authenticated_table composition_root (scale * clength)
      (composition_openings ! i) final_state"
    using partial i_bound
    unfolding accepted_with_partial_composition_openings_def by blast
  have table':
    "partial_authenticated_table composition_root (scale * clength)
      (composition_openings' ! i') final_state'"
    using partial' i'_bound
    unfolding accepted_with_partial_composition_openings_def by blast
  show ?thesis
    by (rule
        partial_authenticated_tables_values_eq_if_no_merkle_conflict_clean_merge
        [OF table table' opn_in opn'_in same_index no_conflict
          clean_merge])
qed

lemma partial_trace_table_candidates_eq_if_cross_openings_cover_clean_merge:
  assumes partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    and partial':
      "accepted_with_partial_trace_openings s'
        (Some (result', final_state')) fr query_idxs' trace_openings'"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and cand':
      "partial_trace_table_candidate trace_table' trace_openings'"
    and cover:
      "\<And>j. j < scale * clength \<Longrightarrow>
        \<exists>i < rounds. \<exists>i' < rounds.
          \<exists>opn \<in> set (trace_openings ! i).
            \<exists>opn' \<in> set (trace_openings' ! i').
              opening_index opn = j \<and>
              opening_index opn' = j"
    and no_conflict:
      "\<not> merkle_hash_value_conflict final_state final_state'"
    and clean_merge:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
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
  obtain i i' opn opn' where
    i_bound: "i < rounds"
    and i'_bound: "i' < rounds"
    and opn_in: "opn \<in> set (trace_openings ! i)"
    and opn'_in: "opn' \<in> set (trace_openings' ! i')"
    and opn_idx: "opening_index opn = j"
    and opn'_idx: "opening_index opn' = j"
    by blast
  have trace_val: "trace_table ! j = opening_value opn"
    using partial_trace_table_candidateD(3)[OF cand i_bound opn_in]
      opn_idx by simp
  have trace'_val: "trace_table' ! j = opening_value opn'"
    using partial_trace_table_candidateD(3)[OF cand' i'_bound opn'_in]
      opn'_idx by simp
  have opening_values:
    "opening_value opn = opening_value opn'"
    by (rule partial_trace_openings_values_eq_if_no_merkle_conflict_clean_merge
        [OF partial partial' i_bound i'_bound opn_in opn'_in _ no_conflict
          clean_merge])
      (use opn_idx opn'_idx in simp)
  show "trace_table ! j = trace_table' ! j"
    using trace_val trace'_val opening_values by simp
qed

lemma partial_trace_table_candidates_eq_if_cross_cover_clean_merge:
  assumes partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr query_idxs trace_openings"
    and partial':
      "accepted_with_partial_trace_openings s'
        (Some (result', final_state')) fr query_idxs' trace_openings'"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and cand':
      "partial_trace_table_candidate trace_table' trace_openings'"
    and cover:
      "partial_openings_cross_cover_all_indices trace_openings
        trace_openings'"
    and no_conflict:
      "\<not> merkle_hash_value_conflict final_state final_state'"
    and clean_merge:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
  shows "trace_table = trace_table'"
proof (rule
    partial_trace_table_candidates_eq_if_cross_openings_cover_clean_merge
      [OF partial partial' cand cand' _ no_conflict clean_merge])
  fix j
  assume "j < scale * clength"
  from partial_openings_cross_cover_all_indicesD[OF cover this]
  obtain i i' opn opn' where
    "i < rounds" "i' < rounds"
    "opn \<in> set (trace_openings ! i)"
    "opn' \<in> set (trace_openings' ! i')"
    "opening_index opn = j"
    "opening_index opn' = j"
    by blast
  then show
    "\<exists>i < rounds. \<exists>i' < rounds.
      \<exists>opn \<in> set (trace_openings ! i).
        \<exists>opn' \<in> set (trace_openings' ! i').
          opening_index opn = j \<and> opening_index opn' = j"
    by blast
qed

lemma partial_composition_table_candidates_eq_if_cross_openings_cover_clean_merge:
  assumes partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) composition_root query_idxs
        composition_openings"
    and partial':
      "accepted_with_partial_composition_openings s'
        (Some (result', final_state')) composition_root query_idxs'
        composition_openings'"
    and cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and cand':
      "partial_composition_table_candidate composition_table'
        composition_openings'"
    and cover:
      "\<And>j. j < scale * clength \<Longrightarrow>
        \<exists>i < rounds. \<exists>i' < rounds.
          \<exists>opn \<in> set (composition_openings ! i).
            \<exists>opn' \<in> set (composition_openings' ! i').
              opening_index opn = j \<and>
              opening_index opn' = j"
    and no_conflict:
      "\<not> merkle_hash_value_conflict final_state final_state'"
    and clean_merge:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
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
  obtain i i' opn opn' where
    i_bound: "i < rounds"
    and i'_bound: "i' < rounds"
    and opn_in: "opn \<in> set (composition_openings ! i)"
    and opn'_in: "opn' \<in> set (composition_openings' ! i')"
    and opn_idx: "opening_index opn = j"
    and opn'_idx: "opening_index opn' = j"
    by blast
  have composition_val:
    "composition_table ! j = opening_value opn"
    using partial_composition_table_candidateD(3)[OF cand i_bound opn_in]
      opn_idx by simp
  have composition'_val:
    "composition_table' ! j = opening_value opn'"
    using partial_composition_table_candidateD(3)[OF cand' i'_bound opn'_in]
      opn'_idx by simp
  have opening_values:
    "opening_value opn = opening_value opn'"
    by (rule
        partial_composition_openings_values_eq_if_no_merkle_conflict_clean_merge
        [OF partial partial' i_bound i'_bound opn_in opn'_in _ no_conflict
          clean_merge])
      (use opn_idx opn'_idx in simp)
  show "composition_table ! j = composition_table' ! j"
    using composition_val composition'_val opening_values by simp
qed

lemma partial_composition_table_candidates_eq_if_cross_cover_clean_merge:
  assumes partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) composition_root query_idxs
        composition_openings"
    and partial':
      "accepted_with_partial_composition_openings s'
        (Some (result', final_state')) composition_root query_idxs'
        composition_openings'"
    and cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and cand':
      "partial_composition_table_candidate composition_table'
        composition_openings'"
    and cover:
      "partial_openings_cross_cover_all_indices composition_openings
        composition_openings'"
    and no_conflict:
      "\<not> merkle_hash_value_conflict final_state final_state'"
    and clean_merge:
      "\<not> hash_map_output_collision
        (merkle_hash_state_merge final_state final_state')"
  shows "composition_table = composition_table'"
proof (rule
    partial_composition_table_candidates_eq_if_cross_openings_cover_clean_merge
      [OF partial partial' cand cand' _ no_conflict clean_merge])
  fix j
  assume "j < scale * clength"
  from partial_openings_cross_cover_all_indicesD[OF cover this]
  obtain i i' opn opn' where
    "i < rounds" "i' < rounds"
    "opn \<in> set (composition_openings ! i)"
    "opn' \<in> set (composition_openings' ! i')"
    "opening_index opn = j"
    "opening_index opn' = j"
    by blast
  then show
    "\<exists>i < rounds. \<exists>i' < rounds.
      \<exists>opn \<in> set (composition_openings ! i).
        \<exists>opn' \<in> set (composition_openings' ! i').
          opening_index opn = j \<and> opening_index opn' = j"
    by blast
qed

end

end
