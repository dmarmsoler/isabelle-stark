(*  Title:      Stark/Soundness_Query_Partial_Candidate_Blocker.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_Query_Partial_Candidate_Blocker
  imports
    Soundness_Query_Header_Cross_Candidate
    Soundness_Partial_Candidate_Blocker
begin

text \<open>
  Exact query-header version of the partial-candidate non-uniqueness
  diagnostic.  These lemmas show why the old singleton-candidate route cannot
  be applied to the broad partial-opening candidate relation.
\<close>

context soundness
begin

lemma sparse_openings_obtain_unopened_index:
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

lemma accepted_with_partial_trace_openings_concat_length:
  assumes partial:
    "accepted_with_partial_trace_openings s out fr query_idxs trace_openings"
  shows "length (List.concat trace_openings) = rounds * powers"
proof -
  have len: "length trace_openings = rounds"
    by (rule accepted_with_partial_trace_openings_shapes(2)[OF partial])
  have entry_len:
    "\<And>xs. xs \<in> set trace_openings \<Longrightarrow> length xs = powers"
  proof -
    fix xs
    assume xs_in: "xs \<in> set trace_openings"
    then obtain i where i_bound: "i < length trace_openings"
      and xs_eq: "xs = trace_openings ! i"
      by (auto simp: in_set_conv_nth)
    have idxs:
      "map opening_index (trace_openings ! i) =
        powers_scaled (query_idxs ! i)"
      by (rule accepted_with_partial_trace_openings_shapes(3)[OF partial])
        (use i_bound len in simp)
    have len_xs: "length (map opening_index xs) =
      length (powers_scaled (query_idxs ! i))"
      using idxs xs_eq by simp
    show "length xs = powers"
      using len_xs unfolding powers_scaled_def by simp
  qed
  have map_len: "map length trace_openings = replicate rounds powers"
  proof (rule nth_equalityI)
    show "length (map length trace_openings) =
      length (replicate rounds powers)"
      using len by simp
  next
    fix i
    assume i_bound: "i < length (map length trace_openings)"
    have "trace_openings ! i \<in> set trace_openings"
      by (rule nth_mem) (use i_bound in simp)
    then show
      "map length trace_openings ! i = replicate rounds powers ! i"
      using entry_len[of "trace_openings ! i"] i_bound len by simp
  qed
  show ?thesis
  proof -
    have "length (List.concat trace_openings) =
      sum_list (map length trace_openings)"
      by (induction trace_openings) simp_all
    also have "... = sum_list (replicate rounds powers)"
      using map_len by simp
    also have "... = rounds * powers"
      by (induction rounds) simp_all
    finally show ?thesis .
  qed
qed

lemma accepted_with_partial_composition_openings_concat_length:
  assumes partial:
    "accepted_with_partial_composition_openings s out composition_root
      query_idxs composition_openings"
  shows "length (List.concat composition_openings) = rounds * 2"
proof -
  have len: "length composition_openings = rounds"
    by (rule accepted_with_partial_composition_openings_shapes(2)
        [OF partial])
  have entry_len:
    "\<And>xs. xs \<in> set composition_openings \<Longrightarrow> length xs = 2"
  proof -
    fix xs
    assume xs_in: "xs \<in> set composition_openings"
    then obtain i where i_bound: "i < length composition_openings"
      and xs_eq: "xs = composition_openings ! i"
      by (auto simp: in_set_conv_nth)
    have idxs:
      "map opening_index (composition_openings ! i) =
        [query_idxs ! i,
         fri_sibling_index (scale * clength) (query_idxs ! i)]"
      by (rule accepted_with_partial_composition_openings_shapes(3)
          [OF partial])
        (use i_bound len in simp)
    have len_xs: "length (map opening_index xs) = length
      [query_idxs ! i,
       fri_sibling_index (scale * clength) (query_idxs ! i)]"
      using idxs xs_eq by simp
    show "length xs = 2"
      using len_xs by simp
  qed
  have map_len: "map length composition_openings = replicate rounds 2"
  proof (rule nth_equalityI)
    show "length (map length composition_openings) =
      length (replicate rounds 2)"
      using len by simp
  next
    fix i
    assume i_bound: "i < length (map length composition_openings)"
    have "composition_openings ! i \<in> set composition_openings"
      by (rule nth_mem) (use i_bound in simp)
    then show
      "map length composition_openings ! i = replicate rounds 2 ! i"
      using entry_len[of "composition_openings ! i"] i_bound len by simp
  qed
  show ?thesis
  proof -
    have "length (List.concat composition_openings) =
      sum_list (map length composition_openings)"
      by (induction composition_openings) simp_all
    also have "... = sum_list (replicate rounds 2)"
      using map_len by simp
    also have "... = rounds * 2"
      by (induction rounds) simp_all
    finally show ?thesis .
  qed
qed

lemma query_header_supported_partial_table_candidates_update_trace_unopened:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow> opn \<in> set (trace_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
  shows
    "(trace_table[j := v], composition_table) \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
proof -
  have trace_candidate':
    "partial_trace_table_candidate (trace_table[j := v]) trace_openings"
    by (rule partial_trace_table_candidate_update_unopened
        [OF trace_candidate unopened])
  show ?thesis
    unfolding query_header_supported_partial_table_candidates_def
    using comp_nonempty outcome trace_partial trace_candidate'
      comp_partial comp_candidate header
    by blast
qed

lemma query_header_supported_partial_table_candidates_not_singleton_if_trace_unopened:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and j_bound: "j < scale * clength"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow> opn \<in> set (trace_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
  shows
    "\<not> (\<exists>trace_table0 composition_table0.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)})"
proof
  assume unique:
    "\<exists>trace_table0 composition_table0.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)}"
  let ?trace_table' = "trace_table[j := trace_table ! j + 1]"
  have candidate:
    "(trace_table, composition_table) \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_table_candidates_def
    using comp_nonempty outcome trace_partial trace_candidate
      comp_partial comp_candidate header
    by blast
  have candidate':
    "(?trace_table', composition_table) \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    by (rule
        query_header_supported_partial_table_candidates_update_trace_unopened
        [OF comp_nonempty outcome trace_partial trace_candidate comp_partial
          comp_candidate header unopened])
  from unique obtain trace_table0 composition_table0 where subset:
    "query_header_supported_partial_table_candidates s fr f_fri_roots
      f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)}"
    by blast
  have pair_eq:
    "(trace_table, composition_table) = (trace_table0, composition_table0)"
    using subset candidate by blast
  have pair'_eq:
    "(?trace_table', composition_table) = (trace_table0, composition_table0)"
    using subset candidate' by blast
  have len: "length trace_table = scale * clength"
    using trace_candidate unfolding partial_trace_table_candidate_def by simp
  have changed: "?trace_table' ! j \<noteq> trace_table ! j"
    using j_bound len by simp
  show False
    using pair_eq pair'_eq changed by simp
qed

lemma query_header_supported_partial_table_candidates_not_singleton_if_trace_sparse:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and sparse: "length (List.concat trace_openings) < scale * clength"
  shows
    "\<not> (\<exists>trace_table0 composition_table0.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)})"
proof -
  have rounds_len: "length trace_openings = rounds"
    using trace_candidate unfolding partial_trace_table_candidate_def by simp
  obtain j where j_bound: "j < scale * clength"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow> opn \<in> set (trace_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
    using sparse_openings_obtain_unopened_index[OF rounds_len sparse]
    by blast
  show ?thesis
    by (rule
        query_header_supported_partial_table_candidates_not_singleton_if_trace_unopened
        [OF comp_nonempty outcome trace_partial trace_candidate comp_partial
          comp_candidate header j_bound unopened])
qed

lemma query_header_supported_partial_pairwise_cross_or_merkle_bad_if_trace_sparse:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and sparse: "length (List.concat trace_openings) < scale * clength"
  shows
    "query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
      f_fri_roots f_final as dg composition_fri_roots final"
proof -
  have not_unique:
    "\<not> (\<exists>trace_table0 composition_table0.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)})"
    by (rule
        query_header_supported_partial_table_candidates_not_singleton_if_trace_sparse
        [OF comp_nonempty outcome trace_partial trace_candidate comp_partial
          comp_candidate header sparse])
  show ?thesis
    by (rule
        query_header_supported_partial_pairwise_cross_or_merkle_bad_if_not_singleton
        [OF not_unique])
qed

lemma query_header_supported_partial_table_candidates_not_singleton_if_trace_query_sparse:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and sparse: "rounds * powers < scale * clength"
  shows
    "\<not> (\<exists>trace_table0 composition_table0.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)})"
proof -
  have concat_sparse:
    "length (List.concat trace_openings) < scale * clength"
    using accepted_with_partial_trace_openings_concat_length[OF trace_partial]
      sparse by simp
  show ?thesis
    by (rule
        query_header_supported_partial_table_candidates_not_singleton_if_trace_sparse
        [OF comp_nonempty outcome trace_partial trace_candidate comp_partial
          comp_candidate header concat_sparse])
qed

lemma query_header_supported_partial_pairwise_cross_or_merkle_bad_if_trace_query_sparse:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and sparse: "rounds * powers < scale * clength"
  shows
    "query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
      f_fri_roots f_final as dg composition_fri_roots final"
proof -
  have not_unique:
    "\<not> (\<exists>trace_table0 composition_table0.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)})"
    by (rule
        query_header_supported_partial_table_candidates_not_singleton_if_trace_query_sparse
        [OF comp_nonempty outcome trace_partial trace_candidate comp_partial
          comp_candidate header sparse])
  show ?thesis
    by (rule
        query_header_supported_partial_pairwise_cross_or_merkle_bad_if_not_singleton
        [OF not_unique])
qed

lemma query_header_supported_partial_table_candidates_update_composition_unopened:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow>
        opn \<in> set (composition_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
  shows
    "(trace_table, composition_table[j := v]) \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
proof -
  have comp_candidate':
    "partial_composition_table_candidate (composition_table[j := v])
      composition_openings"
    by (rule partial_composition_table_candidate_update_unopened
        [OF comp_candidate unopened])
  show ?thesis
    unfolding query_header_supported_partial_table_candidates_def
    using comp_nonempty outcome trace_partial trace_candidate
      comp_partial comp_candidate' header
    by blast
qed

lemma query_header_supported_partial_table_candidates_not_singleton_if_composition_unopened:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and j_bound: "j < scale * clength"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow>
        opn \<in> set (composition_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
  shows
    "\<not> (\<exists>trace_table0 composition_table0.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)})"
proof
  assume unique:
    "\<exists>trace_table0 composition_table0.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)}"
  let ?composition_table' =
    "composition_table[j := composition_table ! j + 1]"
  have candidate:
    "(trace_table, composition_table) \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    unfolding query_header_supported_partial_table_candidates_def
    using comp_nonempty outcome trace_partial trace_candidate
      comp_partial comp_candidate header
    by blast
  have candidate':
    "(trace_table, ?composition_table') \<in>
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final"
    by (rule
        query_header_supported_partial_table_candidates_update_composition_unopened
        [OF comp_nonempty outcome trace_partial trace_candidate comp_partial
          comp_candidate header unopened])
  from unique obtain trace_table0 composition_table0 where subset:
    "query_header_supported_partial_table_candidates s fr f_fri_roots
      f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)}"
    by blast
  have pair_eq:
    "(trace_table, composition_table) = (trace_table0, composition_table0)"
    using subset candidate by blast
  have pair'_eq:
    "(trace_table, ?composition_table') =
      (trace_table0, composition_table0)"
    using subset candidate' by blast
  have len: "length composition_table = scale * clength"
    using comp_candidate
    unfolding partial_composition_table_candidate_def by simp
  have changed: "?composition_table' ! j \<noteq> composition_table ! j"
    using j_bound len by simp
  show False
    using pair_eq pair'_eq changed by simp
qed

lemma query_header_supported_partial_table_candidates_not_singleton_if_composition_sparse:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and sparse:
      "length (List.concat composition_openings) < scale * clength"
  shows
    "\<not> (\<exists>trace_table0 composition_table0.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)})"
proof -
  have rounds_len: "length composition_openings = rounds"
    using comp_candidate
    unfolding partial_composition_table_candidate_def by simp
  obtain j where j_bound: "j < scale * clength"
    and unopened:
      "\<And>i opn. i < rounds \<Longrightarrow>
        opn \<in> set (composition_openings ! i) \<Longrightarrow>
        opening_index opn \<noteq> j"
    using sparse_openings_obtain_unopened_index[OF rounds_len sparse]
    by blast
  show ?thesis
    by (rule
        query_header_supported_partial_table_candidates_not_singleton_if_composition_unopened
        [OF comp_nonempty outcome trace_partial trace_candidate comp_partial
          comp_candidate header j_bound unopened])
qed

lemma query_header_supported_partial_pairwise_cross_or_merkle_bad_if_composition_sparse:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and sparse:
      "length (List.concat composition_openings) < scale * clength"
  shows
    "query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
      f_fri_roots f_final as dg composition_fri_roots final"
proof -
  have not_unique:
    "\<not> (\<exists>trace_table0 composition_table0.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)})"
    by (rule
        query_header_supported_partial_table_candidates_not_singleton_if_composition_sparse
        [OF comp_nonempty outcome trace_partial trace_candidate comp_partial
          comp_candidate header sparse])
  show ?thesis
    by (rule
        query_header_supported_partial_pairwise_cross_or_merkle_bad_if_not_singleton
        [OF not_unique])
qed

lemma query_header_supported_partial_table_candidates_not_singleton_if_composition_query_sparse:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and sparse: "rounds * 2 < scale * clength"
  shows
    "\<not> (\<exists>trace_table0 composition_table0.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)})"
proof -
  have concat_sparse:
    "length (List.concat composition_openings) < scale * clength"
    using accepted_with_partial_composition_openings_concat_length
      [OF comp_partial] sparse by simp
  show ?thesis
    by (rule
        query_header_supported_partial_table_candidates_not_singleton_if_composition_sparse
        [OF comp_nonempty outcome trace_partial trace_candidate comp_partial
          comp_candidate header concat_sparse])
qed

lemma query_header_supported_partial_pairwise_cross_or_merkle_bad_if_composition_query_sparse:
  assumes comp_nonempty: "composition_fri_roots \<noteq> []"
    and outcome:
      "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and trace_partial:
      "accepted_with_partial_trace_openings s
        (Some (result, final_state)) fr trace_query_idxs trace_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_partial:
      "accepted_with_partial_composition_openings s
        (Some (result, final_state)) (hd composition_fri_roots)
        composition_query_idxs composition_openings"
    and comp_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and header:
      "verifier_header_transcript s fr f_fri_roots f_final as dg
        composition_fri_roots final rest"
    and sparse: "rounds * 2 < scale * clength"
  shows
    "query_header_supported_partial_pairwise_cross_or_merkle_bad s fr
      f_fri_roots f_final as dg composition_fri_roots final"
proof -
  have not_unique:
    "\<not> (\<exists>trace_table0 composition_table0.
      query_header_supported_partial_table_candidates s fr f_fri_roots
        f_final as dg composition_fri_roots final \<subseteq>
      {(trace_table0, composition_table0)})"
    by (rule
        query_header_supported_partial_table_candidates_not_singleton_if_composition_query_sparse
        [OF comp_nonempty outcome trace_partial trace_candidate comp_partial
          comp_candidate header sparse])
  show ?thesis
    by (rule
        query_header_supported_partial_pairwise_cross_or_merkle_bad_if_not_singleton
        [OF not_unique])
qed

end

end
