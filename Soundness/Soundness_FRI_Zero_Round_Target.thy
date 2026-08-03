(*  Title:      Stark/Soundness_FRI_Zero_Round_Target.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Zero_Round_Target
  imports Soundness_FRI_Sampled_Assignment_Chain
begin

text \<open>
  Query-style target events for the zero-round FRI branch.

  If no FRI fold round is present, sampled fold equations cannot produce a
  successor layer.  Acceptance can only test that sampled base-layer entries
  agree with the final value.  This theory factors the corresponding target
  set without changing the protocol or the public soundness interface.
\<close>

context soundness
begin

definition fri_final_value_agreement_set :: "'f list \<Rightarrow> 'f \<Rightarrow> nat set"
  where
    "fri_final_value_agreement_set table final =
      {idx \<in> query_sample_space. idx < length table \<and> table ! idx = final}"

definition fri_zero_round_final_value_target_hit
  :: "'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "fri_zero_round_final_value_target_hit table final query_idxs
      \<longleftrightarrow>
        \<not> fri_final_constant_consistent table final \<and>
        set query_idxs \<subseteq> fri_final_value_agreement_set table final"

definition trace_zero_round_final_checked_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow>
      'f \<Rightarrow> nat list \<Rightarrow> 'f authenticated_opening list list \<Rightarrow>
      'f list \<Rightarrow> 'f \<Rightarrow> bool"
  where
    "trace_zero_round_final_checked_candidate s out fr query_idxs
        trace_openings trace_table final \<longleftrightarrow>
      accepted_with_partial_trace_openings s out fr query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      (\<forall>idx \<in> set query_idxs. idx \<in> query_sample_space) \<and>
      (\<forall>i < rounds. opening_value (hd (trace_openings ! i)) = final)"

definition trace_fri_zero_round_checked_final_obstruction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_zero_round_checked_final_obstruction s out \<longleftrightarrow>
      (\<exists>trace_roots trace_bs trace_final dg composition_roots
          composition_bs composition_final fri_query_idxs trace_round_layers
          composition_round_layers fr trace_openings trace_table.
        accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final dg composition_roots composition_bs composition_final
          fri_query_idxs trace_round_layers composition_round_layers \<and>
        length trace_bs = 0 \<and>
        trace_zero_round_final_checked_candidate s out fr fri_query_idxs
          trace_openings trace_table trace_final \<and>
        \<not> fri_final_constant_consistent trace_table trace_final)"

lemma fri_final_value_agreement_set_subset:
  "fri_final_value_agreement_set table final \<subseteq> query_sample_space"
  unfolding fri_final_value_agreement_set_def by blast

lemma finite_fri_final_value_agreement_set[simp]:
  "finite (fri_final_value_agreement_set table final)"
  by (rule finite_subset[OF fri_final_value_agreement_set_subset])
    simp

lemma fri_final_value_agreement_setD:
  assumes "idx \<in> fri_final_value_agreement_set table final"
  shows "idx \<in> query_sample_space"
    and "idx < length table"
    and "table ! idx = final"
  using assms unfolding fri_final_value_agreement_set_def by blast+

lemma fri_zero_round_final_value_target_hitD:
  assumes "fri_zero_round_final_value_target_hit table final query_idxs"
  shows "\<not> fri_final_constant_consistent table final"
    and "\<And>idx. idx \<in> set query_idxs \<Longrightarrow>
      idx \<in> fri_final_value_agreement_set table final"
  using assms
  unfolding fri_zero_round_final_value_target_hit_def by blast+

lemma powers_scaled_hd:
  "hd (powers_scaled idx) = idx"
  unfolding powers_scaled_def
  using powers_pos by (simp add: upt_conv_Cons)

lemma trace_zero_round_final_checked_candidate_query_agrees:
  assumes checked:
    "trace_zero_round_final_checked_candidate s out fr query_idxs
      trace_openings trace_table final"
    and i_bound: "i < rounds"
  shows
    "query_idxs ! i \<in> fri_final_value_agreement_set trace_table final"
proof -
  have partial:
    "accepted_with_partial_trace_openings s out fr query_idxs trace_openings"
    using checked unfolding trace_zero_round_final_checked_candidate_def
    by simp
  have cand:
    "partial_trace_table_candidate trace_table trace_openings"
    using checked unfolding trace_zero_round_final_checked_candidate_def
    by simp
  have query_sample:
    "query_idxs ! i \<in> query_sample_space"
    using checked i_bound accepted_with_partial_trace_openings_shapes(1)
      [OF partial]
    unfolding trace_zero_round_final_checked_candidate_def
    by simp
  have idxs:
    "map opening_index (trace_openings ! i) =
      powers_scaled (query_idxs ! i)"
    by (rule accepted_with_partial_trace_openings_shapes(3)
        [OF partial i_bound])
  have openings_nonempty: "trace_openings ! i \<noteq> []"
  proof -
    have "map opening_index (trace_openings ! i) \<noteq> []"
      using idxs powers_pos unfolding powers_scaled_def by simp
    then show ?thesis by auto
  qed
  have hd_index:
    "opening_index (hd (trace_openings ! i)) = query_idxs ! i"
  proof -
    have "opening_index (hd (trace_openings ! i)) =
        hd (map opening_index (trace_openings ! i))"
      using openings_nonempty by (cases "trace_openings ! i") auto
    also have "... = hd (powers_scaled (query_idxs ! i))"
      using idxs by simp
    also have "... = query_idxs ! i"
      by (rule powers_scaled_hd)
    finally show ?thesis .
  qed
  have hd_in: "hd (trace_openings ! i) \<in> set (trace_openings ! i)"
    using openings_nonempty by simp
  have table_value:
    "trace_table ! (query_idxs ! i) =
      opening_value (hd (trace_openings ! i))"
    using partial_trace_table_candidateD(3)[OF cand i_bound hd_in]
      hd_index by simp
  have final:
    "opening_value (hd (trace_openings ! i)) = final"
    using checked i_bound
    unfolding trace_zero_round_final_checked_candidate_def by simp
  have table_len:
    "length trace_table = scale * clength"
    using cand unfolding partial_trace_table_candidate_def by blast
  have idx_bound: "query_idxs ! i < length trace_table"
    using partial_trace_table_candidateD(2)[OF cand i_bound hd_in]
      hd_index table_len by simp
  show ?thesis
    unfolding fri_final_value_agreement_set_def
    using query_sample idx_bound table_value final by simp
qed

lemma trace_zero_round_final_checked_candidate_target_hit:
  assumes checked:
    "trace_zero_round_final_checked_candidate s out fr query_idxs
      trace_openings trace_table final"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table final"
  shows
    "fri_zero_round_final_value_target_hit trace_table final query_idxs"
proof -
  have partial:
    "accepted_with_partial_trace_openings s out fr query_idxs trace_openings"
    using checked unfolding trace_zero_round_final_checked_candidate_def
    by simp
  have len_query: "length query_idxs = rounds"
    by (rule accepted_with_partial_trace_openings_shapes(1)[OF partial])
  have subset:
    "set query_idxs \<subseteq> fri_final_value_agreement_set trace_table final"
  proof
    fix idx
    assume idx_in: "idx \<in> set query_idxs"
    then obtain i where i_bound: "i < length query_idxs"
      and idx_eq: "idx = query_idxs ! i"
      by (auto simp: in_set_conv_nth)
    then have "i < rounds"
      using len_query by simp
    then show "idx \<in> fri_final_value_agreement_set trace_table final"
      using idx_eq
      by (simp add:
          trace_zero_round_final_checked_candidate_query_agrees[OF checked])
  qed
  show ?thesis
    unfolding fri_zero_round_final_value_target_hit_def
    using not_final subset by simp
qed

lemma trace_fri_zero_round_checked_final_obstructionE:
  assumes "trace_fri_zero_round_checked_final_obstruction s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table
  where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "length trace_bs = 0"
    "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
      trace_openings trace_table trace_final"
    "\<not> fri_final_constant_consistent trace_table trace_final"
  using assms
  unfolding trace_fri_zero_round_checked_final_obstruction_def
  by blast

lemma trace_fri_zero_round_checked_final_obstruction_target_hit:
  assumes "trace_fri_zero_round_checked_final_obstruction s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table
  where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "length trace_bs = 0"
    "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
      trace_openings trace_table trace_final"
    "\<not> fri_final_constant_consistent trace_table trace_final"
    "fri_zero_round_final_value_target_hit trace_table trace_final
      fri_query_idxs"
proof (rule trace_fri_zero_round_checked_final_obstructionE[OF assms])
  fix trace_roots trace_bs trace_final dg composition_roots composition_bs
    composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr trace_openings trace_table
  assume fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and rounds_empty: "length trace_bs = 0"
    and checked:
    "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
      trace_openings trace_table trace_final"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
  have target:
    "fri_zero_round_final_value_target_hit trace_table trace_final
      fri_query_idxs"
    by (rule trace_zero_round_final_checked_candidate_target_hit
        [OF checked not_final])
  show ?thesis
    by (rule that[OF fri_openings rounds_empty checked not_final target])
qed

lemma fri_final_value_agreement_set_card_le:
  "card (fri_final_value_agreement_set table final) \<le>
    query_sample_space_size"
proof -
  have "card (fri_final_value_agreement_set table final) \<le>
      card query_sample_space"
    by (rule card_mono[OF finite_query_sample_space
          fri_final_value_agreement_set_subset])
  then show ?thesis by simp
qed

lemma fri_final_value_agreement_set_card_lt_if_query_sample_disagrees:
  assumes idx_sample: "idx \<in> query_sample_space"
    and idx_bound: "idx < length table"
    and neq: "table ! idx \<noteq> final"
  shows "card (fri_final_value_agreement_set table final) <
    query_sample_space_size"
proof -
  have proper:
    "fri_final_value_agreement_set table final \<subset> query_sample_space"
  proof
    show "fri_final_value_agreement_set table final \<subseteq> query_sample_space"
      by (rule fri_final_value_agreement_set_subset)
  next
    show "fri_final_value_agreement_set table final \<noteq> query_sample_space"
    proof
      assume eq: "fri_final_value_agreement_set table final =
        query_sample_space"
      then have "idx \<in> fri_final_value_agreement_set table final"
        using idx_sample by simp
      then show False
        using fri_final_value_agreement_setD(3) neq by blast
    qed
  qed
  have "card (fri_final_value_agreement_set table final) <
      card query_sample_space"
    by (rule psubset_card_mono[OF finite_query_sample_space proper])
  then show ?thesis by simp
qed

lemma fri_final_value_agreement_set_all_query_sample_iff:
  assumes table_covers_query_sample:
    "\<And>idx. idx \<in> query_sample_space \<Longrightarrow> idx < length table"
  shows
    "fri_final_value_agreement_set table final = query_sample_space
      \<longleftrightarrow>
     (\<forall>idx \<in> query_sample_space. table ! idx = final)"
  unfolding fri_final_value_agreement_set_def
  using table_covers_query_sample by blast

lemma fri_final_constant_consistent_if_query_sample_is_whole_table:
  assumes table_len: "length table = query_sample_space_size"
    and all_query: "\<forall>idx \<in> query_sample_space. table ! idx = final"
  shows "fri_final_constant_consistent table final"
proof -
  have all_idx: "\<And>idx. idx < length table \<Longrightarrow> table ! idx = final"
  proof -
    fix idx
    assume idx_bound: "idx < length table"
    then have "idx \<in> query_sample_space"
      using table_len unfolding query_sample_space_def by simp
    then show "table ! idx = final"
      using all_query by simp
  qed
  show ?thesis
    unfolding fri_final_constant_consistent_def
    using all_idx by (auto simp: in_set_conv_nth)
qed

lemma fri_final_value_agreement_set_card_lt_if_not_constant_whole_sample:
  assumes table_len: "length table = query_sample_space_size"
    and not_final: "\<not> fri_final_constant_consistent table final"
  shows "card (fri_final_value_agreement_set table final) <
    query_sample_space_size"
proof (rule ccontr)
  assume "\<not> card (fri_final_value_agreement_set table final) <
      query_sample_space_size"
  then have card_eq:
    "card (fri_final_value_agreement_set table final) =
      query_sample_space_size"
    using fri_final_value_agreement_set_card_le[of table final] by linarith
  have set_eq:
    "fri_final_value_agreement_set table final = query_sample_space"
    by (rule card_subset_eq[OF finite_query_sample_space
          fri_final_value_agreement_set_subset])
      (use card_eq in simp)
  have all_query:
    "\<forall>idx \<in> query_sample_space. table ! idx = final"
    using set_eq fri_final_value_agreement_setD(3) by metis
  have "fri_final_constant_consistent table final"
    by (rule fri_final_constant_consistent_if_query_sample_is_whole_table
        [OF table_len all_query])
  then show False
    using not_final by simp
qed

lemma trace_zero_round_table_len_equals_query_sample_space:
  assumes trace_rounds_empty: "length trace_bs = 0"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
  shows "length trace_table = query_sample_space_size"
proof -
  have len_trace_bs: "length trace_bs = ceil_log clength"
    using accepted_fri_opening_transcript_shapes(1,2)[OF fri_openings]
    by simp
  have ceil_zero: "ceil_log clength = 0"
    using trace_rounds_empty len_trace_bs by simp
  have clength_le_one: "clength \<le> 1"
    using ceil_zero unfolding ceil_log_def
    by (cases "clength \<le> 1") simp_all
  have clength_eq: "clength = 1"
    using clength_le_one clength_pos by simp
  have powers_eq: "powers = 1"
    using powers_pos powers_le_clength clength_eq by simp
  have table_len: "length trace_table = scale * clength"
    using cand unfolding partial_trace_table_candidate_def by blast
  show ?thesis
    unfolding query_sample_space_size_def
    using table_len clength_eq powers_eq by simp
qed

lemma trace_fri_zero_round_checked_final_obstruction_agreement_set_card_lt:
  assumes obstruction:
    "trace_fri_zero_round_checked_final_obstruction s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table
  where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "length trace_bs = 0"
    "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
      trace_openings trace_table trace_final"
    "\<not> fri_final_constant_consistent trace_table trace_final"
    "fri_zero_round_final_value_target_hit trace_table trace_final
      fri_query_idxs"
    "card (fri_final_value_agreement_set trace_table trace_final) <
      query_sample_space_size"
proof (rule trace_fri_zero_round_checked_final_obstruction_target_hit
    [OF obstruction])
  fix trace_roots trace_bs trace_final dg composition_roots composition_bs
    composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr trace_openings trace_table
  assume fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and rounds_empty: "length trace_bs = 0"
    and checked:
    "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
      trace_openings trace_table trace_final"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
    and target:
      "fri_zero_round_final_value_target_hit trace_table trace_final
        fri_query_idxs"
  have cand:
    "partial_trace_table_candidate trace_table trace_openings"
    using checked unfolding trace_zero_round_final_checked_candidate_def
    by simp
  have table_len:
    "length trace_table = query_sample_space_size"
    by (rule trace_zero_round_table_len_equals_query_sample_space
        [OF rounds_empty fri_openings cand])
  have card_lt:
    "card (fri_final_value_agreement_set trace_table trace_final) <
      query_sample_space_size"
    by (rule fri_final_value_agreement_set_card_lt_if_not_constant_whole_sample
        [OF table_len not_final])
  show ?thesis
    by (rule that[OF fri_openings rounds_empty checked not_final target
          card_lt])
qed

lemma trace_fri_zero_round_checked_final_obstruction_first_query_target:
  assumes obstruction:
    "trace_fri_zero_round_checked_final_obstruction s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table
  where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "length trace_bs = 0"
    "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
      trace_openings trace_table trace_final"
    "\<not> fri_final_constant_consistent trace_table trace_final"
    "fri_query_idxs ! 0 \<in>
      fri_final_value_agreement_set trace_table trace_final"
    "card (fri_final_value_agreement_set trace_table trace_final) <
      query_sample_space_size"
proof (rule trace_fri_zero_round_checked_final_obstruction_agreement_set_card_lt
    [OF obstruction])
  fix trace_roots trace_bs trace_final dg composition_roots composition_bs
    composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr trace_openings trace_table
  assume fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and rounds_empty: "length trace_bs = 0"
    and checked:
    "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
      trace_openings trace_table trace_final"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
    and target:
      "fri_zero_round_final_value_target_hit trace_table trace_final
        fri_query_idxs"
    and card_lt:
      "card (fri_final_value_agreement_set trace_table trace_final) <
        query_sample_space_size"
  have first_in:
    "fri_query_idxs ! 0 \<in>
      fri_final_value_agreement_set trace_table trace_final"
  proof -
    have partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
      using checked unfolding trace_zero_round_final_checked_candidate_def
      by simp
    have "length fri_query_idxs = rounds"
      by (rule accepted_with_partial_trace_openings_shapes(1)[OF partial])
    then have "fri_query_idxs ! 0 \<in> set fri_query_idxs"
      using rounds_positive by (simp add: nth_mem)
    then show ?thesis
      by (rule fri_zero_round_final_value_target_hitD(2)[OF target])
  qed
  show ?thesis
    by (rule that[OF fri_openings rounds_empty checked not_final first_in
          card_lt])
qed

lemma trace_zero_round_checked_candidate_not_trace_low_degree:
  assumes rounds_empty: "length trace_bs = 0"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and checked:
      "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
        trace_openings trace_table trace_final"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
  shows "\<not> trace_table_low_degree trace_table"
proof
  assume low: "trace_table_low_degree trace_table"
  have len_trace_bs: "length trace_bs = ceil_log clength"
    using accepted_fri_opening_transcript_shapes(1,2)[OF fri_openings]
    by simp
  have ceil_zero: "ceil_log clength = 0"
    using rounds_empty len_trace_bs by simp
  have clength_le_one: "clength \<le> 1"
    using ceil_zero unfolding ceil_log_def
    by (cases "clength \<le> 1") simp_all
  have clength_eq: "clength = 1"
    using clength_le_one clength_pos by simp
  obtain f where deg_f: "degree f < clength"
    and trace_table: "trace_table = map (poly f) eval_domain"
    using low unfolding trace_table_low_degree_def by blast
  have deg0: "degree f = 0"
    using deg_f clength_eq by simp
  obtain a where f_eq: "f = [:a:]"
    using degree0_coeffs[OF deg0] by blast
  have table_const:
    "\<And>y. y \<in> set trace_table \<Longrightarrow> y = a"
    using trace_table f_eq by auto
  have sample_agrees:
    "fri_query_idxs ! 0 \<in>
      fri_final_value_agreement_set trace_table trace_final"
    by (rule trace_zero_round_final_checked_candidate_query_agrees
        [OF checked rounds_positive])
  have idx_bound: "fri_query_idxs ! 0 < length trace_table"
    using fri_final_value_agreement_setD(2)[OF sample_agrees] .
  have table_at_final:
    "trace_table ! (fri_query_idxs ! 0) = trace_final"
    using fri_final_value_agreement_setD(3)[OF sample_agrees] .
  have "trace_table ! (fri_query_idxs ! 0) \<in> set trace_table"
    using idx_bound by simp
  then have a_eq: "a = trace_final"
    using table_const table_at_final by simp
  have "fri_final_constant_consistent trace_table trace_final"
    unfolding fri_final_constant_consistent_def
    using table_const a_eq by auto
  then show False
    using not_final by contradiction
qed

lemma trace_fri_zero_round_checked_final_obstruction_not_trace_low_degree:
  assumes obstruction:
    "trace_fri_zero_round_checked_final_obstruction s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table
  where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "length trace_bs = 0"
    "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
      trace_openings trace_table trace_final"
    "\<not> fri_final_constant_consistent trace_table trace_final"
    "\<not> trace_table_low_degree trace_table"
proof (rule trace_fri_zero_round_checked_final_obstructionE[OF obstruction])
  fix trace_roots trace_bs trace_final dg composition_roots composition_bs
    composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr trace_openings trace_table
  assume fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and rounds_empty: "length trace_bs = 0"
    and checked:
    "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
      trace_openings trace_table trace_final"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
  have not_low:
    "\<not> trace_table_low_degree trace_table"
    by (rule trace_zero_round_checked_candidate_not_trace_low_degree
        [OF rounds_empty fri_openings checked not_final])
  show ?thesis
    by (rule that[OF fri_openings rounds_empty checked not_final not_low])
qed

definition trace_fri_zero_round_checked_first_query_target_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
  where
    "trace_fri_zero_round_checked_first_query_target_hit s out \<longleftrightarrow>
      (\<exists>trace_roots trace_bs trace_final dg composition_roots
          composition_bs composition_final fri_query_idxs trace_round_layers
          composition_round_layers fr trace_openings trace_table.
        accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final dg composition_roots composition_bs composition_final
          fri_query_idxs trace_round_layers composition_round_layers \<and>
        length trace_bs = 0 \<and>
        trace_zero_round_final_checked_candidate s out fr fri_query_idxs
          trace_openings trace_table trace_final \<and>
        \<not> fri_final_constant_consistent trace_table trace_final \<and>
        fri_query_idxs ! 0 \<in>
          fri_final_value_agreement_set trace_table trace_final \<and>
        card (fri_final_value_agreement_set trace_table trace_final) <
          query_sample_space_size)"

lemma trace_fri_zero_round_checked_final_obstruction_imp_first_query_target_hit:
  assumes "trace_fri_zero_round_checked_final_obstruction s out"
  shows "trace_fri_zero_round_checked_first_query_target_hit s out"
proof (rule trace_fri_zero_round_checked_final_obstruction_first_query_target
    [OF assms])
  fix trace_roots trace_bs trace_final dg composition_roots composition_bs
    composition_final fri_query_idxs trace_round_layers composition_round_layers
    fr trace_openings trace_table
  assume fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and rounds_empty: "length trace_bs = 0"
    and checked:
      "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
        trace_openings trace_table trace_final"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
    and first_hit:
      "fri_query_idxs ! 0 \<in>
        fri_final_value_agreement_set trace_table trace_final"
    and card_lt:
      "card (fri_final_value_agreement_set trace_table trace_final) <
        query_sample_space_size"
  show ?thesis
    unfolding trace_fri_zero_round_checked_first_query_target_hit_def
    by (intro exI conjI)
      (rule fri_openings, rule rounds_empty, rule checked, rule not_final,
       rule first_hit, rule card_lt)
qed

lemma wp_trace_fri_zero_round_checked_final_obstruction_bound_from_first_query_target_hit:
  assumes target_bound:
    "wp_event verify_monad
      (trace_fri_zero_round_checked_first_query_target_hit s) s \<le> T"
  shows
    "wp_event verify_monad
      (trace_fri_zero_round_checked_final_obstruction s) s \<le> T"
proof -
  have "wp_event verify_monad
      (trace_fri_zero_round_checked_final_obstruction s) s \<le>
      wp_event verify_monad
        (trace_fri_zero_round_checked_first_query_target_hit s) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_zero_round_checked_final_obstruction_imp_first_query_target_hit)
  then show ?thesis
    by (rule order_trans[OF _ target_bound])
qed

lemma trace_fri_zero_round_final_obstruction_agreement_set_card_lt:
  assumes obstruction: "trace_fri_zero_round_final_obstruction s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
  where
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    "length trace_bs = 0"
    "\<not> fri_final_constant_consistent trace_table trace_final"
    "card (fri_final_value_agreement_set trace_table trace_final) <
      query_sample_space_size"
proof -
  from obstruction obtain trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr candidate_query_idxs
      trace_openings trace_table where evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    and rounds_empty: "length trace_bs = 0"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
    unfolding trace_fri_zero_round_final_obstruction_def by blast
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    by (rule trace_fri_partial_candidate_opening_evidenceD(1)
        [OF evidence])
  have partial:
    "trace_fri_partial_candidate_evidence s out fr candidate_query_idxs
      trace_openings trace_table"
    by (rule trace_fri_partial_candidate_opening_evidenceD(2)
        [OF evidence])
  have cand:
    "partial_trace_table_candidate trace_table trace_openings"
    by (rule trace_fri_partial_candidate_evidenceD(2)[OF partial])
  have table_len:
    "length trace_table = query_sample_space_size"
    by (rule trace_zero_round_table_len_equals_query_sample_space
        [OF rounds_empty fri_openings cand])
  have card_lt:
    "card (fri_final_value_agreement_set trace_table trace_final) <
      query_sample_space_size"
    by (rule fri_final_value_agreement_set_card_lt_if_not_constant_whole_sample
        [OF table_len not_final])
  show ?thesis
    by (rule that[OF evidence rounds_empty not_final card_lt])
qed

lemma trace_fri_zero_round_final_obstructionE:
  assumes "trace_fri_zero_round_final_obstruction s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
  where
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    "length trace_bs = 0"
    "\<not> fri_final_constant_consistent trace_table trace_final"
  using assms
  unfolding trace_fri_zero_round_final_obstruction_def by blast

definition trace_fri_zero_round_candidate_small_agreement_set
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_zero_round_candidate_small_agreement_set s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      length trace_bs = 0 \<and>
      \<not> fri_final_constant_consistent trace_table trace_final \<and>
      card (fri_final_value_agreement_set trace_table trace_final) <
        query_sample_space_size)"

definition trace_fri_zero_round_candidate_first_query_target_hit
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_zero_round_candidate_first_query_target_hit s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      length trace_bs = 0 \<and>
      \<not> fri_final_constant_consistent trace_table trace_final \<and>
      candidate_query_idxs ! 0 \<in>
        fri_final_value_agreement_set trace_table trace_final \<and>
      card (fri_final_value_agreement_set trace_table trace_final) <
        query_sample_space_size)"

definition trace_fri_zero_round_candidate_first_query_alignment_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_zero_round_candidate_first_query_alignment_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      length trace_bs = 0 \<and>
      \<not> fri_final_constant_consistent trace_table trace_final \<and>
      candidate_query_idxs ! 0 \<in>
        fri_final_value_agreement_set trace_table trace_final \<and>
      fri_query_idxs ! 0 \<notin>
        fri_final_value_agreement_set trace_table trace_final \<and>
      card (fri_final_value_agreement_set trace_table trace_final) <
        query_sample_space_size)"

definition trace_fri_zero_round_candidate_first_query_value_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_zero_round_candidate_first_query_value_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      length trace_bs = 0 \<and>
      \<not> fri_final_constant_consistent trace_table trace_final \<and>
      candidate_query_idxs ! 0 \<notin>
        fri_final_value_agreement_set trace_table trace_final \<and>
      card (fri_final_value_agreement_set trace_table trace_final) <
        query_sample_space_size)"

lemma trace_fri_zero_round_candidate_small_agreement_setE:
  assumes "trace_fri_zero_round_candidate_small_agreement_set s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
  where
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    "length trace_bs = 0"
    "\<not> fri_final_constant_consistent trace_table trace_final"
    "card (fri_final_value_agreement_set trace_table trace_final) <
      query_sample_space_size"
  using assms
  unfolding trace_fri_zero_round_candidate_small_agreement_set_def
  by blast

lemma trace_fri_zero_round_candidate_first_query_target_hitE:
  assumes "trace_fri_zero_round_candidate_first_query_target_hit s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
  where
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    "length trace_bs = 0"
    "\<not> fri_final_constant_consistent trace_table trace_final"
    "candidate_query_idxs ! 0 \<in>
      fri_final_value_agreement_set trace_table trace_final"
    "card (fri_final_value_agreement_set trace_table trace_final) <
      query_sample_space_size"
  using assms
  unfolding trace_fri_zero_round_candidate_first_query_target_hit_def
  by blast

lemma trace_fri_zero_round_candidate_first_query_alignment_gapE:
  assumes "trace_fri_zero_round_candidate_first_query_alignment_gap s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
  where
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    "length trace_bs = 0"
    "\<not> fri_final_constant_consistent trace_table trace_final"
    "candidate_query_idxs ! 0 \<in>
      fri_final_value_agreement_set trace_table trace_final"
    "fri_query_idxs ! 0 \<notin>
      fri_final_value_agreement_set trace_table trace_final"
    "card (fri_final_value_agreement_set trace_table trace_final) <
      query_sample_space_size"
  using assms
  unfolding trace_fri_zero_round_candidate_first_query_alignment_gap_def
  by blast

lemma trace_fri_zero_round_candidate_first_query_value_gapE:
  assumes "trace_fri_zero_round_candidate_first_query_value_gap s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
  where
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    "length trace_bs = 0"
    "\<not> fri_final_constant_consistent trace_table trace_final"
    "candidate_query_idxs ! 0 \<notin>
      fri_final_value_agreement_set trace_table trace_final"
    "card (fri_final_value_agreement_set trace_table trace_final) <
      query_sample_space_size"
  using assms
  unfolding trace_fri_zero_round_candidate_first_query_value_gap_def
  by blast

lemma trace_fri_zero_round_candidate_first_query_target_hit_imp_small:
  assumes "trace_fri_zero_round_candidate_first_query_target_hit s out"
  shows "trace_fri_zero_round_candidate_small_agreement_set s out"
proof (rule trace_fri_zero_round_candidate_first_query_target_hitE[OF assms])
  fix trace_roots trace_bs trace_final dg composition_roots
    composition_bs composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr candidate_query_idxs trace_openings
    trace_table
  assume evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    and rounds_empty: "length trace_bs = 0"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
    and card_lt:
      "card (fri_final_value_agreement_set trace_table trace_final) <
        query_sample_space_size"
  show ?thesis
    unfolding trace_fri_zero_round_candidate_small_agreement_set_def
    by (intro exI conjI)
      (rule evidence, rule rounds_empty, rule not_final, rule card_lt)
qed

lemma trace_fri_zero_round_checked_first_query_target_hit_imp_candidate:
  assumes "trace_fri_zero_round_checked_first_query_target_hit s out"
  shows "trace_fri_zero_round_candidate_first_query_target_hit s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_openings trace_table
  where fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and rounds_empty: "length trace_bs = 0"
    and checked:
      "trace_zero_round_final_checked_candidate s out fr fri_query_idxs
        trace_openings trace_table trace_final"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
    and first_hit:
      "fri_query_idxs ! 0 \<in>
        fri_final_value_agreement_set trace_table trace_final"
    and card_lt:
      "card (fri_final_value_agreement_set trace_table trace_final) <
        query_sample_space_size"
    unfolding trace_fri_zero_round_checked_first_query_target_hit_def
    by blast
  have partial:
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    using checked unfolding trace_zero_round_final_checked_candidate_def
    by simp
  have candidate:
    "partial_trace_table_candidate trace_table trace_openings"
    using checked unfolding trace_zero_round_final_checked_candidate_def
    by simp
  have not_low:
    "\<not> trace_table_low_degree trace_table"
    by (rule trace_zero_round_checked_candidate_not_trace_low_degree
        [OF rounds_empty fri_openings checked not_final])
  have evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr fri_query_idxs trace_openings trace_table"
    unfolding trace_fri_partial_candidate_opening_evidence_def
      trace_fri_partial_candidate_evidence_def
    by (intro conjI fri_openings partial candidate not_low)
  show ?thesis
    unfolding trace_fri_zero_round_candidate_first_query_target_hit_def
    by (intro exI conjI)
      (rule evidence, rule rounds_empty, rule not_final, rule first_hit,
        rule card_lt)
qed

lemma trace_fri_zero_round_final_obstruction_imp_candidate_small_agreement_set:
  assumes "trace_fri_zero_round_final_obstruction s out"
  shows "trace_fri_zero_round_candidate_small_agreement_set s out"
proof (rule trace_fri_zero_round_final_obstruction_agreement_set_card_lt
    [OF assms])
  fix trace_roots trace_bs trace_final dg composition_roots
    composition_bs composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr candidate_query_idxs trace_openings
    trace_table
  assume evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    and rounds_empty: "length trace_bs = 0"
    and not_final:
      "\<not> fri_final_constant_consistent trace_table trace_final"
    and card_lt:
      "card (fri_final_value_agreement_set trace_table trace_final) <
        query_sample_space_size"
  show ?thesis
    unfolding trace_fri_zero_round_candidate_small_agreement_set_def
    by (intro exI conjI)
      (rule evidence, rule rounds_empty, rule not_final, rule card_lt)
qed

lemma wp_trace_fri_zero_round_final_obstruction_bound_from_candidate_small_agreement_set:
  assumes small_bound:
    "wp_event verify_monad
      (trace_fri_zero_round_candidate_small_agreement_set s) s \<le> T"
  shows
    "wp_event verify_monad
      (trace_fri_zero_round_final_obstruction s) s \<le> T"
proof -
  have "wp_event verify_monad
      (trace_fri_zero_round_final_obstruction s) s \<le>
      wp_event verify_monad
        (trace_fri_zero_round_candidate_small_agreement_set s) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_zero_round_final_obstruction_imp_candidate_small_agreement_set)
  then show ?thesis
    by (rule order_trans[OF _ small_bound])
qed

end

end
