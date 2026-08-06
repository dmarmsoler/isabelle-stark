(*  Title:      Stark/Soundness_FRI_Full_Cover_Reasons.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Full_Cover_Reasons
  imports Soundness_FRI_Refined_Reachable
begin

section \<open>FRI Cover and Verifier-Tied Reductions\<close>

text \<open>
  Diagnostic split for missing full sampled FRI cover.

  The predicates below do not add assumptions.  They expose which clause of
  @{term generic_fri_sampled_layer_chain_full_cover} must fail when verifier
  sampled layer-chain evidence exists but the corresponding full-cover witness
  is absent.  Later proof layers should bound these failures by existing
  Merkle/hash/proximity side events.
\<close>

context soundness
begin

definition generic_fri_sampled_full_cover_failure
  :: "('f list \<Rightarrow> bool) \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list \<Rightarrow> 'f list list \<Rightarrow>
      (nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> bool"
where
  "generic_fri_sampled_full_cover_failure low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad \<longleftrightarrow>
    \<not> fri_multiround_proximity_steps (length challenges) degree_bound
      (fri_layer_lengths (length challenges) (clength * scale))
      (map (\<lambda>i. 2 ^ i) [0..<length challenges])
      doms layers bad \<or>
    \<not> fri_sampled_layers_cover_fold_indices roots query_idxs \<or>
    \<not> (\<forall>layer_idx < length challenges.
      2 dvd fri_evidence_layer_len roots layer_idx) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx * 2 ^ layer_idx =
        clength * scale) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx \<le>
        length (doms ! layer_idx)) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx \<le>
        length (layers ! layer_idx)) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx div 2 \<le>
        length (doms ! Suc layer_idx)) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx div 2 \<le>
        length (layers ! Suc layer_idx)) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      \<forall>idx < fri_evidence_layer_len roots layer_idx div 2.
        doms ! Suc layer_idx ! idx =
          (doms ! layer_idx ! idx)\<^sup>2) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      \<forall>idx < fri_evidence_layer_len roots layer_idx div 2.
        doms ! layer_idx ! idx = (h ^ idx * shift) ^ (2 ^ layer_idx)) \<or>
    fri_table_low_degree_on degree_bound eval_domain candidate_table \<or>
    \<not> fri_table_low_degree_on
      (fri_degree_after (length challenges) degree_bound)
      (doms ! length challenges) (layers ! length challenges)"

definition generic_fri_full_cover_proximity_failure
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow> 'f list list \<Rightarrow>
      (nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> bool"
where
  "generic_fri_full_cover_proximity_failure degree_bound challenges
      doms layers bad \<longleftrightarrow>
    \<not> fri_multiround_proximity_steps (length challenges) degree_bound
      (fri_layer_lengths (length challenges) (clength * scale))
      (map (\<lambda>i. 2 ^ i) [0..<length challenges])
      doms layers bad"

definition generic_fri_full_cover_index_failure
  :: "'f list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "generic_fri_full_cover_index_failure roots query_idxs \<longleftrightarrow>
    \<not> fri_sampled_layers_cover_fold_indices roots query_idxs"

definition generic_fri_full_cover_shape_failure
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "generic_fri_full_cover_shape_failure roots challenges doms layers \<longleftrightarrow>
    \<not> (\<forall>layer_idx < length challenges.
      2 dvd fri_evidence_layer_len roots layer_idx) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx * 2 ^ layer_idx =
        clength * scale) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx \<le>
        length (doms ! layer_idx)) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx \<le>
        length (layers ! layer_idx)) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx div 2 \<le>
        length (doms ! Suc layer_idx)) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      fri_evidence_layer_len roots layer_idx div 2 \<le>
        length (layers ! Suc layer_idx)) \<or>
    length (doms ! length challenges) \<noteq>
      length (layers ! length challenges)"

definition generic_fri_full_cover_arithmetic_shape_failure
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> bool"
where
  "generic_fri_full_cover_arithmetic_shape_failure roots challenges
    \<longleftrightarrow>
      \<not> (\<forall>layer_idx < length challenges.
        2 dvd fri_evidence_layer_len roots layer_idx) \<or>
      \<not> (\<forall>layer_idx < length challenges.
        fri_evidence_layer_len roots layer_idx * 2 ^ layer_idx =
          clength * scale)"

definition generic_fri_full_cover_witness_length_failure
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "generic_fri_full_cover_witness_length_failure roots challenges doms layers
    \<longleftrightarrow>
      \<not> (\<forall>layer_idx < length challenges.
        fri_evidence_layer_len roots layer_idx \<le>
          length (doms ! layer_idx)) \<or>
      \<not> (\<forall>layer_idx < length challenges.
        fri_evidence_layer_len roots layer_idx \<le>
          length (layers ! layer_idx)) \<or>
      \<not> (\<forall>layer_idx < length challenges.
        fri_evidence_layer_len roots layer_idx div 2 \<le>
          length (doms ! Suc layer_idx)) \<or>
      \<not> (\<forall>layer_idx < length challenges.
        fri_evidence_layer_len roots layer_idx div 2 \<le>
          length (layers ! Suc layer_idx)) \<or>
      length (doms ! length challenges) \<noteq>
        length (layers ! length challenges)"

lemma generic_fri_full_cover_shape_failure_split:
  assumes "generic_fri_full_cover_shape_failure roots challenges doms layers"
  shows
    "generic_fri_full_cover_arithmetic_shape_failure roots challenges \<or>
     generic_fri_full_cover_witness_length_failure roots challenges
      doms layers"
  using assms
  unfolding generic_fri_full_cover_shape_failure_def
    generic_fri_full_cover_arithmetic_shape_failure_def
    generic_fri_full_cover_witness_length_failure_def
  by blast

lemma ceil_log_Suc_le_power_local:
  assumes "d < 2 ^ N"
  shows "ceil_log (Suc d) \<le> N"
proof (cases "d = 0")
  case True
  then show ?thesis
    unfolding ceil_log_def by simp
next
  case False
  then have d_pos: "0 < d"
    by simp
  have "2 ^ floor_log d \<le> d"
    by (rule floor_log_exp2_le[OF d_pos])
  also have "... < 2 ^ N"
    using assms .
  finally have "floor_log d < N"
    by (subst (asm) power_strict_increasing_iff) simp_all
  then show ?thesis
    using False unfolding ceil_log_def by simp
qed

lemma ceil_log_le_power_bound:
  assumes "n \<le> 2 ^ N"
  shows "ceil_log n \<le> N"
proof (cases n)
  case 0
  then show ?thesis
    unfolding ceil_log_def by simp
next
  case (Suc d)
  then have "d < 2 ^ N"
    using assms by simp
  then show ?thesis
    unfolding Suc by (rule ceil_log_Suc_le_power_local)
qed

lemma generic_fri_full_cover_arithmetic_shape_failure_false:
  assumes challenges_len: "length challenges = length roots"
    and eval_power: "clength * scale = 2 ^ N"
    and rounds_bound: "length challenges \<le> N"
  shows "\<not> generic_fri_full_cover_arithmetic_shape_failure roots challenges"
proof -
  have even:
    "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
      2 dvd fri_evidence_layer_len roots layer_idx"
  proof -
    fix layer_idx
    assume layer_bound: "layer_idx < length challenges"
    have layer_root_bound: "layer_idx < length roots"
      using layer_bound challenges_len by simp
    have suc_le: "Suc layer_idx \<le> N"
      using layer_bound rounds_bound by simp
    have "(2::nat) ^ Suc layer_idx dvd (2::nat) ^ N"
      by (rule le_imp_power_dvd[OF suc_le])
    then have dvd_eval: "2 ^ Suc layer_idx dvd clength * scale"
      using eval_power by simp
    show "2 dvd fri_evidence_layer_len roots layer_idx"
      unfolding fri_evidence_layer_len_def
      by (rule fri_layer_lengths_even_if_dvd[OF layer_root_bound dvd_eval])
  qed
  have product:
    "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
      fri_evidence_layer_len roots layer_idx * 2 ^ layer_idx =
        clength * scale"
  proof -
    fix layer_idx
    assume layer_bound: "layer_idx < length challenges"
    have layer_root_bound: "layer_idx < length roots"
      using layer_bound challenges_len by simp
    have le_N: "layer_idx \<le> N"
      using layer_bound rounds_bound by simp
    have "(2::nat) ^ layer_idx dvd (2::nat) ^ N"
      by (rule le_imp_power_dvd[OF le_N])
    then have dvd_eval: "2 ^ layer_idx dvd clength * scale"
      using eval_power by simp
    show "fri_evidence_layer_len roots layer_idx * 2 ^ layer_idx =
        clength * scale"
      unfolding fri_evidence_layer_len_def
      by (rule fri_layer_lengths_round_product_if_dvd
          [OF layer_root_bound dvd_eval])
  qed
  show ?thesis
    unfolding generic_fri_full_cover_arithmetic_shape_failure_def
    using even product by simp
qed

definition generic_fri_full_cover_domain_failure
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "generic_fri_full_cover_domain_failure roots challenges doms \<longleftrightarrow>
    \<not> (\<forall>layer_idx < length challenges.
      \<forall>idx < fri_evidence_layer_len roots layer_idx div 2.
        doms ! Suc layer_idx ! idx =
          (doms ! layer_idx ! idx)\<^sup>2) \<or>
    \<not> (\<forall>layer_idx < length challenges.
      \<forall>idx < fri_evidence_layer_len roots layer_idx div 2.
        doms ! layer_idx ! idx = (h ^ idx * shift) ^ (2 ^ layer_idx))"

definition generic_fri_full_cover_start_low_failure
  :: "nat \<Rightarrow> 'f list \<Rightarrow> bool"
where
  "generic_fri_full_cover_start_low_failure degree_bound candidate_table
    \<longleftrightarrow> fri_table_low_degree_on degree_bound eval_domain candidate_table"

definition generic_fri_full_cover_final_low_failure
  :: "nat \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "generic_fri_full_cover_final_low_failure degree_bound challenges
      doms layers \<longleftrightarrow>
    \<not> fri_table_low_degree_on
      (fri_degree_after (length challenges) degree_bound)
      (doms ! length challenges) (layers ! length challenges)"

definition generic_fri_full_cover_final_length_failure
  :: "'f list \<Rightarrow> 'f list list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "generic_fri_full_cover_final_length_failure challenges doms layers
    \<longleftrightarrow>
      length (doms ! length challenges) \<noteq>
        length (layers ! length challenges)"

lemma fri_final_constant_consistent_low_degree_if_lengths:
  assumes final: "fri_final_constant_consistent table final_value"
    and len: "length table = length fri_dom"
  shows "fri_table_low_degree_on d fri_dom table"
proof -
  have table: "table = map (poly [:final_value:]) fri_dom"
  proof (rule nth_equalityI)
    show "length table = length (map (poly [:final_value:]) fri_dom)"
      using len by simp
  next
    fix i
    assume i_bound: "i < length table"
    have "table ! i = final_value"
      by (rule fri_final_constant_consistent_nth[OF final i_bound])
    then show "table ! i = map (poly [:final_value:]) fri_dom ! i"
      using i_bound len by simp
  qed
  show ?thesis
    unfolding fri_table_low_degree_on_def
    using table by (intro exI[where x="[:final_value:]"]) simp
qed

lemma generic_fri_final_low_failure_imp_length_failure:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
    and final_low:
      "generic_fri_full_cover_final_low_failure degree_bound challenges
        doms layers"
  shows "generic_fri_full_cover_final_length_failure challenges doms layers"
proof (unfold generic_fri_full_cover_final_length_failure_def, rule notI)
  assume len:
    "length (doms ! length challenges) =
      length (layers ! length challenges)"
  have final:
    "fri_final_constant_consistent (layers ! length challenges) final_value"
    by (rule generic_fri_sampled_layer_chain_evidenceD(6)[OF chain])
  have low:
    "fri_table_low_degree_on
      (fri_degree_after (length challenges) degree_bound)
      (doms ! length challenges) (layers ! length challenges)"
    by (rule fri_final_constant_consistent_low_degree_if_lengths[OF final])
      (rule len[symmetric])
  show False
    using final_low low
    unfolding generic_fri_full_cover_final_low_failure_def by contradiction
qed

definition generic_fri_sampled_full_cover_failure_case
  :: "('f list \<Rightarrow> bool) \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list \<Rightarrow> 'f list list \<Rightarrow>
      (nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> bool"
where
  "generic_fri_sampled_full_cover_failure_case low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad \<longleftrightarrow>
    generic_fri_full_cover_proximity_failure degree_bound challenges
      doms layers bad \<or>
    generic_fri_full_cover_index_failure roots query_idxs \<or>
    generic_fri_full_cover_shape_failure roots challenges doms layers \<or>
    generic_fri_full_cover_domain_failure roots challenges doms \<or>
    generic_fri_full_cover_start_low_failure degree_bound candidate_table \<or>
    generic_fri_full_cover_final_low_failure degree_bound challenges
      doms layers"

lemma generic_fri_sampled_full_cover_failure_iff_case:
  "generic_fri_sampled_full_cover_failure low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad \<longleftrightarrow>
    generic_fri_sampled_full_cover_failure_case low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
  unfolding generic_fri_sampled_full_cover_failure_def
    generic_fri_sampled_full_cover_failure_case_def
    generic_fri_full_cover_proximity_failure_def
    generic_fri_full_cover_index_failure_def
    generic_fri_full_cover_shape_failure_def
    generic_fri_full_cover_domain_failure_def
    generic_fri_full_cover_start_low_failure_def
    generic_fri_full_cover_final_low_failure_def
    fri_table_low_degree_on_def
  by auto

lemma generic_fri_sampled_full_cover_failure_cases:
  assumes
    "generic_fri_sampled_full_cover_failure low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
  shows
    "generic_fri_full_cover_proximity_failure degree_bound challenges
      doms layers bad \<or>
     generic_fri_full_cover_index_failure roots query_idxs \<or>
     generic_fri_full_cover_shape_failure roots challenges doms layers \<or>
     generic_fri_full_cover_domain_failure roots challenges doms \<or>
     generic_fri_full_cover_start_low_failure degree_bound candidate_table \<or>
     generic_fri_full_cover_final_low_failure degree_bound challenges
      doms layers"
  using assms
  unfolding generic_fri_sampled_full_cover_failure_iff_case
    generic_fri_sampled_full_cover_failure_case_def
  by blast

definition trace_fri_sampled_full_cover_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_failure s bad out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<and>
      generic_fri_sampled_full_cover_failure trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers (bad trace_table))"

definition trace_fri_sampled_full_cover_failure_case
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_failure_case s bad out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<and>
      generic_fri_sampled_full_cover_failure_case trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers (bad trace_table))"

definition trace_fri_sampled_full_cover_proximity_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_proximity_failure s bad out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<and>
      generic_fri_full_cover_proximity_failure (clength - 1) trace_bs
        doms layers (bad trace_table))"

definition trace_fri_sampled_full_cover_index_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_index_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<and>
      generic_fri_full_cover_index_failure trace_roots fri_query_idxs)"

definition trace_fri_sampled_full_cover_shape_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_shape_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<and>
      generic_fri_full_cover_shape_failure trace_roots trace_bs
        doms layers)"

definition trace_fri_sampled_full_cover_arithmetic_shape_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_arithmetic_shape_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<and>
      generic_fri_full_cover_arithmetic_shape_failure trace_roots trace_bs)"

definition trace_fri_sampled_full_cover_witness_length_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_witness_length_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<and>
      generic_fri_full_cover_witness_length_failure trace_roots trace_bs
        doms layers)"

definition trace_fri_sampled_full_cover_domain_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_domain_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<and>
      generic_fri_full_cover_domain_failure trace_roots trace_bs doms)"

definition trace_fri_sampled_full_cover_start_low_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_start_low_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<and>
      generic_fri_full_cover_start_low_failure (clength - 1) trace_table)"

definition trace_fri_sampled_full_cover_final_low_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_final_low_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<and>
      generic_fri_full_cover_final_low_failure (clength - 1) trace_bs
        doms layers)"

definition trace_fri_sampled_full_cover_final_length_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_final_length_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<and>
      generic_fri_full_cover_final_length_failure trace_bs doms layers)"

definition composition_fri_sampled_full_cover_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_failure s bad out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table doms layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        \<and>
      generic_fri_sampled_full_cover_failure
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        (bad fri_dg composition_table))"

definition composition_fri_sampled_full_cover_failure_case
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_failure_case s bad out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table doms layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        \<and>
      generic_fri_sampled_full_cover_failure_case
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        (bad fri_dg composition_table))"

definition composition_fri_sampled_full_cover_proximity_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_proximity_failure s bad out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table doms layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        \<and>
      generic_fri_full_cover_proximity_failure (to_nat fri_dg)
        composition_bs doms layers (bad fri_dg composition_table))"

definition composition_fri_sampled_full_cover_index_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_index_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table doms layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        \<and>
      generic_fri_full_cover_index_failure opening_composition_roots
        fri_query_idxs)"

definition composition_fri_sampled_full_cover_shape_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_shape_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table doms layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        \<and>
      generic_fri_full_cover_shape_failure opening_composition_roots
        composition_bs doms layers)"

definition composition_fri_sampled_full_cover_arithmetic_shape_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_arithmetic_shape_failure s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table doms layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        \<and>
      generic_fri_full_cover_arithmetic_shape_failure
        opening_composition_roots composition_bs)"

definition composition_fri_sampled_full_cover_witness_length_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_witness_length_failure s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table doms layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        \<and>
      generic_fri_full_cover_witness_length_failure
        opening_composition_roots composition_bs doms layers)"

definition composition_fri_sampled_full_cover_domain_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_domain_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table doms layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        \<and>
      generic_fri_full_cover_domain_failure opening_composition_roots
        composition_bs doms)"

definition composition_fri_sampled_full_cover_start_low_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_start_low_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table doms layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        \<and>
      generic_fri_full_cover_start_low_failure (to_nat fri_dg)
        composition_table)"

definition composition_fri_sampled_full_cover_final_low_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_final_low_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table doms layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        \<and>
      generic_fri_full_cover_final_low_failure (to_nat fri_dg)
        composition_bs doms layers)"

definition composition_fri_sampled_full_cover_final_length_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_final_length_failure s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table doms layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        \<and>
      generic_fri_full_cover_final_length_failure composition_bs doms
        layers)"

lemma trace_fri_sampled_full_cover_failure_iff_case:
  "trace_fri_sampled_full_cover_failure s bad out \<longleftrightarrow>
    trace_fri_sampled_full_cover_failure_case s bad out"
  unfolding trace_fri_sampled_full_cover_failure_def
    trace_fri_sampled_full_cover_failure_case_def
  by (simp only: generic_fri_sampled_full_cover_failure_iff_case)

lemma composition_fri_sampled_full_cover_failure_iff_case:
  "composition_fri_sampled_full_cover_failure s bad out \<longleftrightarrow>
    composition_fri_sampled_full_cover_failure_case s bad out"
  unfolding composition_fri_sampled_full_cover_failure_def
    composition_fri_sampled_full_cover_failure_case_def
  by (simp only: generic_fri_sampled_full_cover_failure_iff_case)

lemma trace_fri_sampled_full_cover_failure_case_split:
  assumes "trace_fri_sampled_full_cover_failure_case s bad out"
  shows
    "trace_fri_sampled_full_cover_proximity_failure s bad out \<or>
     trace_fri_sampled_full_cover_index_failure s out \<or>
     trace_fri_sampled_full_cover_shape_failure s out \<or>
     trace_fri_sampled_full_cover_domain_failure s out \<or>
     trace_fri_sampled_full_cover_start_low_failure s out \<or>
     trace_fri_sampled_full_cover_final_low_failure s out"
  using assms
  unfolding trace_fri_sampled_full_cover_failure_case_def
    trace_fri_sampled_full_cover_proximity_failure_def
    trace_fri_sampled_full_cover_index_failure_def
    trace_fri_sampled_full_cover_shape_failure_def
    trace_fri_sampled_full_cover_domain_failure_def
    trace_fri_sampled_full_cover_start_low_failure_def
    trace_fri_sampled_full_cover_final_low_failure_def
    generic_fri_sampled_full_cover_failure_case_def
  by meson

lemma composition_fri_sampled_full_cover_failure_case_split:
  assumes "composition_fri_sampled_full_cover_failure_case s bad out"
  shows
    "composition_fri_sampled_full_cover_proximity_failure s bad out \<or>
     composition_fri_sampled_full_cover_index_failure s out \<or>
     composition_fri_sampled_full_cover_shape_failure s out \<or>
     composition_fri_sampled_full_cover_domain_failure s out \<or>
     composition_fri_sampled_full_cover_start_low_failure s out \<or>
     composition_fri_sampled_full_cover_final_low_failure s out"
  using assms
  unfolding composition_fri_sampled_full_cover_failure_case_def
    composition_fri_sampled_full_cover_proximity_failure_def
    composition_fri_sampled_full_cover_index_failure_def
    composition_fri_sampled_full_cover_shape_failure_def
    composition_fri_sampled_full_cover_domain_failure_def
    composition_fri_sampled_full_cover_start_low_failure_def
    composition_fri_sampled_full_cover_final_low_failure_def
    generic_fri_sampled_full_cover_failure_case_def
  by meson

lemma trace_fri_sampled_full_cover_shape_failure_split:
  assumes "trace_fri_sampled_full_cover_shape_failure s out"
  shows
    "trace_fri_sampled_full_cover_arithmetic_shape_failure s out \<or>
     trace_fri_sampled_full_cover_witness_length_failure s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table doms layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
    and shape:
      "generic_fri_full_cover_shape_failure trace_roots trace_bs
        doms layers"
    unfolding trace_fri_sampled_full_cover_shape_failure_def by blast
  have split:
    "generic_fri_full_cover_arithmetic_shape_failure trace_roots trace_bs \<or>
     generic_fri_full_cover_witness_length_failure trace_roots trace_bs
      doms layers"
    by (rule generic_fri_full_cover_shape_failure_split[OF shape])
  then show ?thesis
    unfolding trace_fri_sampled_full_cover_arithmetic_shape_failure_def
      trace_fri_sampled_full_cover_witness_length_failure_def
    using evidence chain by meson
qed

lemma composition_fri_sampled_full_cover_shape_failure_split:
  assumes "composition_fri_sampled_full_cover_shape_failure s out"
  shows
    "composition_fri_sampled_full_cover_arithmetic_shape_failure s out \<or>
     composition_fri_sampled_full_cover_witness_length_failure s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table doms layers
    where evidence:
      "composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table"
    and chain:
      "generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers"
    and shape:
      "generic_fri_full_cover_shape_failure opening_composition_roots
        composition_bs doms layers"
    unfolding composition_fri_sampled_full_cover_shape_failure_def
    by meson
  have split:
    "generic_fri_full_cover_arithmetic_shape_failure
      opening_composition_roots composition_bs \<or>
     generic_fri_full_cover_witness_length_failure
      opening_composition_roots composition_bs doms layers"
    by (rule generic_fri_full_cover_shape_failure_split[OF shape])
  then show ?thesis
    unfolding
      composition_fri_sampled_full_cover_arithmetic_shape_failure_def
      composition_fri_sampled_full_cover_witness_length_failure_def
    using evidence chain by meson
qed

lemma wp_trace_fri_sampled_full_cover_shape_bound_from_split:
  assumes arithmetic:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_arithmetic_shape_failure s) s \<le> A"
    and witness:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_witness_length_failure s) s \<le> W"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_shape_failure s) s \<le> A + W"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_full_cover_shape_failure s) s
    \<le> wp_event verify_monad
      (\<lambda>out.
        trace_fri_sampled_full_cover_arithmetic_shape_failure s out \<or>
        trace_fri_sampled_full_cover_witness_length_failure s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_full_cover_shape_failure_split)
  also have "... \<le> A + W"
    by (rule order_trans[OF wp_event_union_bound
        add_mono[OF arithmetic witness]])
  finally show ?thesis .
qed

lemma wp_composition_fri_sampled_full_cover_shape_bound_from_split:
  assumes arithmetic:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_arithmetic_shape_failure s) s
      \<le> A"
    and witness:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_witness_length_failure s) s
      \<le> W"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_shape_failure s) s \<le> A + W"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_full_cover_shape_failure s) s
    \<le> wp_event verify_monad
      (\<lambda>out.
        composition_fri_sampled_full_cover_arithmetic_shape_failure s out \<or>
        composition_fri_sampled_full_cover_witness_length_failure s out) s"
    by (rule wp_event_mono)
      (rule composition_fri_sampled_full_cover_shape_failure_split)
  also have "... \<le> A + W"
    by (rule order_trans[OF wp_event_union_bound
        add_mono[OF arithmetic witness]])
  finally show ?thesis .
qed

lemma wp_event_six_union_bound:
  assumes A: "wp_event m A s \<le> a"
    and B: "wp_event m B s \<le> b"
    and C: "wp_event m C s \<le> c"
    and D: "wp_event m D s \<le> d"
    and E: "wp_event m E s \<le> e"
    and F: "wp_event m F s \<le> f"
  shows "wp_event m
      (\<lambda>x. A x \<or> B x \<or> C x \<or> D x \<or> E x \<or> F x) s
    \<le> a + b + c + d + e + f"
proof -
  have EF:
    "wp_event m (\<lambda>x. E x \<or> F x) s \<le> e + f"
    by (rule order_trans[OF wp_event_union_bound add_mono[OF E F]])
  have DEF:
    "wp_event m (\<lambda>x. D x \<or> E x \<or> F x) s \<le> d + e + f"
  proof -
    have "wp_event m (\<lambda>x. D x \<or> E x \<or> F x) s
      \<le> wp_event m D s + wp_event m (\<lambda>x. E x \<or> F x) s"
      by (rule wp_event_union_bound)
    also have "... \<le> d + (e + f)"
      by (rule add_mono[OF D EF])
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  have CDEF:
    "wp_event m (\<lambda>x. C x \<or> D x \<or> E x \<or> F x) s
      \<le> c + d + e + f"
  proof -
    have "wp_event m (\<lambda>x. C x \<or> D x \<or> E x \<or> F x) s
      \<le> wp_event m C s + wp_event m (\<lambda>x. D x \<or> E x \<or> F x) s"
      by (rule wp_event_union_bound)
    also have "... \<le> c + (d + e + f)"
      by (rule add_mono[OF C DEF])
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  have BCDEF:
    "wp_event m (\<lambda>x. B x \<or> C x \<or> D x \<or> E x \<or> F x) s
      \<le> b + c + d + e + f"
  proof -
    have "wp_event m (\<lambda>x. B x \<or> C x \<or> D x \<or> E x \<or> F x) s
      \<le> wp_event m B s +
        wp_event m (\<lambda>x. C x \<or> D x \<or> E x \<or> F x) s"
      by (rule wp_event_union_bound)
    also have "... \<le> b + (c + d + e + f)"
      by (rule add_mono[OF B CDEF])
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  have "wp_event m
      (\<lambda>x. A x \<or> B x \<or> C x \<or> D x \<or> E x \<or> F x) s
    \<le> wp_event m A s +
      wp_event m (\<lambda>x. B x \<or> C x \<or> D x \<or> E x \<or> F x) s"
    by (rule wp_event_union_bound)
  also have "... \<le> a + (b + c + d + e + f)"
    by (rule add_mono[OF A BCDEF])
  finally show ?thesis
    by (simp add: add.assoc)
qed

lemma wp_trace_fri_sampled_full_cover_failure_case_union_bound:
  assumes proximity:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
    and domain:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and start_low:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_start_low_failure s) s \<le> SL"
    and final_low:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_final_low_failure s) s \<le> FL"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_failure_case s bad) s
      \<le> P + I + Sh + D + SL + FL"
proof -
  have step1:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_failure_case s bad) s
      \<le>
      wp_event verify_monad
        (\<lambda>out. trace_fri_sampled_full_cover_proximity_failure s bad out \<or>
          trace_fri_sampled_full_cover_index_failure s out \<or>
          trace_fri_sampled_full_cover_shape_failure s out \<or>
          trace_fri_sampled_full_cover_domain_failure s out \<or>
          trace_fri_sampled_full_cover_start_low_failure s out \<or>
          trace_fri_sampled_full_cover_final_low_failure s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_full_cover_failure_case_split)
  have step2:
    "wp_event verify_monad
        (\<lambda>out. trace_fri_sampled_full_cover_proximity_failure s bad out \<or>
          trace_fri_sampled_full_cover_index_failure s out \<or>
          trace_fri_sampled_full_cover_shape_failure s out \<or>
          trace_fri_sampled_full_cover_domain_failure s out \<or>
          trace_fri_sampled_full_cover_start_low_failure s out \<or>
          trace_fri_sampled_full_cover_final_low_failure s out) s
      \<le> P + I + Sh + D + SL + FL"
    by (rule wp_event_six_union_bound
        [OF proximity index shape domain start_low final_low])
  show ?thesis
    by (rule order_trans[OF step1 step2])
qed

lemma wp_composition_fri_sampled_full_cover_failure_case_union_bound:
  assumes proximity:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
    and domain:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and start_low:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_start_low_failure s) s \<le> SL"
    and final_low:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_final_low_failure s) s \<le> FL"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_failure_case s bad) s
      \<le> P + I + Sh + D + SL + FL"
proof -
  have step1:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_failure_case s bad) s
      \<le>
      wp_event verify_monad
        (\<lambda>out.
          composition_fri_sampled_full_cover_proximity_failure s bad out \<or>
          composition_fri_sampled_full_cover_index_failure s out \<or>
          composition_fri_sampled_full_cover_shape_failure s out \<or>
          composition_fri_sampled_full_cover_domain_failure s out \<or>
          composition_fri_sampled_full_cover_start_low_failure s out \<or>
          composition_fri_sampled_full_cover_final_low_failure s out) s"
    by (rule wp_event_mono)
      (rule composition_fri_sampled_full_cover_failure_case_split)
  have step2:
    "wp_event verify_monad
        (\<lambda>out.
          composition_fri_sampled_full_cover_proximity_failure s bad out \<or>
          composition_fri_sampled_full_cover_index_failure s out \<or>
          composition_fri_sampled_full_cover_shape_failure s out \<or>
          composition_fri_sampled_full_cover_domain_failure s out \<or>
          composition_fri_sampled_full_cover_start_low_failure s out \<or>
          composition_fri_sampled_full_cover_final_low_failure s out) s
      \<le> P + I + Sh + D + SL + FL"
    by (rule wp_event_six_union_bound
        [OF proximity index shape domain start_low final_low])
  show ?thesis
    by (rule order_trans[OF step1 step2])
qed

lemma trace_fri_sampled_full_cover_start_low_failure_false:
  "\<not> trace_fri_sampled_full_cover_start_low_failure s out"
proof
  assume failure: "trace_fri_sampled_full_cover_start_low_failure s out"
  then obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table doms layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and start_low:
      "generic_fri_full_cover_start_low_failure (clength - 1)
        trace_table"
    unfolding trace_fri_sampled_full_cover_start_low_failure_def by blast
  have not_low:
    "\<not> fri_table_low_degree_on (clength - 1) eval_domain trace_table"
    by (rule trace_fri_partial_candidate_opening_evidence_not_low_on_eval_domain
        [OF evidence])
  have low:
    "fri_table_low_degree_on (clength - 1) eval_domain trace_table"
    using start_low
    unfolding generic_fri_full_cover_start_low_failure_def .
  show False
    using not_low low by contradiction
qed

lemma wp_trace_fri_sampled_full_cover_start_low_failure_zero:
  "wp_event verify_monad
    (trace_fri_sampled_full_cover_start_low_failure s) s \<le> 0"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_full_cover_start_low_failure s) s
    \<le> wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono)
      (simp add: trace_fri_sampled_full_cover_start_low_failure_false)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis .
qed

lemma composition_fri_sampled_full_cover_start_low_failure_false_on_support:
  assumes outcome:
    "out \<in> set_dist (execute verify_monad s)"
    and failure:
    "composition_fri_sampled_full_cover_start_low_failure s out"
  shows False
proof -
  from failure obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table doms layers
    where evidence:
      "composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table"
    and chain:
      "generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers"
    and start_low:
      "generic_fri_full_cover_start_low_failure (to_nat fri_dg)
        composition_table"
    unfolding composition_fri_sampled_full_cover_start_low_failure_def
    by meson
  have fri_opening:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      fri_dg opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    by (rule composition_fri_partial_candidate_opening_evidenceD(1)
        [OF evidence])
  from fri_opening obtain result final_state where
    out_eq: "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  have outcome':
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using outcome out_eq by simp
  have challenges:
    "accepted_fri_challenges s (Some (result, final_state)) trace_bs
      fri_dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF fri_opening]
      out_eq by simp
  have degree_bound: "to_nat fri_dg \<le> maxDegree"
    by (rule verify_monad_accepted_fri_challenges_degree_bound
        [OF outcome' challenges])
  have not_low:
    "\<not> fri_table_low_degree_on (to_nat fri_dg) eval_domain
      composition_table"
    by (rule
        composition_fri_partial_candidate_opening_evidence_not_low_declared_on_eval_domain
        [OF evidence degree_bound])
  have low:
    "fri_table_low_degree_on (to_nat fri_dg) eval_domain composition_table"
    using start_low
    unfolding generic_fri_full_cover_start_low_failure_def .
  show False
    using not_low low by contradiction
qed

lemma wp_composition_fri_sampled_full_cover_start_low_failure_zero:
  "wp_event verify_monad
    (composition_fri_sampled_full_cover_start_low_failure s) s \<le> 0"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_full_cover_start_low_failure s) s
    \<le> wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono_on_support)
      (rule composition_fri_sampled_full_cover_start_low_failure_false_on_support)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis .
qed

lemma trace_fri_sampled_full_cover_arithmetic_shape_failure_false:
  assumes "trace_fri_sampled_full_cover_arithmetic_shape_failure s out"
  shows False
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table doms layers
    where chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
    and arithmetic:
      "generic_fri_full_cover_arithmetic_shape_failure trace_roots trace_bs"
    unfolding trace_fri_sampled_full_cover_arithmetic_shape_failure_def
    by meson
  have partial:
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have challenges_len: "length trace_bs = length trace_roots"
    using generic_fri_partial_evidence_shapes(2)[OF partial] .
  have rounds_eq: "length trace_bs = ceil_log clength"
    using generic_fri_partial_evidence_shapes(1,2)[OF partial]
    unfolding fri_round_count_for_degree_bound_def
    using clength_pos by simp
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have clength_le_eval: "clength \<le> clength * scale"
    using scale_pos by simp
  have rounds_bound: "length trace_bs \<le> N"
    unfolding rounds_eq
    by (rule ceil_log_le_power_bound)
      (use clength_le_eval eval_power in simp)
  have "\<not> generic_fri_full_cover_arithmetic_shape_failure
      trace_roots trace_bs"
    by (rule generic_fri_full_cover_arithmetic_shape_failure_false
        [OF challenges_len eval_power rounds_bound])
  then show False
    using arithmetic by contradiction
qed

lemma wp_trace_fri_sampled_full_cover_arithmetic_shape_failure_zero:
  "wp_event verify_monad
    (trace_fri_sampled_full_cover_arithmetic_shape_failure s) s \<le> 0"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_full_cover_arithmetic_shape_failure s) s
    \<le> wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_full_cover_arithmetic_shape_failure_false)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis .
qed

lemma composition_fri_sampled_full_cover_arithmetic_shape_failure_false_on_support:
  assumes outcome:
    "out \<in> set_dist (execute verify_monad s)"
    and failure:
    "composition_fri_sampled_full_cover_arithmetic_shape_failure s out"
  shows False
proof -
  from failure obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table doms layers
    where evidence:
      "composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table"
    and chain:
      "generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers"
    and arithmetic:
      "generic_fri_full_cover_arithmetic_shape_failure
        opening_composition_roots composition_bs"
    unfolding composition_fri_sampled_full_cover_arithmetic_shape_failure_def
    by meson
  have partial:
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have challenges_len:
    "length composition_bs = length opening_composition_roots"
    using generic_fri_partial_evidence_shapes(2)[OF partial] .
  have rounds_eq:
    "length composition_bs = ceil_log (to_nat fri_dg + 1)"
    using generic_fri_partial_evidence_shapes(1,2)[OF partial]
    unfolding fri_round_count_for_degree_bound_def by simp
  have fri_opening:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      fri_dg opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    by (rule composition_fri_partial_candidate_opening_evidenceD(1)
        [OF evidence])
  from fri_opening obtain result final_state where
    out_eq: "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  have outcome':
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using outcome out_eq by simp
  have challenges:
    "accepted_fri_challenges s (Some (result, final_state)) trace_bs
      fri_dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF fri_opening]
      out_eq by simp
  have degree_bound: "to_nat fri_dg \<le> maxDegree"
    by (rule verify_monad_accepted_fri_challenges_degree_bound
        [OF outcome' challenges])
  have degree_eval_bound: "to_nat fri_dg + 1 \<le> clength * scale"
    using degree_bound maxDegree_less_eval_domain by linarith
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have rounds_bound: "length composition_bs \<le> N"
    unfolding rounds_eq
    by (rule ceil_log_le_power_bound)
      (use degree_eval_bound eval_power in simp)
  have "\<not> generic_fri_full_cover_arithmetic_shape_failure
      opening_composition_roots composition_bs"
    by (rule generic_fri_full_cover_arithmetic_shape_failure_false
        [OF challenges_len eval_power rounds_bound])
  then show False
    using arithmetic by contradiction
qed

lemma wp_composition_fri_sampled_full_cover_arithmetic_shape_failure_zero:
  "wp_event verify_monad
    (composition_fri_sampled_full_cover_arithmetic_shape_failure s) s \<le> 0"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_full_cover_arithmetic_shape_failure s) s
    \<le> wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono_on_support)
      (rule
        composition_fri_sampled_full_cover_arithmetic_shape_failure_false_on_support)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis .
qed

lemma wp_trace_fri_sampled_full_cover_shape_bound_from_witness_length:
  assumes witness:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_witness_length_failure s) s \<le> W"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_shape_failure s) s \<le> W"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_full_cover_shape_failure s) s \<le> 0 + W"
    by (rule wp_trace_fri_sampled_full_cover_shape_bound_from_split
        [OF wp_trace_fri_sampled_full_cover_arithmetic_shape_failure_zero
          witness])
  then show ?thesis
    by simp
qed

lemma wp_composition_fri_sampled_full_cover_shape_bound_from_witness_length:
  assumes witness:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_witness_length_failure s) s
      \<le> W"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_shape_failure s) s \<le> W"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_full_cover_shape_failure s) s \<le> 0 + W"
    by (rule wp_composition_fri_sampled_full_cover_shape_bound_from_split
        [OF
          wp_composition_fri_sampled_full_cover_arithmetic_shape_failure_zero
          witness])
  then show ?thesis
    by simp
qed

lemma trace_fri_sampled_full_cover_final_low_imp_length:
  assumes "trace_fri_sampled_full_cover_final_low_failure s out"
  shows "trace_fri_sampled_full_cover_final_length_failure s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table doms layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
    and final_low:
      "generic_fri_full_cover_final_low_failure (clength - 1) trace_bs
        doms layers"
    unfolding trace_fri_sampled_full_cover_final_low_failure_def by blast
  have length_failure:
    "generic_fri_full_cover_final_length_failure trace_bs doms layers"
    by (rule generic_fri_final_low_failure_imp_length_failure
        [OF chain final_low])
  show ?thesis
    unfolding trace_fri_sampled_full_cover_final_length_failure_def
    using evidence chain length_failure by blast
qed

lemma composition_fri_sampled_full_cover_final_low_imp_length:
  assumes "composition_fri_sampled_full_cover_final_low_failure s out"
  shows "composition_fri_sampled_full_cover_final_length_failure s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table doms layers
    where evidence:
      "composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table"
    and chain:
      "generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers"
    and final_low:
      "generic_fri_full_cover_final_low_failure (to_nat fri_dg)
        composition_bs doms layers"
    unfolding composition_fri_sampled_full_cover_final_low_failure_def
    by meson
  have length_failure:
    "generic_fri_full_cover_final_length_failure composition_bs doms layers"
    by (rule generic_fri_final_low_failure_imp_length_failure
        [OF chain final_low])
  show ?thesis
    unfolding composition_fri_sampled_full_cover_final_length_failure_def
    using evidence chain length_failure by meson
qed

lemma wp_trace_fri_sampled_full_cover_final_low_bound_from_length:
  assumes length_bound:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_final_length_failure s) s \<le> L"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_final_low_failure s) s \<le> L"
  by (rule order_trans[OF _ length_bound])
    (rule wp_event_mono,
      rule trace_fri_sampled_full_cover_final_low_imp_length)

lemma wp_composition_fri_sampled_full_cover_final_low_bound_from_length:
  assumes length_bound:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_final_length_failure s) s \<le> L"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_final_low_failure s) s \<le> L"
  by (rule order_trans[OF _ length_bound])
    (rule wp_event_mono,
      rule composition_fri_sampled_full_cover_final_low_imp_length)

lemma trace_fri_sampled_full_cover_final_length_imp_shape:
  assumes "trace_fri_sampled_full_cover_final_length_failure s out"
  shows "trace_fri_sampled_full_cover_shape_failure s out"
  using assms
  unfolding trace_fri_sampled_full_cover_final_length_failure_def
    trace_fri_sampled_full_cover_shape_failure_def
    generic_fri_full_cover_final_length_failure_def
    generic_fri_full_cover_shape_failure_def
  by blast

lemma composition_fri_sampled_full_cover_final_length_imp_shape:
  assumes "composition_fri_sampled_full_cover_final_length_failure s out"
  shows "composition_fri_sampled_full_cover_shape_failure s out"
  using assms
  unfolding composition_fri_sampled_full_cover_final_length_failure_def
    composition_fri_sampled_full_cover_shape_failure_def
    generic_fri_full_cover_final_length_failure_def
    generic_fri_full_cover_shape_failure_def
  by meson

lemma trace_fri_sampled_full_cover_final_low_imp_shape:
  assumes "trace_fri_sampled_full_cover_final_low_failure s out"
  shows "trace_fri_sampled_full_cover_shape_failure s out"
  using trace_fri_sampled_full_cover_final_low_imp_length[OF assms]
    trace_fri_sampled_full_cover_final_length_imp_shape
  by blast

lemma composition_fri_sampled_full_cover_final_low_imp_shape:
  assumes "composition_fri_sampled_full_cover_final_low_failure s out"
  shows "composition_fri_sampled_full_cover_shape_failure s out"
  using composition_fri_sampled_full_cover_final_low_imp_length[OF assms]
    composition_fri_sampled_full_cover_final_length_imp_shape
  by blast

lemma trace_fri_sampled_full_cover_failure_case_split_no_final:
  assumes "trace_fri_sampled_full_cover_failure_case s bad out"
  shows
    "trace_fri_sampled_full_cover_proximity_failure s bad out \<or>
     trace_fri_sampled_full_cover_index_failure s out \<or>
     trace_fri_sampled_full_cover_shape_failure s out \<or>
     trace_fri_sampled_full_cover_domain_failure s out \<or>
     trace_fri_sampled_full_cover_start_low_failure s out"
  using trace_fri_sampled_full_cover_failure_case_split[OF assms]
    trace_fri_sampled_full_cover_final_low_imp_shape
  by blast

lemma composition_fri_sampled_full_cover_failure_case_split_no_final:
  assumes "composition_fri_sampled_full_cover_failure_case s bad out"
  shows
    "composition_fri_sampled_full_cover_proximity_failure s bad out \<or>
     composition_fri_sampled_full_cover_index_failure s out \<or>
     composition_fri_sampled_full_cover_shape_failure s out \<or>
     composition_fri_sampled_full_cover_domain_failure s out \<or>
     composition_fri_sampled_full_cover_start_low_failure s out"
  using composition_fri_sampled_full_cover_failure_case_split[OF assms]
    composition_fri_sampled_full_cover_final_low_imp_shape
  by blast

lemma wp_trace_fri_sampled_full_cover_failure_case_union_bound_no_final:
  assumes proximity:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
    and domain:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and start_low:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_start_low_failure s) s \<le> SL"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_failure_case s bad) s
      \<le> P + I + Sh + D + SL"
proof -
  let ?A = "\<lambda>out. trace_fri_sampled_full_cover_proximity_failure s bad out"
  let ?B = "\<lambda>out. trace_fri_sampled_full_cover_index_failure s out"
  let ?C = "\<lambda>out. trace_fri_sampled_full_cover_shape_failure s out"
  let ?D = "\<lambda>out. trace_fri_sampled_full_cover_domain_failure s out"
  let ?E = "\<lambda>out. trace_fri_sampled_full_cover_start_low_failure s out"
  have step1:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_failure_case s bad) s
      \<le> wp_event verify_monad
        (\<lambda>out. ?A out \<or> ?B out \<or> ?C out \<or> ?D out \<or> ?E out) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_full_cover_failure_case_split_no_final)
  have four:
    "wp_event verify_monad
      (\<lambda>out. ?A out \<or> ?B out \<or> ?C out \<or> ?D out) s
      \<le> P + I + Sh + D"
    by (rule order_trans[OF wp_event_union_bound4
          add_mono[OF add_mono[OF add_mono[OF proximity index] shape]
            domain]])
  have five:
    "wp_event verify_monad
      (\<lambda>out. ?A out \<or> ?B out \<or> ?C out \<or> ?D out \<or> ?E out) s
      \<le> P + I + Sh + D + SL"
  proof -
    have "wp_event verify_monad
      (\<lambda>out. ?A out \<or> ?B out \<or> ?C out \<or> ?D out \<or> ?E out) s
      \<le> wp_event verify_monad
        (\<lambda>out. ?A out \<or> ?B out \<or> ?C out \<or> ?D out) s +
        wp_event verify_monad ?E s"
      by (rule order_trans[OF _ wp_event_union_bound])
        (rule wp_event_mono, blast)
    also have "... \<le> (P + I + Sh + D) + SL"
      by (rule add_mono[OF four start_low])
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  show ?thesis
    by (rule order_trans[OF step1 five])
qed

lemma wp_composition_fri_sampled_full_cover_failure_case_union_bound_no_final:
  assumes proximity:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
    and domain:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and start_low:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_start_low_failure s) s \<le> SL"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_failure_case s bad) s
      \<le> P + I + Sh + D + SL"
proof -
  let ?A =
    "\<lambda>out. composition_fri_sampled_full_cover_proximity_failure s bad out"
  let ?B = "\<lambda>out. composition_fri_sampled_full_cover_index_failure s out"
  let ?C = "\<lambda>out. composition_fri_sampled_full_cover_shape_failure s out"
  let ?D = "\<lambda>out. composition_fri_sampled_full_cover_domain_failure s out"
  let ?E = "\<lambda>out. composition_fri_sampled_full_cover_start_low_failure s out"
  have step1:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_failure_case s bad) s
      \<le> wp_event verify_monad
        (\<lambda>out. ?A out \<or> ?B out \<or> ?C out \<or> ?D out \<or> ?E out) s"
    by (rule wp_event_mono)
      (rule composition_fri_sampled_full_cover_failure_case_split_no_final)
  have four:
    "wp_event verify_monad
      (\<lambda>out. ?A out \<or> ?B out \<or> ?C out \<or> ?D out) s
      \<le> P + I + Sh + D"
    by (rule order_trans[OF wp_event_union_bound4
          add_mono[OF add_mono[OF add_mono[OF proximity index] shape]
            domain]])
  have five:
    "wp_event verify_monad
      (\<lambda>out. ?A out \<or> ?B out \<or> ?C out \<or> ?D out \<or> ?E out) s
      \<le> P + I + Sh + D + SL"
  proof -
    have "wp_event verify_monad
      (\<lambda>out. ?A out \<or> ?B out \<or> ?C out \<or> ?D out \<or> ?E out) s
      \<le> wp_event verify_monad
        (\<lambda>out. ?A out \<or> ?B out \<or> ?C out \<or> ?D out) s +
        wp_event verify_monad ?E s"
      by (rule order_trans[OF _ wp_event_union_bound])
        (rule wp_event_mono, blast)
    also have "... \<le> (P + I + Sh + D) + SL"
      by (rule add_mono[OF four start_low])
    finally show ?thesis
      by (simp add: add.assoc)
  qed
  show ?thesis
    by (rule order_trans[OF step1 five])
qed

lemma generic_fri_sampled_layer_chain_full_cover_or_failure:
  assumes
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
  shows
    "generic_fri_sampled_layer_chain_full_cover low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad \<or>
     generic_fri_sampled_full_cover_failure low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
  using assms
  unfolding generic_fri_sampled_layer_chain_full_cover_def
    generic_fri_sampled_full_cover_failure_def
  by blast

lemma generic_fri_sampled_layer_chain_missing_full_cover_failure:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
    and no_full:
    "\<not> generic_fri_sampled_layer_chain_full_cover low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers doms layers bad"
  shows
    "generic_fri_sampled_full_cover_failure low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers bad"
  using generic_fri_sampled_layer_chain_full_cover_or_failure[OF chain]
    no_full by blast

lemma trace_fri_sampled_missing_full_cover_imp_failure:
  assumes "trace_fri_sampled_missing_full_cover s bad out"
  shows "trace_fri_sampled_full_cover_failure s bad out"
proof -
  have sampled: "trace_fri_bad_with_sampled_layer_chain s out"
    and not_full: "\<not> trace_fri_bad_with_full_cover_layer_chain s bad out"
    using assms unfolding trace_fri_sampled_missing_full_cover_def by blast+
  from sampled obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table doms layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
    unfolding trace_fri_bad_with_sampled_layer_chain_def by blast
  have no_full:
    "\<not> generic_fri_sampled_layer_chain_full_cover trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers doms layers (bad trace_table)"
  proof
    assume full:
      "generic_fri_sampled_layer_chain_full_cover trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers (bad trace_table)"
    have "trace_fri_bad_with_full_cover_layer_chain s bad out"
      unfolding trace_fri_bad_with_full_cover_layer_chain_def
      using evidence full by blast
    then show False
      using not_full by contradiction
  qed
  have failure:
    "generic_fri_sampled_full_cover_failure trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers doms layers (bad trace_table)"
    by (rule generic_fri_sampled_layer_chain_missing_full_cover_failure
        [OF chain no_full])
  show ?thesis
    unfolding trace_fri_sampled_full_cover_failure_def
    using evidence chain failure by blast
qed

lemma composition_fri_sampled_missing_full_cover_imp_failure:
  assumes "composition_fri_sampled_missing_full_cover s bad out"
  shows "composition_fri_sampled_full_cover_failure s bad out"
proof -
  have sampled: "composition_fri_bad_with_sampled_layer_chain s out"
    and not_full:
      "\<not> composition_fri_bad_with_full_cover_layer_chain s bad out"
    using assms unfolding composition_fri_sampled_missing_full_cover_def
    by blast+
  from sampled obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table doms layers
    where evidence:
      "composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table"
    and chain:
      "generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers"
    unfolding composition_fri_bad_with_sampled_layer_chain_def by auto
  have no_full:
    "\<not> generic_fri_sampled_layer_chain_full_cover
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers doms layers
      (bad fri_dg composition_table)"
  proof
    assume full:
      "generic_fri_sampled_layer_chain_full_cover
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms
        layers (bad fri_dg composition_table)"
    have "composition_fri_bad_with_full_cover_layer_chain s bad out"
      unfolding composition_fri_bad_with_full_cover_layer_chain_def
      using evidence full by metis
    then show False
      using not_full by contradiction
  qed
  have failure:
    "generic_fri_sampled_full_cover_failure
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers doms layers
      (bad fri_dg composition_table)"
    by (rule generic_fri_sampled_layer_chain_missing_full_cover_failure
        [OF chain no_full])
  show ?thesis
    unfolding composition_fri_sampled_full_cover_failure_def
    using evidence chain failure by metis
qed

lemma wp_trace_fri_sampled_missing_full_cover_bound_from_failure:
  assumes failure_bound:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_failure s bad) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s \<le> M"
  by (rule order_trans[OF _ failure_bound])
    (rule wp_event_mono,
      rule trace_fri_sampled_missing_full_cover_imp_failure)

lemma wp_trace_fri_sampled_missing_full_cover_bound_from_failure_case:
  assumes failure_bound:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_failure_case s bad) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s \<le> M"
  by (rule wp_trace_fri_sampled_missing_full_cover_bound_from_failure)
    (rule order_trans[OF _ failure_bound],
      rule wp_event_mono,
      simp add: trace_fri_sampled_full_cover_failure_iff_case)

lemma wp_trace_fri_sampled_missing_full_cover_bound_from_failure_subcases:
  assumes proximity:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
    and domain:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and start_low:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_start_low_failure s) s \<le> SL"
    and final_low:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_final_low_failure s) s \<le> FL"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + Sh + D + SL + FL"
  by (rule wp_trace_fri_sampled_missing_full_cover_bound_from_failure_case)
    (rule wp_trace_fri_sampled_full_cover_failure_case_union_bound
      [OF proximity index shape domain start_low final_low])

lemma wp_trace_fri_sampled_missing_full_cover_bound_from_five_subcases:
  assumes proximity:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
    and domain:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and final_low:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_final_low_failure s) s \<le> FL"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + Sh + D + FL"
proof -
  have six:
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + Sh + D + 0 + FL"
    by (rule wp_trace_fri_sampled_missing_full_cover_bound_from_failure_subcases
        [OF proximity index shape domain
          wp_trace_fri_sampled_full_cover_start_low_failure_zero final_low])
  then show ?thesis
    by simp
qed

lemma wp_trace_fri_sampled_missing_full_cover_bound_from_length_subcases:
  assumes proximity:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
    and domain:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and final_length:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_final_length_failure s) s \<le> FL"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + Sh + D + FL"
  by (rule wp_trace_fri_sampled_missing_full_cover_bound_from_five_subcases
      [OF proximity index shape domain])
    (rule wp_trace_fri_sampled_full_cover_final_low_bound_from_length
      [OF final_length])

lemma wp_trace_fri_sampled_missing_full_cover_bound_from_shape_subcases:
  assumes proximity:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
    and domain:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_failure s) s \<le> D"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + Sh + D"
proof -
  have case_bound:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_failure_case s bad) s
      \<le> P + I + Sh + D + 0"
    by (rule wp_trace_fri_sampled_full_cover_failure_case_union_bound_no_final
        [OF proximity index shape domain
          wp_trace_fri_sampled_full_cover_start_low_failure_zero])
  have "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + Sh + D + 0"
    by (rule wp_trace_fri_sampled_missing_full_cover_bound_from_failure_case
        [OF case_bound])
  then show ?thesis
    by simp
qed

lemma wp_trace_fri_sampled_missing_full_cover_bound_from_split_shape_subcases:
  assumes proximity:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and arithmetic_shape:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_arithmetic_shape_failure s) s \<le> A"
    and witness_length:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_witness_length_failure s) s \<le> W"
    and domain:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_failure s) s \<le> D"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + (A + W) + D"
  by (rule wp_trace_fri_sampled_missing_full_cover_bound_from_shape_subcases
      [OF proximity index _ domain])
    (rule wp_trace_fri_sampled_full_cover_shape_bound_from_split
      [OF arithmetic_shape witness_length])

lemma wp_trace_fri_sampled_missing_full_cover_bound_from_witness_length_subcases:
  assumes proximity:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and witness_length:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_witness_length_failure s) s \<le> W"
    and domain:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_failure s) s \<le> D"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + W + D"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + (0 + W) + D"
    by (rule
        wp_trace_fri_sampled_missing_full_cover_bound_from_split_shape_subcases
        [OF proximity index
          wp_trace_fri_sampled_full_cover_arithmetic_shape_failure_zero
          witness_length domain])
  then show ?thesis
    by simp
qed

lemma wp_composition_fri_sampled_missing_full_cover_bound_from_failure:
  assumes failure_bound:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_failure s bad) s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s \<le> M"
  by (rule order_trans[OF _ failure_bound])
    (rule wp_event_mono,
      rule composition_fri_sampled_missing_full_cover_imp_failure)

lemma wp_composition_fri_sampled_missing_full_cover_bound_from_failure_case:
  assumes failure_bound:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_failure_case s bad) s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s \<le> M"
  by (rule wp_composition_fri_sampled_missing_full_cover_bound_from_failure)
    (rule order_trans[OF _ failure_bound],
      rule wp_event_mono,
      simp add: composition_fri_sampled_full_cover_failure_iff_case)

lemma wp_composition_fri_sampled_missing_full_cover_bound_from_failure_subcases:
  assumes proximity:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
    and domain:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and start_low:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_start_low_failure s) s \<le> SL"
    and final_low:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_final_low_failure s) s \<le> FL"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + Sh + D + SL + FL"
  by (rule wp_composition_fri_sampled_missing_full_cover_bound_from_failure_case)
    (rule wp_composition_fri_sampled_full_cover_failure_case_union_bound
      [OF proximity index shape domain start_low final_low])

lemma wp_composition_fri_sampled_missing_full_cover_bound_from_five_subcases:
  assumes proximity:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
    and domain:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and final_low:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_final_low_failure s) s \<le> FL"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + Sh + D + FL"
proof -
  have six:
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + Sh + D + 0 + FL"
    by (rule
        wp_composition_fri_sampled_missing_full_cover_bound_from_failure_subcases
        [OF proximity index shape domain
          wp_composition_fri_sampled_full_cover_start_low_failure_zero
          final_low])
  then show ?thesis
    by simp
qed

lemma wp_composition_fri_sampled_missing_full_cover_bound_from_length_subcases:
  assumes proximity:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
    and domain:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
    and final_length:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_final_length_failure s) s \<le> FL"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + Sh + D + FL"
  by (rule
      wp_composition_fri_sampled_missing_full_cover_bound_from_five_subcases
      [OF proximity index shape domain])
    (rule wp_composition_fri_sampled_full_cover_final_low_bound_from_length
      [OF final_length])

lemma wp_composition_fri_sampled_missing_full_cover_bound_from_shape_subcases:
  assumes proximity:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
    and domain:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + Sh + D"
proof -
  have case_bound:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_failure_case s bad) s
      \<le> P + I + Sh + D + 0"
    by (rule
        wp_composition_fri_sampled_full_cover_failure_case_union_bound_no_final
        [OF proximity index shape domain
          wp_composition_fri_sampled_full_cover_start_low_failure_zero])
  have "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + Sh + D + 0"
    by (rule
        wp_composition_fri_sampled_missing_full_cover_bound_from_failure_case
        [OF case_bound])
  then show ?thesis
    by simp
qed

lemma
  wp_composition_fri_sampled_missing_full_cover_bound_from_split_shape_subcases:
  assumes proximity:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and arithmetic_shape:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_arithmetic_shape_failure s) s
      \<le> A"
    and witness_length:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_witness_length_failure s) s \<le> W"
    and domain:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + (A + W) + D"
  by (rule
      wp_composition_fri_sampled_missing_full_cover_bound_from_shape_subcases
      [OF proximity index _ domain])
    (rule wp_composition_fri_sampled_full_cover_shape_bound_from_split
      [OF arithmetic_shape witness_length])

lemma
  wp_composition_fri_sampled_missing_full_cover_bound_from_witness_length_subcases:
  assumes proximity:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and witness_length:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_witness_length_failure s) s \<le> W"
    and domain:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + W + D"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + (0 + W) + D"
    by (rule
        wp_composition_fri_sampled_missing_full_cover_bound_from_split_shape_subcases
        [OF proximity index
          wp_composition_fri_sampled_full_cover_arithmetic_shape_failure_zero
          witness_length domain])
  then show ?thesis
    by simp
qed

end

end
