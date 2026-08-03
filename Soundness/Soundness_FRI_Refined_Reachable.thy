(*  Title:      Stark/Soundness_FRI_Refined_Reachable.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Refined_Reachable
  imports Soundness_FRI_Internal_Bounds
begin

text \<open>
  Refined reachable FRI layer-chain targets.

  Broad reachable partial-candidate events quantify full base tables compatible
  with sampled initial openings.  Sampled base openings alone do not determine
  the committed FRI layer chain, so this theory introduces the narrower
  algebraic cover used by the next proof layer.

  Its witnesses include the accepted FRI opening transcript and a canonical FRI
  layer chain.  The cover is internal proof infrastructure; it does not change
  the protocol, verifier, Merkle interface, or public theorem assumptions.
\<close>

context soundness
begin

definition trace_fri_bad_with_refined_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_refined_layer_chain s bad out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_canonical_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers (bad trace_table))"

definition composition_fri_bad_with_refined_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_bad_with_refined_layer_chain s bad out \<longleftrightarrow>
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
      generic_fri_canonical_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        (bad fri_dg composition_table))"

definition trace_fri_reachable_missing_refined_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_reachable_missing_refined_layer_chain s bad out \<longleftrightarrow>
    trace_fri_bad_with_reachable_partial_candidate s out \<and>
    \<not> trace_fri_bad_with_refined_layer_chain s bad out"

definition composition_fri_reachable_missing_refined_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_reachable_missing_refined_layer_chain s bad out
    \<longleftrightarrow>
    composition_fri_bad_with_reachable_partial_candidate s out \<and>
    \<not> composition_fri_bad_with_refined_layer_chain s bad out"

definition trace_fri_bad_with_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_sampled_layer_chain s out \<longleftrightarrow>
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
        fri_query_idxs trace_round_layers doms layers)"

definition composition_fri_bad_with_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_bad_with_sampled_layer_chain s out \<longleftrightarrow>
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
        composition_final fri_query_idxs composition_round_layers doms layers)"

definition trace_fri_reachable_missing_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_reachable_missing_sampled_layer_chain s out \<longleftrightarrow>
    trace_fri_bad_with_reachable_partial_candidate s out \<and>
    \<not> trace_fri_bad_with_sampled_layer_chain s out"

definition composition_fri_reachable_missing_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_reachable_missing_sampled_layer_chain s out \<longleftrightarrow>
    composition_fri_bad_with_reachable_partial_candidate s out \<and>
    \<not> composition_fri_bad_with_sampled_layer_chain s out"

definition trace_fri_sampled_layer_chain_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> bool"
where
  "trace_fri_sampled_layer_chain_cover s bad \<longleftrightarrow>
    (\<forall>out trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<longrightarrow>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<longrightarrow>
      trace_bs \<in> trace_fri_multiround_bad_sets bad trace_table)"

definition composition_fri_sampled_layer_chain_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> bool"
where
  "composition_fri_sampled_layer_chain_cover s bad \<longleftrightarrow>
    (\<forall>out trace_roots trace_bs trace_final fri_dg
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
        composition_table \<longrightarrow>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        \<longrightarrow>
      composition_bs \<in>
        composition_fri_multiround_bad_sets bad fri_dg composition_table)"

definition trace_fri_bad_with_full_cover_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_full_cover_layer_chain s bad out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_chain_full_cover trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers (bad trace_table))"

definition composition_fri_bad_with_full_cover_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_bad_with_full_cover_layer_chain s bad out \<longleftrightarrow>
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
      generic_fri_sampled_layer_chain_full_cover
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        (bad fri_dg composition_table))"

definition trace_fri_sampled_missing_full_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_missing_full_cover s bad out \<longleftrightarrow>
    trace_fri_bad_with_sampled_layer_chain s out \<and>
    \<not> trace_fri_bad_with_full_cover_layer_chain s bad out"

definition composition_fri_sampled_missing_full_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_missing_full_cover s bad out \<longleftrightarrow>
    composition_fri_bad_with_sampled_layer_chain s out \<and>
    \<not> composition_fri_bad_with_full_cover_layer_chain s bad out"

lemma trace_fri_sampled_layer_chain_cover_from_full_cover:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  fixes bad :: "'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes full_cover:
    "\<And>out trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<Longrightarrow>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers \<Longrightarrow>
      generic_fri_sampled_layer_chain_full_cover trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers (bad trace_table)"
  shows "trace_fri_sampled_layer_chain_cover s bad"
proof (unfold trace_fri_sampled_layer_chain_cover_def, intro allI impI)
  fix out trace_roots trace_bs trace_final dg composition_roots
    composition_bs composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr candidate_query_idxs trace_openings
    trace_table doms layers
  assume evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
  assume chain:
    "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers doms layers"
  have full:
    "generic_fri_sampled_layer_chain_full_cover trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers doms layers (bad trace_table)"
    by (rule full_cover[OF evidence chain])
  have not_low: "\<not> trace_table_low_degree trace_table"
    using trace_fri_partial_candidate_opening_evidenceD(2)[OF evidence]
      trace_fri_partial_candidate_evidenceD(3)
    by blast
  have bad_candidate:
    "generic_fri_bad_candidate trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers (bad trace_table)"
    by (rule generic_fri_bad_candidate_from_sampled_layer_chain_full_cover
        [OF full not_low])
  have bad_generic:
    "trace_bs \<in> generic_fri_bad_challenge_lists (length trace_bs)
      (bad trace_table)"
    by (rule generic_fri_bad_candidateD(3)[OF bad_candidate])
  have partial:
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
    by (rule generic_fri_bad_candidateD(1)[OF bad_candidate])
  have len_trace:
    "length trace_bs = trace_fri_algebraic_round_count"
    using generic_fri_partial_evidence_shapes(1,2)[OF partial]
    by (simp add: trace_fri_algebraic_round_count_def)
  show "trace_bs \<in> trace_fri_multiround_bad_sets bad trace_table"
    using bad_generic len_trace
    by (simp add: trace_fri_multiround_bad_sets_as_generic)
qed

lemma composition_fri_sampled_layer_chain_cover_from_full_cover:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  fixes bad :: "'f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  assumes full_cover:
    "\<And>out trace_roots trace_bs trace_final fri_dg
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
        composition_table \<Longrightarrow>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms
        layers \<Longrightarrow>
      generic_fri_sampled_layer_chain_full_cover
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms
        layers (bad fri_dg composition_table)"
  shows "composition_fri_sampled_layer_chain_cover s bad"
proof (unfold composition_fri_sampled_layer_chain_cover_def,
    intro allI impI)
  fix out trace_roots trace_bs trace_final fri_dg
    opening_composition_roots composition_bs composition_final
    fri_query_idxs trace_round_layers composition_round_layers fr
    f_fri_roots f_final as dg composition_fri_roots final
    trace_query_idxs trace_openings composition_query_idxs
    composition_openings trace_table composition_table doms layers
  assume evidence:
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
  assume chain:
    "generic_fri_sampled_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers doms
      layers"
  have full:
    "generic_fri_sampled_layer_chain_full_cover
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers doms
      layers (bad fri_dg composition_table)"
    by (rule full_cover[OF evidence chain])
  have not_low_on:
    "\<not> fri_table_low_degree_on (to_nat fri_dg) eval_domain
      composition_table"
    using full unfolding generic_fri_sampled_layer_chain_full_cover_def
    by blast
  have not_low:
    "\<not> composition_table_low_degree (to_nat fri_dg) composition_table"
    using not_low_on
      composition_table_not_low_degree_iff_not_fri_table_low_degree_on_eval_domain
    by simp
  have bad_candidate:
    "generic_fri_bad_candidate
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers
      (bad fri_dg composition_table)"
    by (rule generic_fri_bad_candidate_from_sampled_layer_chain_full_cover
        [OF full not_low])
  have bad_generic:
    "composition_bs \<in> generic_fri_bad_challenge_lists
      (length composition_bs) (bad fri_dg composition_table)"
    by (rule generic_fri_bad_candidateD(3)[OF bad_candidate])
  have partial:
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers"
    by (rule generic_fri_bad_candidateD(1)[OF bad_candidate])
  have len_composition:
    "length composition_bs = composition_fri_algebraic_round_count fri_dg"
    using generic_fri_partial_evidence_shapes(1,2)[OF partial]
    by (simp add: composition_fri_algebraic_round_count_def)
  show "composition_bs \<in>
      composition_fri_multiround_bad_sets bad fri_dg composition_table"
    using bad_generic len_composition
    by (simp add: composition_fri_multiround_bad_sets_as_generic)
qed

lemma trace_fri_bad_with_full_cover_layer_chain_imp_list_hit:
  assumes full:
    "trace_fri_bad_with_full_cover_layer_chain s bad out"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
  shows "trace_fri_challenge_list_set_hit s B out"
proof -
  from full obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table doms layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and full_cover:
      "generic_fri_sampled_layer_chain_full_cover trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers (bad trace_table)"
    unfolding trace_fri_bad_with_full_cover_layer_chain_def by blast
  have bad_generic:
    "trace_bs \<in> generic_fri_bad_challenge_lists (length trace_bs)
      (bad trace_table)"
  proof -
    have not_low: "\<not> trace_table_low_degree trace_table"
      using trace_fri_partial_candidate_opening_evidenceD(2)[OF evidence]
        trace_fri_partial_candidate_evidenceD(3)
      by blast
    have bad_candidate:
      "generic_fri_bad_candidate trace_table_low_degree trace_table
        (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers (bad trace_table)"
      by (rule generic_fri_bad_candidate_from_sampled_layer_chain_full_cover
          [OF full_cover not_low])
    show ?thesis
      by (rule generic_fri_bad_candidateD(3)[OF bad_candidate])
  qed
  have partial:
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
  proof -
    have not_low: "\<not> trace_table_low_degree trace_table"
      using trace_fri_partial_candidate_opening_evidenceD(2)[OF evidence]
        trace_fri_partial_candidate_evidenceD(3)
      by blast
    have bad_candidate:
      "generic_fri_bad_candidate trace_table_low_degree trace_table
        (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers (bad trace_table)"
      by (rule generic_fri_bad_candidate_from_sampled_layer_chain_full_cover
          [OF full_cover not_low])
    show ?thesis
      by (rule generic_fri_bad_candidateD(1)[OF bad_candidate])
  qed
  have len_trace:
    "length trace_bs = trace_fri_algebraic_round_count"
    using generic_fri_partial_evidence_shapes(1,2)[OF partial]
    by (simp add: trace_fri_algebraic_round_count_def)
  have bad_hit: "trace_bs \<in> trace_fri_multiround_bad_sets bad trace_table"
    using bad_generic len_trace
    by (simp add: trace_fri_multiround_bad_sets_as_generic)
  have challenges:
    "accepted_fri_challenges s out trace_bs dg composition_bs"
    using trace_fri_partial_candidate_opening_evidenceD(1)[OF evidence]
      accepted_fri_opening_transcript_challenges by blast
  have "trace_bs \<in> B"
    using bad_hit envelope[of trace_table] by blast
  then show ?thesis
    unfolding trace_fri_challenge_list_set_hit_def
    using challenges by blast
qed

lemma composition_fri_bad_with_full_cover_layer_chain_imp_list_hit:
  assumes full:
    "composition_fri_bad_with_full_cover_layer_chain s bad out"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
  shows "composition_fri_challenge_list_set_hit s B out"
proof -
  from full obtain trace_roots trace_bs trace_final fri_dg
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
    and full_cover:
      "generic_fri_sampled_layer_chain_full_cover
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        (bad fri_dg composition_table)"
    unfolding composition_fri_bad_with_full_cover_layer_chain_def
    by auto
  have bad_generic:
    "composition_bs \<in> generic_fri_bad_challenge_lists
      (length composition_bs) (bad fri_dg composition_table)"
  proof -
    have not_low_on:
      "\<not> fri_table_low_degree_on (to_nat fri_dg) eval_domain
        composition_table"
      using full_cover
      unfolding generic_fri_sampled_layer_chain_full_cover_def by blast
    have not_low:
      "\<not> composition_table_low_degree (to_nat fri_dg) composition_table"
      using not_low_on
        composition_table_not_low_degree_iff_not_fri_table_low_degree_on_eval_domain
      by simp
    have bad_candidate:
      "generic_fri_bad_candidate
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        (bad fri_dg composition_table)"
      by (rule generic_fri_bad_candidate_from_sampled_layer_chain_full_cover
          [OF full_cover not_low])
    show ?thesis
      by (rule generic_fri_bad_candidateD(3)[OF bad_candidate])
  qed
  have partial:
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers"
  proof -
    have not_low_on:
      "\<not> fri_table_low_degree_on (to_nat fri_dg) eval_domain
        composition_table"
      using full_cover
      unfolding generic_fri_sampled_layer_chain_full_cover_def by blast
    have not_low:
      "\<not> composition_table_low_degree (to_nat fri_dg) composition_table"
      using not_low_on
        composition_table_not_low_degree_iff_not_fri_table_low_degree_on_eval_domain
      by simp
    have bad_candidate:
      "generic_fri_bad_candidate
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        (bad fri_dg composition_table)"
      by (rule generic_fri_bad_candidate_from_sampled_layer_chain_full_cover
          [OF full_cover not_low])
    show ?thesis
      by (rule generic_fri_bad_candidateD(1)[OF bad_candidate])
  qed
  have len_composition:
    "length composition_bs = composition_fri_algebraic_round_count fri_dg"
    using generic_fri_partial_evidence_shapes(1,2)[OF partial]
    by (simp add: composition_fri_algebraic_round_count_def)
  have bad_hit:
    "composition_bs \<in>
      composition_fri_multiround_bad_sets bad fri_dg composition_table"
    using bad_generic len_composition
    by (simp add: composition_fri_multiround_bad_sets_as_generic)
  have challenges:
    "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
    using composition_fri_partial_candidate_opening_evidenceD(1)[OF evidence]
      accepted_fri_opening_transcript_challenges by blast
  have "composition_bs \<in> B fri_dg"
    using bad_hit envelope[of fri_dg composition_table] by blast
  then show ?thesis
    unfolding composition_fri_challenge_list_set_hit_def
    using challenges by blast
qed

lemma trace_fri_sampled_imp_full_cover_or_missing:
  assumes "trace_fri_bad_with_sampled_layer_chain s out"
  shows
    "trace_fri_bad_with_full_cover_layer_chain s bad out \<or>
     trace_fri_sampled_missing_full_cover s bad out"
  using assms unfolding trace_fri_sampled_missing_full_cover_def by blast

lemma composition_fri_sampled_imp_full_cover_or_missing:
  assumes "composition_fri_bad_with_sampled_layer_chain s out"
  shows
    "composition_fri_bad_with_full_cover_layer_chain s bad out \<or>
     composition_fri_sampled_missing_full_cover s bad out"
  using assms unfolding composition_fri_sampled_missing_full_cover_def
  by blast

lemma wp_trace_fri_bad_with_full_cover_layer_chain_bound_from_envelope:
  assumes future: "trace_fri_future_fresh s"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_full_cover_layer_chain s bad) s \<le> C"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_full_cover_layer_chain s bad) s \<le>
    wp_event verify_monad (trace_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule trace_fri_bad_with_full_cover_layer_chain_imp_list_hit
        [OF _ envelope])
  also have "... \<le> nnreal (card B) /
      nnreal (CARD('f) ^ ceil_log clength)"
    by (rule wp_verify_monad_trace_fri_challenge_list_set_bound
        [OF future subset])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_bad_with_full_cover_layer_chain_bound_from_envelope:
  assumes future: "composition_fri_future_fresh s"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_full_cover_layer_chain s bad) s \<le> C"
proof -
  have "wp_event verify_monad
      (composition_fri_bad_with_full_cover_layer_chain s bad) s \<le>
    wp_event verify_monad (composition_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule composition_fri_bad_with_full_cover_layer_chain_imp_list_hit
        [OF _ envelope])
  also have "... \<le> C"
    by (rule wp_verify_monad_composition_fri_challenge_list_set_bound
        [OF future subset bound])
  finally show ?thesis .
qed

lemma wp_trace_fri_sampled_bound_from_full_cover_and_missing:
  assumes full_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_full_cover_layer_chain s bad) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> R + M"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le>
    wp_event verify_monad
      (\<lambda>out. trace_fri_bad_with_full_cover_layer_chain s bad out \<or>
        trace_fri_sampled_missing_full_cover s bad out) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_imp_full_cover_or_missing)
  also have "... \<le>
    wp_event verify_monad
      (trace_fri_bad_with_full_cover_layer_chain s bad) s +
    wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (intro add_mono full_bound missing_bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_sampled_bound_from_full_cover_and_missing:
  assumes full_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_full_cover_layer_chain s bad) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le> R + M"
proof -
  have "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le>
    wp_event verify_monad
      (\<lambda>out. composition_fri_bad_with_full_cover_layer_chain s bad out \<or>
        composition_fri_sampled_missing_full_cover s bad out) s"
    by (rule wp_event_mono)
      (rule composition_fri_sampled_imp_full_cover_or_missing)
  also have "... \<le>
    wp_event verify_monad
      (composition_fri_bad_with_full_cover_layer_chain s bad) s +
    wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (intro add_mono full_bound missing_bound)
  finally show ?thesis .
qed

definition trace_fri_canonical_layer_chain_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> bool"
where
  "trace_fri_canonical_layer_chain_cover s bad \<longleftrightarrow>
    (\<forall>out trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table doms layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<longrightarrow>
      generic_fri_canonical_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers (bad trace_table)
        \<longrightarrow>
      trace_bs \<in> trace_fri_multiround_bad_sets bad trace_table)"

definition composition_fri_canonical_layer_chain_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow> bool"
where
  "composition_fri_canonical_layer_chain_cover s bad \<longleftrightarrow>
    (\<forall>out trace_roots trace_bs trace_final fri_dg
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
        composition_table \<longrightarrow>
      generic_fri_canonical_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        (bad fri_dg composition_table) \<longrightarrow>
      composition_bs \<in>
        composition_fri_multiround_bad_sets bad fri_dg composition_table)"

lemma trace_fri_canonical_layer_chain_cover_generic:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  fixes bad :: "'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  shows "trace_fri_canonical_layer_chain_cover s bad"
proof (unfold trace_fri_canonical_layer_chain_cover_def, intro allI impI)
  fix out trace_roots trace_bs trace_final dg composition_roots
    composition_bs composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr candidate_query_idxs trace_openings
    trace_table doms layers
  assume evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
  assume chain:
    "generic_fri_canonical_layer_chain_evidence trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers doms layers (bad trace_table)"
  have bad_generic:
    "trace_bs \<in> generic_fri_bad_challenge_lists (length trace_bs)
      (bad trace_table)"
    by (rule generic_fri_canonical_layer_chain_bad_challenge_list[OF chain])
  have partial:
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
    by (rule generic_fri_canonical_layer_chain_evidenceD(1)[OF chain])
  have len_trace:
    "length trace_bs = trace_fri_algebraic_round_count"
    using generic_fri_partial_evidence_shapes(1,2)[OF partial]
    by (simp add: trace_fri_algebraic_round_count_def)
  show "trace_bs \<in> trace_fri_multiround_bad_sets bad trace_table"
    using bad_generic len_trace
    by (simp add: trace_fri_multiround_bad_sets_as_generic)
qed

lemma composition_fri_canonical_layer_chain_cover_generic:
  fixes s :: "('f, 'a) protocol_channel_scheme"
  fixes bad :: "'f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set"
  shows "composition_fri_canonical_layer_chain_cover s bad"
proof (unfold composition_fri_canonical_layer_chain_cover_def,
    intro allI impI)
  fix out trace_roots trace_bs trace_final fri_dg
    opening_composition_roots composition_bs composition_final
    fri_query_idxs trace_round_layers composition_round_layers fr
    f_fri_roots f_final as dg composition_fri_roots final
    trace_query_idxs trace_openings composition_query_idxs
    composition_openings trace_table composition_table doms layers
  assume evidence:
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
  assume chain:
    "generic_fri_canonical_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers doms layers
      (bad fri_dg composition_table)"
  have bad_generic:
    "composition_bs \<in> generic_fri_bad_challenge_lists
      (length composition_bs) (bad fri_dg composition_table)"
    by (rule generic_fri_canonical_layer_chain_bad_challenge_list[OF chain])
  have partial:
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers"
    by (rule generic_fri_canonical_layer_chain_evidenceD(1)[OF chain])
  have len_composition:
    "length composition_bs = composition_fri_algebraic_round_count fri_dg"
    using generic_fri_partial_evidence_shapes(1,2)[OF partial]
    by (simp add: composition_fri_algebraic_round_count_def)
  show "composition_bs \<in>
      composition_fri_multiround_bad_sets bad fri_dg composition_table"
    using bad_generic len_composition
    by (simp add: composition_fri_multiround_bad_sets_as_generic)
qed

lemma trace_fri_bad_with_refined_layer_chain_imp_list_hit:
  assumes refined:
    "trace_fri_bad_with_refined_layer_chain s bad out"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
  shows "trace_fri_challenge_list_set_hit s B out"
proof -
  from refined obtain trace_roots trace_bs trace_final dg composition_roots
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
      "generic_fri_canonical_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers (bad trace_table)"
    unfolding trace_fri_bad_with_refined_layer_chain_def by blast
  have cover: "trace_fri_canonical_layer_chain_cover s bad"
    by (rule trace_fri_canonical_layer_chain_cover_generic)
  have bad_hit: "trace_bs \<in> trace_fri_multiround_bad_sets bad trace_table"
    using cover evidence chain
    unfolding trace_fri_canonical_layer_chain_cover_def by blast
  have challenges:
    "accepted_fri_challenges s out trace_bs dg composition_bs"
    using trace_fri_partial_candidate_opening_evidenceD(1)[OF evidence]
      accepted_fri_opening_transcript_challenges by blast
  have "trace_bs \<in> B"
    using bad_hit envelope[of trace_table] by blast
  then show ?thesis
    unfolding trace_fri_challenge_list_set_hit_def
    using challenges by blast
qed

lemma composition_fri_bad_with_refined_layer_chain_imp_list_hit:
  assumes refined:
    "composition_fri_bad_with_refined_layer_chain s bad out"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
  shows "composition_fri_challenge_list_set_hit s B out"
proof -
  from refined obtain trace_roots trace_bs trace_final fri_dg
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
      "generic_fri_canonical_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        (bad fri_dg composition_table)"
    unfolding composition_fri_bad_with_refined_layer_chain_def
    by auto
  have bad_hit:
    "composition_bs \<in>
      composition_fri_multiround_bad_sets bad fri_dg composition_table"
  proof -
    have bad_generic:
      "composition_bs \<in> generic_fri_bad_challenge_lists
        (length composition_bs) (bad fri_dg composition_table)"
      by (rule generic_fri_canonical_layer_chain_bad_challenge_list
          [OF chain])
    have partial:
      "generic_fri_partial_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers"
      by (rule generic_fri_canonical_layer_chain_evidenceD(1)[OF chain])
    have len_composition:
      "length composition_bs = composition_fri_algebraic_round_count fri_dg"
      using generic_fri_partial_evidence_shapes(1,2)[OF partial]
      by (simp add: composition_fri_algebraic_round_count_def)
    show ?thesis
      using bad_generic len_composition
      by (simp add: composition_fri_multiround_bad_sets_as_generic)
  qed
  have challenges:
    "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
    using composition_fri_partial_candidate_opening_evidenceD(1)[OF evidence]
      accepted_fri_opening_transcript_challenges by blast
  have "composition_bs \<in> B fri_dg"
    using bad_hit envelope[of fri_dg composition_table] by blast
  then show ?thesis
    unfolding composition_fri_challenge_list_set_hit_def
    using challenges by blast
qed

lemma wp_trace_fri_bad_with_refined_layer_chain_bound_from_envelope:
  assumes future: "trace_fri_future_fresh s"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_refined_layer_chain s bad) s \<le> C"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_refined_layer_chain s bad) s \<le>
    wp_event verify_monad (trace_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule trace_fri_bad_with_refined_layer_chain_imp_list_hit
        [OF _ envelope])
  also have "... \<le> nnreal (card B) /
      nnreal (CARD('f) ^ ceil_log clength)"
    by (rule wp_verify_monad_trace_fri_challenge_list_set_bound
        [OF future subset])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_bad_with_refined_layer_chain_bound_from_envelope:
  assumes future: "composition_fri_future_fresh s"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_refined_layer_chain s bad) s \<le> C"
proof -
  have "wp_event verify_monad
      (composition_fri_bad_with_refined_layer_chain s bad) s \<le>
    wp_event verify_monad (composition_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule composition_fri_bad_with_refined_layer_chain_imp_list_hit
        [OF _ envelope])
  also have "... \<le> C"
    by (rule wp_verify_monad_composition_fri_challenge_list_set_bound
        [OF future subset bound])
  finally show ?thesis .
qed

lemma trace_fri_bad_with_sampled_layer_chain_imp_list_hit:
  assumes sampled:
    "trace_fri_bad_with_sampled_layer_chain s out"
    and cover: "trace_fri_sampled_layer_chain_cover s bad"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
  shows "trace_fri_challenge_list_set_hit s B out"
proof -
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
  have bad_hit: "trace_bs \<in> trace_fri_multiround_bad_sets bad trace_table"
    using cover evidence chain
    unfolding trace_fri_sampled_layer_chain_cover_def by blast
  have challenges:
    "accepted_fri_challenges s out trace_bs dg composition_bs"
    using trace_fri_partial_candidate_opening_evidenceD(1)[OF evidence]
      accepted_fri_opening_transcript_challenges by blast
  have "trace_bs \<in> B"
    using bad_hit envelope[of trace_table] by blast
  then show ?thesis
    unfolding trace_fri_challenge_list_set_hit_def
    using challenges by blast
qed

lemma composition_fri_bad_with_sampled_layer_chain_imp_list_hit:
  assumes sampled:
    "composition_fri_bad_with_sampled_layer_chain s out"
    and cover: "composition_fri_sampled_layer_chain_cover s bad"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
  shows "composition_fri_challenge_list_set_hit s B out"
proof -
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
  have bad_hit:
    "composition_bs \<in>
      composition_fri_multiround_bad_sets bad fri_dg composition_table"
    using cover evidence chain
    unfolding composition_fri_sampled_layer_chain_cover_def by metis
  have challenges:
    "accepted_fri_challenges s out trace_bs fri_dg composition_bs"
    using composition_fri_partial_candidate_opening_evidenceD(1)[OF evidence]
      accepted_fri_opening_transcript_challenges by blast
  have "composition_bs \<in> B fri_dg"
    using bad_hit envelope[of fri_dg composition_table] by blast
  then show ?thesis
    unfolding composition_fri_challenge_list_set_hit_def
    using challenges by blast
qed

lemma wp_trace_fri_bad_with_sampled_layer_chain_bound_from_envelope:
  assumes future: "trace_fri_future_fresh s"
    and cover: "trace_fri_sampled_layer_chain_cover s bad"
    and envelope:
      "\<And>trace_table. trace_fri_multiround_bad_sets bad trace_table \<subseteq> B"
    and subset: "B \<subseteq> fri_challenge_space (ceil_log clength)"
    and bound:
      "nnreal (card B) / nnreal (CARD('f) ^ ceil_log clength) \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> C"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le>
    wp_event verify_monad (trace_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule trace_fri_bad_with_sampled_layer_chain_imp_list_hit
        [OF _ cover envelope])
  also have "... \<le> nnreal (card B) /
      nnreal (CARD('f) ^ ceil_log clength)"
    by (rule wp_verify_monad_trace_fri_challenge_list_set_bound
        [OF future subset])
  also have "... \<le> C"
    by (rule bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_bad_with_sampled_layer_chain_bound_from_envelope:
  assumes future: "composition_fri_future_fresh s"
    and cover: "composition_fri_sampled_layer_chain_cover s bad"
    and envelope:
      "\<And>dg composition_table.
        composition_fri_multiround_bad_sets bad dg composition_table
          \<subseteq> B dg"
    and subset:
      "\<And>dg. B dg \<subseteq> fri_challenge_space (ceil_log (to_nat dg + 1))"
    and bound:
      "\<And>dg. nnreal (card (B dg)) /
        nnreal (CARD('f) ^ ceil_log (to_nat dg + 1)) \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le> C"
proof -
  have "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le>
    wp_event verify_monad (composition_fri_challenge_list_set_hit s B) s"
    by (rule wp_event_mono)
      (rule composition_fri_bad_with_sampled_layer_chain_imp_list_hit
        [OF _ cover envelope])
  also have "... \<le> C"
    by (rule wp_verify_monad_composition_fri_challenge_list_set_bound
        [OF future subset bound])
  finally show ?thesis .
qed

lemma trace_fri_reachable_imp_refined_or_missing_layer_chain:
  assumes "trace_fri_bad_with_reachable_partial_candidate s out"
  shows
    "trace_fri_bad_with_refined_layer_chain s bad out \<or>
     trace_fri_reachable_missing_refined_layer_chain s bad out"
  using assms
  unfolding trace_fri_reachable_missing_refined_layer_chain_def by blast

lemma composition_fri_reachable_imp_refined_or_missing_layer_chain:
  assumes "composition_fri_bad_with_reachable_partial_candidate s out"
  shows
    "composition_fri_bad_with_refined_layer_chain s bad out \<or>
     composition_fri_reachable_missing_refined_layer_chain s bad out"
  using assms
  unfolding composition_fri_reachable_missing_refined_layer_chain_def by blast

lemma trace_fri_reachable_imp_sampled_or_missing_layer_chain:
  assumes "trace_fri_bad_with_reachable_partial_candidate s out"
  shows
    "trace_fri_bad_with_sampled_layer_chain s out \<or>
     trace_fri_reachable_missing_sampled_layer_chain s out"
  using assms
  unfolding trace_fri_reachable_missing_sampled_layer_chain_def by blast

lemma composition_fri_reachable_imp_sampled_or_missing_layer_chain:
  assumes "composition_fri_bad_with_reachable_partial_candidate s out"
  shows
    "composition_fri_bad_with_sampled_layer_chain s out \<or>
     composition_fri_reachable_missing_sampled_layer_chain s out"
  using assms
  unfolding composition_fri_reachable_missing_sampled_layer_chain_def
  by blast

lemma verify_monad_trace_fri_missing_extracts_opening_evidence:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and missing:
      "trace_fri_reachable_missing_refined_layer_chain s bad
        (Some (result, final_state))"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
  where
    "trace_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr candidate_query_idxs
      trace_openings trace_table"
    "\<And>doms layers. \<not>
      generic_fri_canonical_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers (bad trace_table)"
proof -
  have reachable:
    "trace_fri_bad_with_reachable_partial_candidate s
      (Some (result, final_state))"
    and not_refined:
      "\<not> trace_fri_bad_with_refined_layer_chain s bad
        (Some (result, final_state))"
    using missing
    unfolding trace_fri_reachable_missing_refined_layer_chain_def
    by blast+
  from verify_monad_trace_fri_bad_extracts_opening_evidence
    [OF outcome reachable]
  obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s
        (Some (result, final_state)) trace_roots trace_bs trace_final dg
        composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers fr candidate_query_idxs
        trace_openings trace_table"
    by blast
  have no_chain:
    "\<And>doms layers. \<not>
      generic_fri_canonical_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers (bad trace_table)"
  proof
    fix doms layers
    assume chain:
      "generic_fri_canonical_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers (bad trace_table)"
    have "trace_fri_bad_with_refined_layer_chain s bad
        (Some (result, final_state))"
      unfolding trace_fri_bad_with_refined_layer_chain_def
      using evidence chain by blast
    then show False
      using not_refined by contradiction
  qed
  show ?thesis
    by (rule that[OF evidence no_chain])
qed

lemma verify_monad_composition_fri_missing_extracts_opening_evidence:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and missing:
      "composition_fri_reachable_missing_refined_layer_chain s bad
        (Some (result, final_state))"
  obtains trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table
  where
    "composition_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table"
    "to_nat fri_dg \<le> maxDegree"
    "\<And>doms layers. \<not>
      generic_fri_canonical_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers
        (bad fri_dg composition_table)"
proof -
  have reachable:
    "composition_fri_bad_with_reachable_partial_candidate s
      (Some (result, final_state))"
    and not_refined:
      "\<not> composition_fri_bad_with_refined_layer_chain s bad
        (Some (result, final_state))"
    using missing
    unfolding composition_fri_reachable_missing_refined_layer_chain_def
    by blast+
  show ?thesis
  proof (rule
      verify_monad_composition_fri_bad_extracts_opening_evidence_with_degree_bound
        [OF outcome reachable])
    fix trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table
    assume evidence:
      "composition_fri_partial_candidate_opening_evidence s
        (Some (result, final_state)) trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table"
    assume degree_bound: "to_nat fri_dg \<le> maxDegree"
    have no_chain:
      "\<And>doms layers. \<not>
        generic_fri_canonical_layer_chain_evidence
          (composition_table_low_degree (to_nat fri_dg)) composition_table
          (to_nat fri_dg) opening_composition_roots composition_bs
          composition_final fri_query_idxs composition_round_layers doms
          layers (bad fri_dg composition_table)"
    proof
      fix doms layers
      assume chain:
        "generic_fri_canonical_layer_chain_evidence
          (composition_table_low_degree (to_nat fri_dg)) composition_table
          (to_nat fri_dg) opening_composition_roots composition_bs
          composition_final fri_query_idxs composition_round_layers doms
          layers (bad fri_dg composition_table)"
      have "composition_fri_bad_with_refined_layer_chain s bad
          (Some (result, final_state))"
        using evidence chain
        unfolding composition_fri_bad_with_refined_layer_chain_def
        by metis
      then show False
        using not_refined by contradiction
    qed
    show thesis
      by (rule that[OF evidence degree_bound no_chain])
  qed
qed

lemma verify_monad_trace_fri_missing_sampled_extracts_opening_evidence:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and missing:
      "trace_fri_reachable_missing_sampled_layer_chain s
        (Some (result, final_state))"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
  where
    "trace_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr candidate_query_idxs
      trace_openings trace_table"
    "\<And>doms layers. \<not>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
proof -
  have reachable:
    "trace_fri_bad_with_reachable_partial_candidate s
      (Some (result, final_state))"
    and not_sampled:
      "\<not> trace_fri_bad_with_sampled_layer_chain s
        (Some (result, final_state))"
    using missing
    unfolding trace_fri_reachable_missing_sampled_layer_chain_def
    by blast+
  from verify_monad_trace_fri_bad_extracts_opening_evidence
    [OF outcome reachable]
  obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s
        (Some (result, final_state)) trace_roots trace_bs trace_final dg
        composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers fr candidate_query_idxs
        trace_openings trace_table"
    by blast
  have no_sampled:
    "\<And>doms layers. \<not>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
  proof
    fix doms layers
    assume chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
    have "trace_fri_bad_with_sampled_layer_chain s
        (Some (result, final_state))"
      unfolding trace_fri_bad_with_sampled_layer_chain_def
      using evidence chain by blast
    then show False
      using not_sampled by contradiction
  qed
  show ?thesis
    by (rule that[OF evidence no_sampled])
qed

lemma verify_monad_composition_fri_missing_sampled_extracts_opening_evidence:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and missing:
      "composition_fri_reachable_missing_sampled_layer_chain s
        (Some (result, final_state))"
  obtains trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table
  where
    "composition_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table"
    "to_nat fri_dg \<le> maxDegree"
    "\<And>doms layers. \<not>
      generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers"
proof -
  have reachable:
    "composition_fri_bad_with_reachable_partial_candidate s
      (Some (result, final_state))"
    and not_sampled:
      "\<not> composition_fri_bad_with_sampled_layer_chain s
        (Some (result, final_state))"
    using missing
    unfolding composition_fri_reachable_missing_sampled_layer_chain_def
    by blast+
  show ?thesis
  proof (rule
      verify_monad_composition_fri_bad_extracts_opening_evidence_with_degree_bound
        [OF outcome reachable])
    fix trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table
    assume evidence:
      "composition_fri_partial_candidate_opening_evidence s
        (Some (result, final_state)) trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table"
    assume degree_bound: "to_nat fri_dg \<le> maxDegree"
    have no_sampled:
      "\<And>doms layers. \<not>
        generic_fri_sampled_layer_chain_evidence
          (composition_table_low_degree (to_nat fri_dg)) composition_table
          (to_nat fri_dg) opening_composition_roots composition_bs
          composition_final fri_query_idxs composition_round_layers doms
          layers"
    proof
      fix doms layers
      assume chain:
        "generic_fri_sampled_layer_chain_evidence
          (composition_table_low_degree (to_nat fri_dg)) composition_table
          (to_nat fri_dg) opening_composition_roots composition_bs
          composition_final fri_query_idxs composition_round_layers doms
          layers"
      have "composition_fri_bad_with_sampled_layer_chain s
          (Some (result, final_state))"
        using evidence chain
        unfolding composition_fri_bad_with_sampled_layer_chain_def
        by metis
      then show False
        using not_sampled by contradiction
    qed
    show thesis
      by (rule that[OF evidence degree_bound no_sampled])
  qed
qed

lemma verify_monad_trace_fri_missing_full_cover_extracts_sampled_evidence:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and missing:
      "trace_fri_sampled_missing_full_cover s bad
        (Some (result, final_state))"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table doms layers
  where
    "trace_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr candidate_query_idxs
      trace_openings trace_table"
    "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers doms layers"
    "\<not> generic_fri_sampled_layer_chain_full_cover trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers doms layers (bad trace_table)"
proof -
  have sampled:
    "trace_fri_bad_with_sampled_layer_chain s
      (Some (result, final_state))"
    and not_full:
      "\<not> trace_fri_bad_with_full_cover_layer_chain s bad
        (Some (result, final_state))"
    using missing
    unfolding trace_fri_sampled_missing_full_cover_def by blast+
  from sampled obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table doms layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s
        (Some (result, final_state)) trace_roots trace_bs trace_final dg
        composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers fr candidate_query_idxs
        trace_openings trace_table"
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
    have "trace_fri_bad_with_full_cover_layer_chain s bad
        (Some (result, final_state))"
      unfolding trace_fri_bad_with_full_cover_layer_chain_def
      using evidence full by blast
    then show False
      using not_full by contradiction
  qed
  show ?thesis
    by (rule that[OF evidence chain no_full])
qed

lemma verify_monad_composition_fri_missing_full_cover_extracts_sampled_evidence:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and missing:
      "composition_fri_sampled_missing_full_cover s bad
        (Some (result, final_state))"
  obtains trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table doms layers
  where
    "composition_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table"
    "generic_fri_sampled_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers doms layers"
    "\<not> generic_fri_sampled_layer_chain_full_cover
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers doms layers
      (bad fri_dg composition_table)"
proof -
  have sampled:
    "composition_fri_bad_with_sampled_layer_chain s
      (Some (result, final_state))"
    and not_full:
      "\<not> composition_fri_bad_with_full_cover_layer_chain s bad
        (Some (result, final_state))"
    using missing
    unfolding composition_fri_sampled_missing_full_cover_def by blast+
  from sampled obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table doms layers
    where evidence:
      "composition_fri_partial_candidate_opening_evidence s
        (Some (result, final_state)) trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table"
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
        composition_final fri_query_idxs composition_round_layers doms layers
        (bad fri_dg composition_table)"
    have "composition_fri_bad_with_full_cover_layer_chain s bad
        (Some (result, final_state))"
      unfolding composition_fri_bad_with_full_cover_layer_chain_def
      using evidence full by metis
    then show False
      using not_full by contradiction
  qed
  show ?thesis
    by (rule that[OF evidence chain no_full])
qed

lemma wp_trace_fri_reachable_bound_from_refined_and_missing:
  assumes refined_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_refined_layer_chain s bad) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (trace_fri_reachable_missing_refined_layer_chain s bad) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le> R + M"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le>
    wp_event verify_monad
      (\<lambda>out. trace_fri_bad_with_refined_layer_chain s bad out \<or>
        trace_fri_reachable_missing_refined_layer_chain s bad out) s"
    by (rule wp_event_mono)
      (rule trace_fri_reachable_imp_refined_or_missing_layer_chain)
  also have "... \<le>
    wp_event verify_monad
      (trace_fri_bad_with_refined_layer_chain s bad) s +
    wp_event verify_monad
      (trace_fri_reachable_missing_refined_layer_chain s bad) s"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (intro add_mono refined_bound missing_bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_reachable_bound_from_refined_and_missing:
  assumes refined_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_refined_layer_chain s bad) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (composition_fri_reachable_missing_refined_layer_chain s bad) s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate s) s \<le> R + M"
proof -
  have "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate s) s \<le>
    wp_event verify_monad
      (\<lambda>out. composition_fri_bad_with_refined_layer_chain s bad out \<or>
        composition_fri_reachable_missing_refined_layer_chain s bad out) s"
    by (rule wp_event_mono)
      (rule composition_fri_reachable_imp_refined_or_missing_layer_chain)
  also have "... \<le>
    wp_event verify_monad
      (composition_fri_bad_with_refined_layer_chain s bad) s +
    wp_event verify_monad
      (composition_fri_reachable_missing_refined_layer_chain s bad) s"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (intro add_mono refined_bound missing_bound)
  finally show ?thesis .
qed

lemma wp_trace_fri_reachable_bound_from_sampled_and_missing:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain s) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le> R + M"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le>
    wp_event verify_monad
      (\<lambda>out. trace_fri_bad_with_sampled_layer_chain s out \<or>
        trace_fri_reachable_missing_sampled_layer_chain s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_reachable_imp_sampled_or_missing_layer_chain)
  also have "... \<le>
    wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s +
    wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (intro add_mono sampled_bound missing_bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_reachable_bound_from_sampled_and_missing:
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (composition_fri_reachable_missing_sampled_layer_chain s) s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate s) s \<le> R + M"
proof -
  have "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate s) s \<le>
    wp_event verify_monad
      (\<lambda>out. composition_fri_bad_with_sampled_layer_chain s out \<or>
        composition_fri_reachable_missing_sampled_layer_chain s out) s"
    by (rule wp_event_mono)
      (rule composition_fri_reachable_imp_sampled_or_missing_layer_chain)
  also have "... \<le>
    wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s +
    wp_event verify_monad
      (composition_fri_reachable_missing_sampled_layer_chain s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (intro add_mono sampled_bound missing_bound)
  finally show ?thesis .
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_refined_and_missing:
  assumes refined_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_refined_layer_chain s bad) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (trace_fri_reachable_missing_refined_layer_chain s bad) s \<le> M"
    and total_bound: "R + M \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have old_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le> R + M"
    by (rule wp_trace_fri_reachable_bound_from_refined_and_missing
        [OF refined_bound missing_bound])
  show ?thesis
    unfolding trace_fri_reachable_partial_candidate_reduction_assumption_def
    by (rule order_trans[OF old_bound total_bound])
qed

lemma composition_fri_reachable_partial_candidate_reduction_from_refined_and_missing:
  assumes refined_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_refined_layer_chain s bad) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (composition_fri_reachable_missing_refined_layer_chain s bad) s \<le> M"
    and total_bound: "R + M \<le> composition_fri_error"
  shows "composition_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have old_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate s) s \<le> R + M"
    by (rule wp_composition_fri_reachable_bound_from_refined_and_missing
        [OF refined_bound missing_bound])
  show ?thesis
    unfolding
      composition_fri_reachable_partial_candidate_reduction_assumption_def
    by (rule order_trans[OF old_bound total_bound])
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_sampled_and_missing:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain s) s \<le> M"
    and total_bound: "R + M \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have old_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le> R + M"
    by (rule wp_trace_fri_reachable_bound_from_sampled_and_missing
        [OF sampled_bound missing_bound])
  show ?thesis
    unfolding trace_fri_reachable_partial_candidate_reduction_assumption_def
    by (rule order_trans[OF old_bound total_bound])
qed

lemma composition_fri_reachable_partial_candidate_reduction_from_sampled_and_missing:
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (composition_fri_reachable_missing_sampled_layer_chain s) s \<le> M"
    and total_bound: "R + M \<le> composition_fri_error"
  shows "composition_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have old_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate s) s \<le> R + M"
    by (rule wp_composition_fri_reachable_bound_from_sampled_and_missing
        [OF sampled_bound missing_bound])
  show ?thesis
    unfolding
      composition_fri_reachable_partial_candidate_reduction_assumption_def
    by (rule order_trans[OF old_bound total_bound])
qed

lemma trace_fri_bad_with_partial_candidates_bound_from_refined_and_missing:
  fixes R M :: prob
  assumes refined_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_refined_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> R"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_reachable_missing_refined_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> R + M"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> trace_fri_bad_with_partial_candidates s None"
    by (rule trace_fri_bad_with_partial_candidates_not_None)
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have old_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate ?s) ?s \<le> R + M"
    by (rule wp_trace_fri_reachable_bound_from_refined_and_missing
        [OF refined_bound[OF builder] missing_bound[OF builder]])
  show "wp_event verify_monad (trace_fri_bad_with_partial_candidates ?s) ?s
      \<le> R + M"
    by (rule order_trans[OF _ old_bound])
      (rule wp_event_mono,
        rule trace_fri_bad_with_partial_candidates_imp_reachable_partial_candidate)
qed

lemma composition_fri_bad_with_partial_candidates_bound_from_refined_and_missing:
  fixes R M :: prob
  assumes refined_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_bad_with_refined_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> R"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_reachable_missing_refined_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> R + M"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> composition_fri_bad_with_partial_candidates s None"
    by (rule composition_fri_bad_with_partial_candidates_not_None)
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have old_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate ?s) ?s \<le>
      R + M"
    by (rule wp_composition_fri_reachable_bound_from_refined_and_missing
        [OF refined_bound[OF builder] missing_bound[OF builder]])
  show "wp_event verify_monad
      (composition_fri_bad_with_partial_candidates ?s) ?s \<le> R + M"
    by (rule order_trans[OF _ old_bound])
      (rule wp_event_mono,
        rule
          composition_fri_bad_with_partial_candidates_imp_reachable_partial_candidate)
qed

lemma trace_fri_bad_with_empty_header_candidates_bound_from_refined_and_missing:
  fixes R M :: prob
  assumes refined_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_refined_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> R"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_reachable_missing_refined_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> R + M"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> trace_fri_bad_with_empty_composition_header_candidates s None"
    by (rule trace_fri_bad_with_empty_composition_header_candidates_not_None)
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have old_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate ?s) ?s \<le> R + M"
    by (rule wp_trace_fri_reachable_bound_from_refined_and_missing
        [OF refined_bound[OF builder] missing_bound[OF builder]])
  show "wp_event verify_monad
      (trace_fri_bad_with_empty_composition_header_candidates ?s) ?s \<le>
      R + M"
    by (rule order_trans[OF _ old_bound])
      (rule wp_event_mono,
        rule
          trace_fri_bad_with_empty_composition_header_candidates_imp_reachable_partial_candidate)
qed

lemma trace_fri_bad_with_partial_candidates_bound_from_sampled_and_missing:
  fixes R M :: prob
  assumes sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> R"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_reachable_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> R + M"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> trace_fri_bad_with_partial_candidates s None"
    by (rule trace_fri_bad_with_partial_candidates_not_None)
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have old_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate ?s) ?s \<le> R + M"
    by (rule wp_trace_fri_reachable_bound_from_sampled_and_missing
        [OF sampled_bound[OF builder] missing_bound[OF builder]])
  show "wp_event verify_monad (trace_fri_bad_with_partial_candidates ?s) ?s
      \<le> R + M"
    by (rule order_trans[OF _ old_bound])
      (rule wp_event_mono,
        rule trace_fri_bad_with_partial_candidates_imp_reachable_partial_candidate)
qed

lemma composition_fri_bad_with_partial_candidates_bound_from_sampled_and_missing:
  fixes R M :: prob
  assumes sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_bad_with_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> R"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_reachable_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> R + M"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> composition_fri_bad_with_partial_candidates s None"
    by (rule composition_fri_bad_with_partial_candidates_not_None)
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have old_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate ?s) ?s \<le>
      R + M"
    by (rule wp_composition_fri_reachable_bound_from_sampled_and_missing
        [OF sampled_bound[OF builder] missing_bound[OF builder]])
  show "wp_event verify_monad
      (composition_fri_bad_with_partial_candidates ?s) ?s \<le> R + M"
    by (rule order_trans[OF _ old_bound])
      (rule wp_event_mono,
        rule
          composition_fri_bad_with_partial_candidates_imp_reachable_partial_candidate)
qed

lemma trace_fri_bad_with_empty_header_candidates_bound_from_sampled_and_missing:
  fixes R M :: prob
  assumes sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> R"
    and missing_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_reachable_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> R + M"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show "\<And>s. \<not> trace_fri_bad_with_empty_composition_header_candidates s None"
    by (rule trace_fri_bad_with_empty_composition_header_candidates_not_None)
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  have old_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate ?s) ?s \<le> R + M"
    by (rule wp_trace_fri_reachable_bound_from_sampled_and_missing
        [OF sampled_bound[OF builder] missing_bound[OF builder]])
  show "wp_event verify_monad
      (trace_fri_bad_with_empty_composition_header_candidates ?s) ?s \<le>
      R + M"
    by (rule order_trans[OF _ old_bound])
      (rule wp_event_mono,
        rule
          trace_fri_bad_with_empty_composition_header_candidates_imp_reachable_partial_candidate)
qed

lemma trace_fri_bad_with_partial_candidates_bound_from_full_cover_and_missing:
  fixes R MF MS :: prob
  assumes full_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_full_cover_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> R"
    and missing_full_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_missing_full_cover
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> MF"
    and missing_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_reachable_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> MS"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> (R + MF) + MS"
proof (rule trace_fri_bad_with_partial_candidates_bound_from_sampled_and_missing)
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain ?s) ?s \<le> R + MF"
    by (rule wp_trace_fri_sampled_bound_from_full_cover_and_missing
        [OF full_bound[OF builder] missing_full_bound[OF builder]])
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le> MS"
    by (rule missing_sampled_bound[OF builder])
qed

lemma composition_fri_bad_with_partial_candidates_bound_from_full_cover_and_missing:
  fixes R MF MS :: prob
  assumes full_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_bad_with_full_cover_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> R"
    and missing_full_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_missing_full_cover
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> MF"
    and missing_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_reachable_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> MS"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> (R + MF) + MS"
proof (rule
    composition_fri_bad_with_partial_candidates_bound_from_sampled_and_missing)
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain ?s) ?s \<le> R + MF"
    by (rule wp_composition_fri_sampled_bound_from_full_cover_and_missing
        [OF full_bound[OF builder] missing_full_bound[OF builder]])
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (composition_fri_reachable_missing_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le> MS"
    by (rule missing_sampled_bound[OF builder])
qed

lemma trace_fri_bad_with_empty_header_candidates_bound_from_full_cover_and_missing:
  fixes R MF MS :: prob
  assumes full_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_bad_with_full_cover_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> R"
    and missing_full_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_missing_full_cover
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> MF"
    and missing_sampled_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_reachable_missing_sampled_layer_chain
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> MS"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_empty_composition_header_candidates)
      adversary_initial_state \<le> (R + MF) + MS"
proof (rule
    trace_fri_bad_with_empty_header_candidates_bound_from_sampled_and_missing)
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain ?s) ?s \<le> R + MF"
    by (rule wp_trace_fri_sampled_bound_from_full_cover_and_missing
        [OF full_bound[OF builder] missing_full_bound[OF builder]])
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le> MS"
    by (rule missing_sampled_bound[OF builder])
qed

end

end
