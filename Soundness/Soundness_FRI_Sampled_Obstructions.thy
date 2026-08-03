(*  Title:      Stark/Soundness_FRI_Sampled_Obstructions.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Sampled_Obstructions
  imports Soundness_FRI_Full_Cover_Domains
begin

text \<open>
  Explicit obstruction events for the branch where an accepting verifier
  execution reaches the broad reachable FRI bad event, but no sampled FRI
  layer-chain witness exists.

  These predicates are proof-routing devices only.  They do not reconstruct
  complete FRI tables from sampled openings; they record that the verifier's
  partial FRI evidence cannot be organized into the sampled layer-chain object
  required by the generic low-degree reduction.
\<close>

context soundness
begin

definition generic_fri_sampled_next_value_conflict
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> bool"
where
  "generic_fri_sampled_next_value_conflict roots challenges query_idxs
      round_layers \<longleftrightarrow>
    (\<exists>round_idx round_idx' layer_idx v v'.
      round_idx < length query_idxs \<and>
      round_idx' < length query_idxs \<and>
      layer_idx < length challenges \<and>
      fri_evidence_next_idx roots query_idxs round_idx layer_idx =
        fri_evidence_next_idx roots query_idxs round_idx' layer_idx \<and>
      generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx layer_idx v \<and>
      generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx' layer_idx v' \<and>
      v \<noteq> v')"

definition generic_fri_sampled_final_value_conflict
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> bool"
where
  "generic_fri_sampled_final_value_conflict roots challenges final_value
      query_idxs round_layers \<longleftrightarrow>
    (\<exists>round_idx v.
      0 < length challenges \<and>
      round_idx < length query_idxs \<and>
      generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx (length challenges - 1) v \<and>
      v \<noteq> final_value)"

definition generic_fri_sampled_base_opening_conflict
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> bool"
where
  "generic_fri_sampled_base_opening_conflict candidate_table roots challenges
      query_idxs round_layers \<longleftrightarrow>
    (\<exists>round_idx xp xp_path xn xn_path.
      0 < length challenges \<and>
      round_idx < length query_idxs \<and>
      fri_layer_step_evidence
        (roots ! 0)
        (challenges ! 0)
        (fri_evidence_layer_len roots 0)
        (fri_evidence_layer_idx roots query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len roots 0)
          (fri_evidence_layer_idx roots query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx 0)
        (fri_evidence_next_value roots challenges query_idxs round_idx 0
          xp xn)
        (round_layers ! round_idx ! 0) \<and>
      \<not> fri_opening_matches_table (fri_evidence_layer_len roots 0)
        (fri_evidence_layer_idx roots query_idxs round_idx 0)
        candidate_table xp xn)"

definition generic_fri_sampled_successor_opening_conflict
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> bool"
where
  "generic_fri_sampled_successor_opening_conflict roots challenges query_idxs
      round_layers \<longleftrightarrow>
    (\<exists>source_round target_round layer_idx v xp xp_path xn xn_path.
      source_round < length query_idxs \<and>
      target_round < length query_idxs \<and>
      Suc layer_idx < length challenges \<and>
      generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers source_round layer_idx v \<and>
      fri_layer_step_evidence
        (roots ! Suc layer_idx)
        (challenges ! Suc layer_idx)
        (fri_evidence_layer_len roots (Suc layer_idx))
        (fri_evidence_layer_idx roots query_idxs target_round
          (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs target_round
            (Suc layer_idx)))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs target_round
          (Suc layer_idx))
        (fri_evidence_next_value roots challenges query_idxs target_round
          (Suc layer_idx) xp xn)
        (round_layers ! target_round ! Suc layer_idx) \<and>
      ((fri_evidence_next_idx roots query_idxs source_round layer_idx =
          fri_evidence_layer_idx roots query_idxs target_round
            (Suc layer_idx) \<and>
        v \<noteq> xp) \<or>
       (fri_evidence_next_idx roots query_idxs source_round layer_idx =
          fri_sibling_index (fri_evidence_layer_len roots (Suc layer_idx))
            (fri_evidence_layer_idx roots query_idxs target_round
              (Suc layer_idx)) \<and>
        v \<noteq> xn)))"

definition generic_fri_sampled_same_layer_opening_conflict
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> bool"
where
  "generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers \<longleftrightarrow>
    (\<exists>round_idx round_idx' layer_idx
        xp xp_path xn xn_path yp yp_path yn yn_path.
      round_idx < length query_idxs \<and>
      round_idx' < length query_idxs \<and>
      layer_idx < length challenges \<and>
      fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx) \<and>
      fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
        yp yp_path yn yn_path
        (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx'
          layer_idx yp yn)
        (round_layers ! round_idx' ! layer_idx) \<and>
      ((fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xp \<noteq> yp) \<or>
       (fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xp \<noteq> yn) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_evidence_layer_idx roots query_idxs round_idx' layer_idx \<and>
        xn \<noteq> yp) \<or>
       (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
          fri_sibling_index (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
        xn \<noteq> yn)))"

lemma generic_fri_sampled_next_value_conflictE:
  assumes
    "generic_fri_sampled_next_value_conflict roots challenges query_idxs
      round_layers"
  obtains round_idx round_idx' layer_idx v v'
  where
    "round_idx < length query_idxs"
    "round_idx' < length query_idxs"
    "layer_idx < length challenges"
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx =
      fri_evidence_next_idx roots query_idxs round_idx' layer_idx"
    "generic_fri_round_forced_next_value roots challenges query_idxs
      round_layers round_idx layer_idx v"
    "generic_fri_round_forced_next_value roots challenges query_idxs
      round_layers round_idx' layer_idx v'"
    "v \<noteq> v'"
  using assms unfolding generic_fri_sampled_next_value_conflict_def
  by blast

lemma generic_fri_sampled_final_value_conflictE:
  assumes
    "generic_fri_sampled_final_value_conflict roots challenges final_value
      query_idxs round_layers"
  obtains round_idx v
  where
    "0 < length challenges"
    "round_idx < length query_idxs"
    "generic_fri_round_forced_next_value roots challenges query_idxs
      round_layers round_idx (length challenges - 1) v"
    "v \<noteq> final_value"
  using assms unfolding generic_fri_sampled_final_value_conflict_def
  by blast

lemma generic_fri_sampled_successor_opening_conflictE:
  assumes
    "generic_fri_sampled_successor_opening_conflict roots challenges
      query_idxs round_layers"
  obtains source_round target_round layer_idx v xp xp_path xn xn_path
  where
    "source_round < length query_idxs"
    "target_round < length query_idxs"
    "Suc layer_idx < length challenges"
    "generic_fri_round_forced_next_value roots challenges query_idxs
      round_layers source_round layer_idx v"
    "fri_layer_step_evidence
      (roots ! Suc layer_idx)
      (challenges ! Suc layer_idx)
      (fri_evidence_layer_len roots (Suc layer_idx))
      (fri_evidence_layer_idx roots query_idxs target_round
        (Suc layer_idx))
      (2 ^ Suc layer_idx)
      (fri_sibling_index (fri_evidence_layer_len roots (Suc layer_idx))
        (fri_evidence_layer_idx roots query_idxs target_round
          (Suc layer_idx)))
      xp xp_path xn xn_path
      (fri_evidence_next_idx roots query_idxs target_round
        (Suc layer_idx))
      (fri_evidence_next_value roots challenges query_idxs target_round
        (Suc layer_idx) xp xn)
      (round_layers ! target_round ! Suc layer_idx)"
    "((fri_evidence_next_idx roots query_idxs source_round layer_idx =
        fri_evidence_layer_idx roots query_idxs target_round
          (Suc layer_idx) \<and>
      v \<noteq> xp) \<or>
     (fri_evidence_next_idx roots query_idxs source_round layer_idx =
        fri_sibling_index (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs target_round
            (Suc layer_idx)) \<and>
      v \<noteq> xn))"
  using assms unfolding generic_fri_sampled_successor_opening_conflict_def
  by blast

definition generic_fri_sampled_layer_assignment_obstruction
  :: "('f list \<Rightarrow> bool) \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> bool"
where
  "generic_fri_sampled_layer_assignment_obstruction low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers \<longleftrightarrow>
    generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers \<and>
    (\<forall>doms layers. \<not>
      generic_fri_sampled_layer_chain_evidence low_degree candidate_table
        degree_bound roots challenges final_value query_idxs round_layers
        doms layers)"

definition generic_fri_sampled_assignment_conflict
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      nat list \<Rightarrow> 'f list list list \<Rightarrow> bool"
where
  "generic_fri_sampled_assignment_conflict candidate_table roots challenges
      final_value query_idxs round_layers \<longleftrightarrow>
    generic_fri_sampled_base_opening_conflict candidate_table roots
      challenges query_idxs round_layers \<or>
    generic_fri_sampled_next_value_conflict roots challenges query_idxs
      round_layers \<or>
    generic_fri_sampled_successor_opening_conflict roots challenges
      query_idxs round_layers \<or>
    generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers \<or>
    generic_fri_sampled_final_value_conflict roots challenges final_value
      query_idxs round_layers"

definition generic_fri_sampled_layer_value_constraint
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      nat list \<Rightarrow> 'f list list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      'f \<Rightarrow> bool"
where
  "generic_fri_sampled_layer_value_constraint candidate_table roots
      challenges final_value query_idxs round_layers layer_idx idx v
    \<longleftrightarrow>
    (if layer_idx = 0 then
       idx < length candidate_table \<and> v = candidate_table ! idx
     else if layer_idx = length challenges then
       v = final_value
     else
       (\<exists>round_idx.
          round_idx < length query_idxs \<and>
          generic_fri_round_forced_next_value roots challenges query_idxs
            round_layers round_idx (layer_idx - 1) v \<and>
          fri_evidence_next_idx roots query_idxs round_idx
            (layer_idx - 1) = idx) \<or>
       (\<exists>round_idx xp xp_path xn xn_path.
          round_idx < length query_idxs \<and>
          layer_idx < length challenges \<and>
          fri_layer_step_evidence
            (roots ! layer_idx)
            (challenges ! layer_idx)
            (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
            (2 ^ layer_idx)
            (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
            xp xp_path xn xn_path
            (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
            (fri_evidence_next_value roots challenges query_idxs round_idx
              layer_idx xp xn)
            (round_layers ! round_idx ! layer_idx) \<and>
          ((idx = fri_evidence_layer_idx roots query_idxs round_idx
              layer_idx \<and> v = xp) \<or>
           (idx = fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) \<and>
            v = xn))))"

definition generic_fri_sampled_layer_value
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      nat list \<Rightarrow> 'f list list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f"
where
  "generic_fri_sampled_layer_value candidate_table roots challenges
      final_value query_idxs round_layers layer_idx idx =
    (if \<exists>v. generic_fri_sampled_layer_value_constraint candidate_table
        roots challenges final_value query_idxs round_layers layer_idx idx v
     then SOME v. generic_fri_sampled_layer_value_constraint
        candidate_table roots challenges final_value query_idxs round_layers
        layer_idx idx v
     else final_value)"

definition generic_fri_sampled_assignment_layer
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      nat list \<Rightarrow> 'f list list list \<Rightarrow> nat \<Rightarrow> 'f list"
where
  "generic_fri_sampled_assignment_layer candidate_table roots challenges
      final_value query_idxs round_layers layer_idx =
    (if layer_idx = 0 then candidate_table
     else map (generic_fri_sampled_layer_value candidate_table roots
      challenges final_value query_idxs round_layers layer_idx)
      [0..<clength * scale])"

definition generic_fri_sampled_assignment_layers
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow>
      nat list \<Rightarrow> 'f list list list \<Rightarrow> 'f list list"
where
  "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers =
    map (generic_fri_sampled_assignment_layer candidate_table roots
      challenges final_value query_idxs round_layers)
      [0..<Suc (length challenges)]"

lemma generic_fri_sampled_assignment_layer_length_nonzero[simp]:
  assumes "layer_idx \<noteq> 0"
  shows "length (generic_fri_sampled_assignment_layer candidate_table roots
      challenges final_value query_idxs round_layers layer_idx) =
    clength * scale"
  using assms unfolding generic_fri_sampled_assignment_layer_def by simp

lemma generic_fri_sampled_assignment_layer_zero[simp]:
  "generic_fri_sampled_assignment_layer candidate_table roots challenges
      final_value query_idxs round_layers 0 = candidate_table"
  unfolding generic_fri_sampled_assignment_layer_def by simp

lemma generic_fri_sampled_assignment_layers_length[simp]:
  "length (generic_fri_sampled_assignment_layers candidate_table roots
      challenges final_value query_idxs round_layers) =
    Suc (length challenges)"
  unfolding generic_fri_sampled_assignment_layers_def by simp

lemma generic_fri_sampled_assignment_layers_nth:
  assumes "layer_idx \<le> length challenges"
  shows
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers ! layer_idx =
     generic_fri_sampled_assignment_layer candidate_table roots challenges
      final_value query_idxs round_layers layer_idx"
proof (cases "layer_idx < length challenges")
  case True
  then show ?thesis
    unfolding generic_fri_sampled_assignment_layers_def
    by (simp add: nth_append)
next
  case False
  then have layer_eq: "layer_idx = length challenges"
    using assms by simp
  then show ?thesis
    unfolding generic_fri_sampled_assignment_layers_def
    by (simp add: nth_append)
qed

lemma generic_fri_sampled_assignment_layers_base[simp]:
  "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers ! 0 = candidate_table"
  using generic_fri_sampled_assignment_layers_nth[of 0 challenges
      candidate_table roots final_value query_idxs round_layers]
  by simp

lemma generic_fri_sampled_layer_value_unique:
  assumes constraint:
    "generic_fri_sampled_layer_value_constraint candidate_table roots
      challenges final_value query_idxs round_layers layer_idx idx v"
    and unique:
      "\<And>v'. generic_fri_sampled_layer_value_constraint candidate_table
        roots challenges final_value query_idxs round_layers layer_idx idx v'
        \<Longrightarrow> v' = v"
  shows
    "generic_fri_sampled_layer_value candidate_table roots challenges
      final_value query_idxs round_layers layer_idx idx = v"
proof -
  have ex: "\<exists>v. generic_fri_sampled_layer_value_constraint
    candidate_table roots challenges final_value query_idxs round_layers
    layer_idx idx v"
    using constraint by blast
  have some_eq:
    "(SOME v. generic_fri_sampled_layer_value_constraint candidate_table
      roots challenges final_value query_idxs round_layers layer_idx idx v) =
      v"
    by (rule some_equality) (use constraint unique in blast)+
  show ?thesis
    unfolding generic_fri_sampled_layer_value_def
    using ex some_eq by simp
qed

lemma generic_fri_sampled_assignment_layer_nth_unique:
  assumes idx_bound: "idx < clength * scale"
    and layer_nonzero: "layer_idx \<noteq> 0"
    and constraint:
      "generic_fri_sampled_layer_value_constraint candidate_table roots
        challenges final_value query_idxs round_layers layer_idx idx v"
    and unique:
      "\<And>v'. generic_fri_sampled_layer_value_constraint candidate_table
        roots challenges final_value query_idxs round_layers layer_idx idx v'
        \<Longrightarrow> v' = v"
  shows
    "generic_fri_sampled_assignment_layer candidate_table roots challenges
      final_value query_idxs round_layers layer_idx ! idx = v"
  unfolding generic_fri_sampled_assignment_layer_def
  using idx_bound layer_nonzero
  by (simp add: generic_fri_sampled_layer_value_unique[OF constraint unique])

lemma generic_fri_sampled_final_assignment_layer_consistent:
  assumes challenges_nonempty: "0 < length challenges"
  shows
    "fri_final_constant_consistent
      (generic_fri_sampled_assignment_layers candidate_table roots challenges
        final_value query_idxs round_layers ! length challenges)
      final_value"
proof -
  let ?layer =
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers ! length challenges"
  have layer_eq:
    "?layer =
      generic_fri_sampled_assignment_layer candidate_table roots challenges
        final_value query_idxs round_layers (length challenges)"
    by (rule generic_fri_sampled_assignment_layers_nth) simp
  have layer_len: "length ?layer = clength * scale"
    using challenges_nonempty layer_eq by simp
  have nth_final:
    "\<And>idx. idx < length ?layer \<Longrightarrow> ?layer ! idx = final_value"
  proof -
    fix idx
    assume idx_bound_layer: "idx < length ?layer"
    then have idx_bound: "idx < clength * scale"
      using layer_len by simp
    have constraint:
      "generic_fri_sampled_layer_value_constraint candidate_table roots
        challenges final_value query_idxs round_layers
        (length challenges) idx final_value"
      using challenges_nonempty
      unfolding generic_fri_sampled_layer_value_constraint_def by simp
    have unique:
      "\<And>v'. generic_fri_sampled_layer_value_constraint candidate_table
        roots challenges final_value query_idxs round_layers
        (length challenges) idx v' \<Longrightarrow> v' = final_value"
      using challenges_nonempty
      unfolding generic_fri_sampled_layer_value_constraint_def by simp
    show "?layer ! idx = final_value"
      unfolding layer_eq
      by (rule generic_fri_sampled_assignment_layer_nth_unique
          [OF idx_bound _ constraint unique])
        (use challenges_nonempty in simp)
  qed
  show ?thesis
    unfolding fri_final_constant_consistent_def
    using nth_final by (auto simp: in_set_conv_nth)
qed

definition trace_fri_sampled_layer_assignment_obstruction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_layer_assignment_obstruction s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_layer_assignment_obstruction
        trace_table_low_degree trace_table (clength - 1) trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers)"

definition composition_fri_sampled_layer_assignment_obstruction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_layer_assignment_obstruction s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_layer_assignment_obstruction
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers)"

definition trace_fri_sampled_assignment_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_assignment_conflict s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_assignment_conflict trace_table trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers)"

definition composition_fri_sampled_assignment_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_assignment_conflict s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_sampled_assignment_conflict composition_table
        opening_composition_roots composition_bs composition_final
        fri_query_idxs composition_round_layers)"

lemma generic_fri_sampled_layer_assignment_obstructionD:
  assumes
    "generic_fri_sampled_layer_assignment_obstruction low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers"
  shows
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    "\<And>doms layers. \<not>
      generic_fri_sampled_layer_chain_evidence low_degree candidate_table
        degree_bound roots challenges final_value query_idxs round_layers
        doms layers"
  using assms
  unfolding generic_fri_sampled_layer_assignment_obstruction_def
  by simp_all

lemma trace_fri_sampled_layer_assignment_obstructionE:
  assumes
    "trace_fri_sampled_layer_assignment_obstruction s out"
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
    "generic_fri_sampled_layer_assignment_obstruction
      trace_table_low_degree trace_table (clength - 1) trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers"
  using assms
  unfolding trace_fri_sampled_layer_assignment_obstruction_def
  apply (elim exE conjE)
  apply (rule that)
   apply assumption
  apply assumption
  done

lemma composition_fri_sampled_layer_assignment_obstructionE:
  assumes
    "composition_fri_sampled_layer_assignment_obstruction s out"
  obtains trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table
  where
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
    "generic_fri_sampled_layer_assignment_obstruction
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers"
  using assms
  unfolding composition_fri_sampled_layer_assignment_obstruction_def
  apply (elim exE conjE)
  apply (rule that)
   apply assumption
  apply assumption
  done

lemma generic_fri_no_next_value_conflict_unique:
  assumes no_conflict:
    "\<not> generic_fri_sampled_next_value_conflict roots challenges
      query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
    and same_idx:
      "fri_evidence_next_idx roots query_idxs round_idx layer_idx =
       fri_evidence_next_idx roots query_idxs round_idx' layer_idx"
    and forced:
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx layer_idx v"
    and forced':
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx' layer_idx v'"
  shows "v = v'"
  using assms
  unfolding generic_fri_sampled_next_value_conflict_def
  by blast

lemma generic_fri_no_final_value_conflict_forced_eq:
  assumes no_conflict:
    "\<not> generic_fri_sampled_final_value_conflict roots challenges
      final_value query_idxs round_layers"
    and challenges_nonempty: "0 < length challenges"
    and round_bound: "round_idx < length query_idxs"
    and forced:
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx (length challenges - 1) v"
  shows "v = final_value"
  using assms
  unfolding generic_fri_sampled_final_value_conflict_def
  by blast

lemma generic_fri_no_assignment_conflict_no_final:
  assumes
    "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
  shows
    "\<not> generic_fri_sampled_final_value_conflict roots challenges
      final_value query_idxs round_layers"
  using assms unfolding generic_fri_sampled_assignment_conflict_def by simp

lemma generic_fri_no_assignment_conflict_no_next:
  assumes
    "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
  shows
    "\<not> generic_fri_sampled_next_value_conflict roots challenges
      query_idxs round_layers"
  using assms unfolding generic_fri_sampled_assignment_conflict_def by simp

lemma generic_fri_sampled_final_layer_forced_value:
  assumes no_conflict:
    "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
    and challenges_nonempty: "0 < length challenges"
    and round_bound: "round_idx < length query_idxs"
    and idx_bound:
      "fri_evidence_next_idx roots query_idxs round_idx
        (length challenges - 1) < clength * scale"
    and forced:
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx (length challenges - 1) v"
  shows
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers ! length challenges !
        fri_evidence_next_idx roots query_idxs round_idx
          (length challenges - 1) = v"
proof -
  have v_final: "v = final_value"
    by (rule generic_fri_no_final_value_conflict_forced_eq
        [OF generic_fri_no_assignment_conflict_no_final[OF no_conflict]
          challenges_nonempty round_bound forced])
  let ?idx =
    "fri_evidence_next_idx roots query_idxs round_idx
      (length challenges - 1)"
  have layer_eq:
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers ! length challenges =
     generic_fri_sampled_assignment_layer candidate_table roots challenges
      final_value query_idxs round_layers (length challenges)"
    by (rule generic_fri_sampled_assignment_layers_nth) simp
  have constraint:
    "generic_fri_sampled_layer_value_constraint candidate_table roots
      challenges final_value query_idxs round_layers
      (length challenges) ?idx final_value"
    using challenges_nonempty
    unfolding generic_fri_sampled_layer_value_constraint_def by simp
  have unique:
    "\<And>v'. generic_fri_sampled_layer_value_constraint candidate_table roots
      challenges final_value query_idxs round_layers
      (length challenges) ?idx v' \<Longrightarrow> v' = final_value"
    using challenges_nonempty
    unfolding generic_fri_sampled_layer_value_constraint_def by simp
  have nth_final:
    "generic_fri_sampled_assignment_layer candidate_table roots challenges
      final_value query_idxs round_layers (length challenges) ! ?idx =
      final_value"
    by (rule generic_fri_sampled_assignment_layer_nth_unique
        [OF idx_bound _ constraint unique])
      (use challenges_nonempty in simp)
  show ?thesis
    using nth_final v_final unfolding layer_eq by simp
qed

lemma generic_fri_no_base_opening_conflict_matches_step:
  assumes no_conflict:
    "\<not> generic_fri_sampled_base_opening_conflict candidate_table roots
      challenges query_idxs round_layers"
    and challenges_nonempty: "0 < length challenges"
    and round_bound: "round_idx < length query_idxs"
    and step:
      "fri_layer_step_evidence
        (roots ! 0)
        (challenges ! 0)
        (fri_evidence_layer_len roots 0)
        (fri_evidence_layer_idx roots query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len roots 0)
          (fri_evidence_layer_idx roots query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx 0)
        (fri_evidence_next_value roots challenges query_idxs round_idx 0
          xp xn)
        (round_layers ! round_idx ! 0)"
  shows
    "fri_opening_matches_table (fri_evidence_layer_len roots 0)
      (fri_evidence_layer_idx roots query_idxs round_idx 0)
      candidate_table xp xn"
  using assms
  unfolding generic_fri_sampled_base_opening_conflict_def
  by blast

lemma generic_fri_no_assignment_conflict_no_base:
  assumes
    "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
  shows
    "\<not> generic_fri_sampled_base_opening_conflict candidate_table roots
      challenges query_idxs round_layers"
  using assms unfolding generic_fri_sampled_assignment_conflict_def by simp

lemma generic_fri_sampled_assignment_base_matches_step:
  assumes no_conflict:
    "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
    and challenges_nonempty: "0 < length challenges"
    and round_bound: "round_idx < length query_idxs"
    and step:
      "fri_layer_step_evidence
        (roots ! 0)
        (challenges ! 0)
        (fri_evidence_layer_len roots 0)
        (fri_evidence_layer_idx roots query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len roots 0)
          (fri_evidence_layer_idx roots query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx 0)
        (fri_evidence_next_value roots challenges query_idxs round_idx 0
          xp xn)
        (round_layers ! round_idx ! 0)"
  shows
    "fri_opening_matches_table (fri_evidence_layer_len roots 0)
      (fri_evidence_layer_idx roots query_idxs round_idx 0)
      (generic_fri_sampled_assignment_layers candidate_table roots
        challenges final_value query_idxs round_layers ! 0) xp xn"
proof -
  have base_match:
    "fri_opening_matches_table (fri_evidence_layer_len roots 0)
      (fri_evidence_layer_idx roots query_idxs round_idx 0)
      candidate_table xp xn"
    by (rule generic_fri_no_base_opening_conflict_matches_step
        [OF generic_fri_no_assignment_conflict_no_base[OF no_conflict]
          challenges_nonempty round_bound step])
  show ?thesis
    using base_match by simp
qed

lemma generic_fri_no_successor_opening_conflict_matches_left:
  assumes no_conflict:
    "\<not> generic_fri_sampled_successor_opening_conflict roots challenges
      query_idxs round_layers"
    and source_bound: "source_round < length query_idxs"
    and target_bound: "target_round < length query_idxs"
    and layer_bound: "Suc layer_idx < length challenges"
    and forced:
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers source_round layer_idx v"
    and step:
      "fri_layer_step_evidence
        (roots ! Suc layer_idx)
        (challenges ! Suc layer_idx)
        (fri_evidence_layer_len roots (Suc layer_idx))
        (fri_evidence_layer_idx roots query_idxs target_round
          (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs target_round
            (Suc layer_idx)))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs target_round
          (Suc layer_idx))
        (fri_evidence_next_value roots challenges query_idxs target_round
          (Suc layer_idx) xp xn)
        (round_layers ! target_round ! Suc layer_idx)"
    and same_idx:
      "fri_evidence_next_idx roots query_idxs source_round layer_idx =
        fri_evidence_layer_idx roots query_idxs target_round
          (Suc layer_idx)"
  shows "v = xp"
  using assms
  unfolding generic_fri_sampled_successor_opening_conflict_def
  by blast

lemma generic_fri_no_successor_opening_conflict_matches_right:
  assumes no_conflict:
    "\<not> generic_fri_sampled_successor_opening_conflict roots challenges
      query_idxs round_layers"
    and source_bound: "source_round < length query_idxs"
    and target_bound: "target_round < length query_idxs"
    and layer_bound: "Suc layer_idx < length challenges"
    and forced:
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers source_round layer_idx v"
    and step:
      "fri_layer_step_evidence
        (roots ! Suc layer_idx)
        (challenges ! Suc layer_idx)
        (fri_evidence_layer_len roots (Suc layer_idx))
        (fri_evidence_layer_idx roots query_idxs target_round
          (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs target_round
            (Suc layer_idx)))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs target_round
          (Suc layer_idx))
        (fri_evidence_next_value roots challenges query_idxs target_round
          (Suc layer_idx) xp xn)
        (round_layers ! target_round ! Suc layer_idx)"
    and same_idx:
      "fri_evidence_next_idx roots query_idxs source_round layer_idx =
        fri_sibling_index (fri_evidence_layer_len roots (Suc layer_idx))
          (fri_evidence_layer_idx roots query_idxs target_round
            (Suc layer_idx))"
  shows "v = xn"
  using assms
  unfolding generic_fri_sampled_successor_opening_conflict_def
  by blast

lemma generic_fri_no_same_layer_opening_conflict_left_left:
  assumes no_conflict:
    "\<not> generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx)"
    and step':
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
        yp yp_path yn yn_path
        (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx'
          layer_idx yp yn)
        (round_layers ! round_idx' ! layer_idx)"
    and same_idx:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
        fri_evidence_layer_idx roots query_idxs round_idx' layer_idx"
  shows "xp = yp"
  using assms
  unfolding generic_fri_sampled_same_layer_opening_conflict_def
  by blast

lemma generic_fri_no_same_layer_opening_conflict_left_right:
  assumes no_conflict:
    "\<not> generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx)"
    and step':
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
        yp yp_path yn yn_path
        (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx'
          layer_idx yp yn)
        (round_layers ! round_idx' ! layer_idx)"
    and same_idx:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx =
        fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)"
  shows "xp = yn"
  using assms
  unfolding generic_fri_sampled_same_layer_opening_conflict_def
  by blast

lemma generic_fri_no_same_layer_opening_conflict_right_left:
  assumes no_conflict:
    "\<not> generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx)"
    and step':
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
        yp yp_path yn yn_path
        (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx'
          layer_idx yp yn)
        (round_layers ! round_idx' ! layer_idx)"
    and same_idx:
      "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
        fri_evidence_layer_idx roots query_idxs round_idx' layer_idx"
  shows "xn = yp"
  using assms
  unfolding generic_fri_sampled_same_layer_opening_conflict_def
  by blast

lemma generic_fri_no_same_layer_opening_conflict_right_right:
  assumes no_conflict:
    "\<not> generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
    and round_bound': "round_idx' < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx)"
    and step':
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
        yp yp_path yn yn_path
        (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx'
          layer_idx yp yn)
        (round_layers ! round_idx' ! layer_idx)"
    and same_idx:
      "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) =
        fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)"
  shows "xn = yn"
  using assms
  unfolding generic_fri_sampled_same_layer_opening_conflict_def
  by blast

lemma generic_fri_no_assignment_conflict_no_successor:
  assumes
    "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
  shows
    "\<not> generic_fri_sampled_successor_opening_conflict roots challenges
      query_idxs round_layers"
  using assms unfolding generic_fri_sampled_assignment_conflict_def by simp

lemma generic_fri_no_assignment_conflict_no_same:
  assumes
    "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
  shows
    "\<not> generic_fri_sampled_same_layer_opening_conflict roots challenges
      query_idxs round_layers"
  using assms unfolding generic_fri_sampled_assignment_conflict_def by simp

lemma generic_fri_sampled_layer_value_constraint_current_left:
  assumes layer_nonzero: "0 < layer_idx"
    and layer_bound: "layer_idx < length challenges"
    and round_bound: "round_idx < length query_idxs"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx)"
  shows
    "generic_fri_sampled_layer_value_constraint candidate_table roots
      challenges final_value query_idxs round_layers layer_idx
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) xp"
proof -
  have nz: "layer_idx \<noteq> 0"
    using layer_nonzero by simp
  have not_final: "layer_idx \<noteq> length challenges"
    using layer_nonzero layer_bound by simp_all
  show ?thesis
    unfolding generic_fri_sampled_layer_value_constraint_def
    apply (simp add: nz not_final)
    apply (rule disjI2)
    apply (rule exI[of _ round_idx])
    apply (intro conjI)
      apply (rule round_bound)
     apply (rule layer_bound)
    apply (rule exI[of _ xp])
    apply (rule exI[of _ xp_path])
    apply (rule exI[of _ xn])
    apply (intro conjI)
       apply (rule exI[of _ xn_path])
       apply (rule step)
      apply simp
    done
qed

lemma generic_fri_sampled_layer_value_constraint_current_right:
  assumes layer_nonzero: "0 < layer_idx"
    and layer_bound: "layer_idx < length challenges"
    and round_bound: "round_idx < length query_idxs"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx)"
  shows
    "generic_fri_sampled_layer_value_constraint candidate_table roots
      challenges final_value query_idxs round_layers layer_idx
      (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)) xn"
proof -
  have nz: "layer_idx \<noteq> 0"
    using layer_nonzero by simp
  have not_final: "layer_idx \<noteq> length challenges"
    using layer_nonzero layer_bound by simp_all
  show ?thesis
    unfolding generic_fri_sampled_layer_value_constraint_def
    apply (simp add: nz not_final)
    apply (rule disjI2)
    apply (rule exI[of _ round_idx])
    apply (intro conjI)
      apply (rule round_bound)
     apply (rule layer_bound)
    apply (rule exI[of _ xp])
    apply (rule exI[of _ xp_path])
    apply (rule exI[of _ xn])
    apply (intro conjI)
       apply (rule exI[of _ xn_path])
       apply (rule step)
      apply simp
    done
qed

lemma generic_fri_sampled_assignment_current_left_matches_step:
  assumes no_conflict:
    "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
    and layer_nonzero: "0 < layer_idx"
    and layer_bound: "layer_idx < length challenges"
    and round_bound: "round_idx < length query_idxs"
    and idx_bound:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
        clength * scale"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx)"
  shows
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers ! layer_idx !
      fri_evidence_layer_idx roots query_idxs round_idx layer_idx = xp"
proof -
  let ?raw = "fri_evidence_layer_idx roots query_idxs round_idx layer_idx"
  have layer_eq:
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers ! layer_idx =
     generic_fri_sampled_assignment_layer candidate_table roots challenges
      final_value query_idxs round_layers layer_idx"
    by (rule generic_fri_sampled_assignment_layers_nth)
      (use layer_bound in simp)
  have constraint:
    "generic_fri_sampled_layer_value_constraint candidate_table roots
      challenges final_value query_idxs round_layers layer_idx ?raw xp"
    by (rule generic_fri_sampled_layer_value_constraint_current_left
        [OF layer_nonzero layer_bound round_bound step])
  have unique:
    "\<And>v'. generic_fri_sampled_layer_value_constraint candidate_table roots
      challenges final_value query_idxs round_layers layer_idx ?raw v'
      \<Longrightarrow> v' = xp"
  proof -
    fix v'
    assume c:
      "generic_fri_sampled_layer_value_constraint candidate_table roots
        challenges final_value query_idxs round_layers layer_idx ?raw v'"
    have pred_or_current:
      "(\<exists>source_round.
          source_round < length query_idxs \<and>
          generic_fri_round_forced_next_value roots challenges query_idxs
            round_layers source_round (layer_idx - 1) v' \<and>
          fri_evidence_next_idx roots query_idxs source_round
            (layer_idx - 1) = ?raw) \<or>
       (\<exists>round_idx' yp yp_path yn yn_path.
          round_idx' < length query_idxs \<and>
          layer_idx < length challenges \<and>
          fri_layer_step_evidence
            (roots ! layer_idx)
            (challenges ! layer_idx)
            (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
            (2 ^ layer_idx)
            (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
            yp yp_path yn yn_path
            (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
            (fri_evidence_next_value roots challenges query_idxs round_idx'
              layer_idx yp yn)
            (round_layers ! round_idx' ! layer_idx) \<and>
          ((?raw = fri_evidence_layer_idx roots query_idxs round_idx'
              layer_idx \<and> v' = yp) \<or>
           (?raw = fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
            v' = yn)))"
      using c layer_nonzero layer_bound
      unfolding generic_fri_sampled_layer_value_constraint_def
      by auto
    then show "v' = xp"
    proof
      assume
        "\<exists>source_round.
          source_round < length query_idxs \<and>
          generic_fri_round_forced_next_value roots challenges query_idxs
            round_layers source_round (layer_idx - 1) v' \<and>
          fri_evidence_next_idx roots query_idxs source_round
            (layer_idx - 1) = ?raw"
      then obtain source_round where source_bound:
          "source_round < length query_idxs"
        and forced:
          "generic_fri_round_forced_next_value roots challenges query_idxs
            round_layers source_round (layer_idx - 1) v'"
        and same_idx:
          "fri_evidence_next_idx roots query_idxs source_round
            (layer_idx - 1) = ?raw"
        by blast
      have suc: "Suc (layer_idx - 1) = layer_idx"
        using layer_nonzero by simp
      have "v' = xp"
        using generic_fri_no_successor_opening_conflict_matches_left
          [OF generic_fri_no_assignment_conflict_no_successor[OF no_conflict]
            source_bound round_bound, of "layer_idx - 1" v'
            xp xp_path xn xn_path]
          layer_bound forced step same_idx suc by simp
      then show ?thesis .
    next
      assume
        "\<exists>round_idx' yp yp_path yn yn_path.
          round_idx' < length query_idxs \<and>
          layer_idx < length challenges \<and>
          fri_layer_step_evidence
            (roots ! layer_idx)
            (challenges ! layer_idx)
            (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
            (2 ^ layer_idx)
            (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
            yp yp_path yn yn_path
            (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
            (fri_evidence_next_value roots challenges query_idxs round_idx'
              layer_idx yp yn)
            (round_layers ! round_idx' ! layer_idx) \<and>
          ((?raw = fri_evidence_layer_idx roots query_idxs round_idx'
              layer_idx \<and> v' = yp) \<or>
           (?raw = fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
            v' = yn))"
      then obtain round_idx' yp yp_path yn yn_path where round_bound':
          "round_idx' < length query_idxs"
        and step':
          "fri_layer_step_evidence
            (roots ! layer_idx)
            (challenges ! layer_idx)
            (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
            (2 ^ layer_idx)
            (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
            yp yp_path yn yn_path
            (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
            (fri_evidence_next_value roots challenges query_idxs round_idx'
              layer_idx yp yn)
            (round_layers ! round_idx' ! layer_idx)"
        and value_case:
          "(?raw = fri_evidence_layer_idx roots query_idxs round_idx'
              layer_idx \<and> v' = yp) \<or>
           (?raw = fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
            v' = yn)"
        by blast
      from value_case show ?thesis
      proof
        assume raw_case:
          "?raw = fri_evidence_layer_idx roots query_idxs round_idx'
              layer_idx \<and> v' = yp"
        have "xp = yp"
          by (rule generic_fri_no_same_layer_opening_conflict_left_left
              [OF generic_fri_no_assignment_conflict_no_same[OF no_conflict]
                round_bound round_bound' layer_bound step step'])
            (use raw_case in simp)
        then show ?thesis
          using raw_case by simp
      next
        assume sibling_case:
          "?raw = fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
            v' = yn"
        have "xp = yn"
          by (rule generic_fri_no_same_layer_opening_conflict_left_right
              [OF generic_fri_no_assignment_conflict_no_same[OF no_conflict]
                round_bound round_bound' layer_bound step step'])
            (use sibling_case in simp)
        then show ?thesis
          using sibling_case by simp
      qed
    qed
  qed
  have nth_raw:
    "generic_fri_sampled_assignment_layer candidate_table roots challenges
      final_value query_idxs round_layers layer_idx ! ?raw = xp"
    by (rule generic_fri_sampled_assignment_layer_nth_unique
        [OF idx_bound _ constraint unique])
      (use layer_nonzero in simp)
  show ?thesis
    using nth_raw unfolding layer_eq by simp
qed

lemma generic_fri_sampled_assignment_current_right_matches_step:
  assumes no_conflict:
    "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
    and layer_nonzero: "0 < layer_idx"
    and layer_bound: "layer_idx < length challenges"
    and round_bound: "round_idx < length query_idxs"
    and idx_bound:
      "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) <
        clength * scale"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx)"
  shows
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers ! layer_idx !
      fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) = xn"
proof -
  let ?sib =
    "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)"
  have layer_eq:
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers ! layer_idx =
     generic_fri_sampled_assignment_layer candidate_table roots challenges
      final_value query_idxs round_layers layer_idx"
    by (rule generic_fri_sampled_assignment_layers_nth)
      (use layer_bound in simp)
  have constraint:
    "generic_fri_sampled_layer_value_constraint candidate_table roots
      challenges final_value query_idxs round_layers layer_idx ?sib xn"
    by (rule generic_fri_sampled_layer_value_constraint_current_right
        [OF layer_nonzero layer_bound round_bound step])
  have unique:
    "\<And>v'. generic_fri_sampled_layer_value_constraint candidate_table roots
      challenges final_value query_idxs round_layers layer_idx ?sib v'
      \<Longrightarrow> v' = xn"
  proof -
    fix v'
    assume c:
      "generic_fri_sampled_layer_value_constraint candidate_table roots
        challenges final_value query_idxs round_layers layer_idx ?sib v'"
    have pred_or_current:
      "(\<exists>source_round.
          source_round < length query_idxs \<and>
          generic_fri_round_forced_next_value roots challenges query_idxs
            round_layers source_round (layer_idx - 1) v' \<and>
          fri_evidence_next_idx roots query_idxs source_round
            (layer_idx - 1) = ?sib) \<or>
       (\<exists>round_idx' yp yp_path yn yn_path.
          round_idx' < length query_idxs \<and>
          layer_idx < length challenges \<and>
          fri_layer_step_evidence
            (roots ! layer_idx)
            (challenges ! layer_idx)
            (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
            (2 ^ layer_idx)
            (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
            yp yp_path yn yn_path
            (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
            (fri_evidence_next_value roots challenges query_idxs round_idx'
              layer_idx yp yn)
            (round_layers ! round_idx' ! layer_idx) \<and>
          ((?sib = fri_evidence_layer_idx roots query_idxs round_idx'
              layer_idx \<and> v' = yp) \<or>
           (?sib = fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
            v' = yn)))"
      using c layer_nonzero layer_bound
      unfolding generic_fri_sampled_layer_value_constraint_def
      by auto
    then show "v' = xn"
    proof
      assume
        "\<exists>source_round.
          source_round < length query_idxs \<and>
          generic_fri_round_forced_next_value roots challenges query_idxs
            round_layers source_round (layer_idx - 1) v' \<and>
          fri_evidence_next_idx roots query_idxs source_round
            (layer_idx - 1) = ?sib"
      then obtain source_round where source_bound:
          "source_round < length query_idxs"
        and forced:
          "generic_fri_round_forced_next_value roots challenges query_idxs
            round_layers source_round (layer_idx - 1) v'"
        and same_idx:
          "fri_evidence_next_idx roots query_idxs source_round
            (layer_idx - 1) = ?sib"
        by blast
      have suc: "Suc (layer_idx - 1) = layer_idx"
        using layer_nonzero by simp
      have "v' = xn"
        using generic_fri_no_successor_opening_conflict_matches_right
          [OF generic_fri_no_assignment_conflict_no_successor[OF no_conflict]
            source_bound round_bound, of "layer_idx - 1" v'
            xp xp_path xn xn_path]
          layer_bound forced step same_idx suc by simp
      then show ?thesis .
    next
      assume
        "\<exists>round_idx' yp yp_path yn yn_path.
          round_idx' < length query_idxs \<and>
          layer_idx < length challenges \<and>
          fri_layer_step_evidence
            (roots ! layer_idx)
            (challenges ! layer_idx)
            (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
            (2 ^ layer_idx)
            (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
            yp yp_path yn yn_path
            (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
            (fri_evidence_next_value roots challenges query_idxs round_idx'
              layer_idx yp yn)
            (round_layers ! round_idx' ! layer_idx) \<and>
          ((?sib = fri_evidence_layer_idx roots query_idxs round_idx'
              layer_idx \<and> v' = yp) \<or>
           (?sib = fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
            v' = yn))"
      then obtain round_idx' yp yp_path yn yn_path where round_bound':
          "round_idx' < length query_idxs"
        and step':
          "fri_layer_step_evidence
            (roots ! layer_idx)
            (challenges ! layer_idx)
            (fri_evidence_layer_len roots layer_idx)
            (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx)
            (2 ^ layer_idx)
            (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx))
            yp yp_path yn yn_path
            (fri_evidence_next_idx roots query_idxs round_idx' layer_idx)
            (fri_evidence_next_value roots challenges query_idxs round_idx'
              layer_idx yp yn)
            (round_layers ! round_idx' ! layer_idx)"
        and value_case:
          "(?sib = fri_evidence_layer_idx roots query_idxs round_idx'
              layer_idx \<and> v' = yp) \<or>
           (?sib = fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
            v' = yn)"
        by blast
      from value_case show ?thesis
      proof
        assume raw_case:
          "?sib = fri_evidence_layer_idx roots query_idxs round_idx'
              layer_idx \<and> v' = yp"
        have "xn = yp"
          by (rule generic_fri_no_same_layer_opening_conflict_right_left
              [OF generic_fri_no_assignment_conflict_no_same[OF no_conflict]
                round_bound round_bound' layer_bound step step'])
            (use raw_case in simp)
        then show ?thesis
          using raw_case by simp
      next
        assume sibling_case:
          "?sib = fri_sibling_index (fri_evidence_layer_len roots layer_idx)
              (fri_evidence_layer_idx roots query_idxs round_idx' layer_idx) \<and>
            v' = yn"
        have "xn = yn"
          by (rule generic_fri_no_same_layer_opening_conflict_right_right
              [OF generic_fri_no_assignment_conflict_no_same[OF no_conflict]
                round_bound round_bound' layer_bound step step'])
            (use sibling_case in simp)
        then show ?thesis
          using sibling_case by simp
      qed
    qed
  qed
  have nth_sib:
    "generic_fri_sampled_assignment_layer candidate_table roots challenges
      final_value query_idxs round_layers layer_idx ! ?sib = xn"
    by (rule generic_fri_sampled_assignment_layer_nth_unique
        [OF idx_bound _ constraint unique])
      (use layer_nonzero in simp)
  show ?thesis
    using nth_sib unfolding layer_eq by simp
qed

lemma generic_fri_sampled_assignment_current_matches_step:
  assumes no_conflict:
    "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
    and layer_nonzero: "0 < layer_idx"
    and layer_bound: "layer_idx < length challenges"
    and round_bound: "round_idx < length query_idxs"
    and raw_bound:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
        fri_evidence_layer_len roots layer_idx"
    and len_bound:
      "fri_evidence_layer_len roots layer_idx \<le> clength * scale"
    and sibling_bound:
      "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) <
        clength * scale"
    and step:
      "fri_layer_step_evidence
        (roots ! layer_idx)
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_sibling_index (fri_evidence_layer_len roots layer_idx)
          (fri_evidence_layer_idx roots query_idxs round_idx layer_idx))
        xp xp_path xn xn_path
        (fri_evidence_next_idx roots query_idxs round_idx layer_idx)
        (fri_evidence_next_value roots challenges query_idxs round_idx
          layer_idx xp xn)
        (round_layers ! round_idx ! layer_idx)"
  shows
    "fri_opening_matches_table (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (generic_fri_sampled_assignment_layers candidate_table roots
        challenges final_value query_idxs round_layers ! layer_idx) xp xn"
proof -
  let ?len = "fri_evidence_layer_len roots layer_idx"
  let ?raw = "fri_evidence_layer_idx roots query_idxs round_idx layer_idx"
  let ?sib = "fri_sibling_index ?len ?raw"
  let ?layer =
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers ! layer_idx"
  have raw_bound_assignment: "?raw < clength * scale"
    using raw_bound len_bound by simp
  have layer_eq:
    "?layer =
      generic_fri_sampled_assignment_layer candidate_table roots challenges
        final_value query_idxs round_layers layer_idx"
    by (rule generic_fri_sampled_assignment_layers_nth)
      (use layer_bound in simp)
  have layer_len: "length ?layer = clength * scale"
    using layer_eq layer_nonzero by simp
  have left:
    "?layer ! ?raw = xp"
    by (rule generic_fri_sampled_assignment_current_left_matches_step
        [OF no_conflict layer_nonzero layer_bound round_bound
          raw_bound_assignment step])
  have right:
    "?layer ! ?sib = xn"
    by (rule generic_fri_sampled_assignment_current_right_matches_step
        [OF no_conflict layer_nonzero layer_bound round_bound
          sibling_bound step])
  show ?thesis
    unfolding fri_opening_matches_table_def
    using raw_bound len_bound layer_len left right by simp
qed

lemma generic_fri_sampled_assignment_successor_forced_value:
  assumes no_conflict:
    "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
    and layer_bound: "Suc layer_idx < length challenges"
    and round_bound: "round_idx < length query_idxs"
    and next_bound:
      "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        clength * scale"
    and forced:
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx layer_idx v"
  shows
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers ! Suc layer_idx !
      fri_evidence_next_idx roots query_idxs round_idx layer_idx = v"
proof -
  let ?next = "fri_evidence_next_idx roots query_idxs round_idx layer_idx"
  have suc_nonzero: "Suc layer_idx \<noteq> 0"
    by simp
  have layer_eq:
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers ! Suc layer_idx =
     generic_fri_sampled_assignment_layer candidate_table roots challenges
      final_value query_idxs round_layers (Suc layer_idx)"
    by (rule generic_fri_sampled_assignment_layers_nth)
      (use layer_bound in simp)
  have constraint:
    "generic_fri_sampled_layer_value_constraint candidate_table roots
      challenges final_value query_idxs round_layers (Suc layer_idx)
      ?next v"
    using layer_bound round_bound forced
    unfolding generic_fri_sampled_layer_value_constraint_def
    by auto
  have unique:
    "\<And>v'. generic_fri_sampled_layer_value_constraint candidate_table roots
      challenges final_value query_idxs round_layers (Suc layer_idx)
      ?next v' \<Longrightarrow> v' = v"
  proof -
    fix v'
    assume c:
      "generic_fri_sampled_layer_value_constraint candidate_table roots
        challenges final_value query_idxs round_layers (Suc layer_idx)
        ?next v'"
    have pred_or_current:
      "(\<exists>source_round.
          source_round < length query_idxs \<and>
          generic_fri_round_forced_next_value roots challenges query_idxs
            round_layers source_round layer_idx v' \<and>
          fri_evidence_next_idx roots query_idxs source_round layer_idx =
            ?next) \<or>
       (\<exists>target_round xp xp_path xn xn_path.
          target_round < length query_idxs \<and>
          Suc layer_idx < length challenges \<and>
          fri_layer_step_evidence
            (roots ! Suc layer_idx)
            (challenges ! Suc layer_idx)
            (fri_evidence_layer_len roots (Suc layer_idx))
            (fri_evidence_layer_idx roots query_idxs target_round
              (Suc layer_idx))
            (2 ^ Suc layer_idx)
            (fri_sibling_index (fri_evidence_layer_len roots (Suc layer_idx))
              (fri_evidence_layer_idx roots query_idxs target_round
                (Suc layer_idx)))
            xp xp_path xn xn_path
            (fri_evidence_next_idx roots query_idxs target_round
              (Suc layer_idx))
            (fri_evidence_next_value roots challenges query_idxs target_round
              (Suc layer_idx) xp xn)
            (round_layers ! target_round ! Suc layer_idx) \<and>
          ((?next = fri_evidence_layer_idx roots query_idxs target_round
              (Suc layer_idx) \<and> v' = xp) \<or>
           (?next = fri_sibling_index
              (fri_evidence_layer_len roots (Suc layer_idx))
              (fri_evidence_layer_idx roots query_idxs target_round
                (Suc layer_idx)) \<and>
            v' = xn)))"
      using c layer_bound
      unfolding generic_fri_sampled_layer_value_constraint_def
      by auto
    then show "v' = v"
    proof
      assume
        "\<exists>source_round.
          source_round < length query_idxs \<and>
          generic_fri_round_forced_next_value roots challenges query_idxs
            round_layers source_round layer_idx v' \<and>
          fri_evidence_next_idx roots query_idxs source_round layer_idx =
            ?next"
      then obtain source_round where source_bound:
          "source_round < length query_idxs"
        and forced':
          "generic_fri_round_forced_next_value roots challenges query_idxs
            round_layers source_round layer_idx v'"
        and same_idx:
          "fri_evidence_next_idx roots query_idxs source_round layer_idx =
            ?next"
        by blast
      have "v = v'"
      proof -
        have layer_bound0: "layer_idx < length challenges"
          using layer_bound by simp
        show ?thesis
        by (rule generic_fri_no_next_value_conflict_unique
            [OF generic_fri_no_assignment_conflict_no_next[OF no_conflict]
              round_bound source_bound layer_bound0 _ forced forced'])
          (use same_idx in simp)
      qed
      then show ?thesis by simp
    next
      assume
        "\<exists>target_round xp xp_path xn xn_path.
          target_round < length query_idxs \<and>
          Suc layer_idx < length challenges \<and>
          fri_layer_step_evidence
            (roots ! Suc layer_idx)
            (challenges ! Suc layer_idx)
            (fri_evidence_layer_len roots (Suc layer_idx))
            (fri_evidence_layer_idx roots query_idxs target_round
              (Suc layer_idx))
            (2 ^ Suc layer_idx)
            (fri_sibling_index (fri_evidence_layer_len roots (Suc layer_idx))
              (fri_evidence_layer_idx roots query_idxs target_round
                (Suc layer_idx)))
            xp xp_path xn xn_path
            (fri_evidence_next_idx roots query_idxs target_round
              (Suc layer_idx))
            (fri_evidence_next_value roots challenges query_idxs target_round
              (Suc layer_idx) xp xn)
            (round_layers ! target_round ! Suc layer_idx) \<and>
          ((?next = fri_evidence_layer_idx roots query_idxs target_round
              (Suc layer_idx) \<and> v' = xp) \<or>
           (?next = fri_sibling_index
              (fri_evidence_layer_len roots (Suc layer_idx))
              (fri_evidence_layer_idx roots query_idxs target_round
                (Suc layer_idx)) \<and>
            v' = xn))"
      then obtain target_round xp xp_path xn xn_path where target_bound:
          "target_round < length query_idxs"
        and step:
          "fri_layer_step_evidence
            (roots ! Suc layer_idx)
            (challenges ! Suc layer_idx)
            (fri_evidence_layer_len roots (Suc layer_idx))
            (fri_evidence_layer_idx roots query_idxs target_round
              (Suc layer_idx))
            (2 ^ Suc layer_idx)
            (fri_sibling_index (fri_evidence_layer_len roots (Suc layer_idx))
              (fri_evidence_layer_idx roots query_idxs target_round
                (Suc layer_idx)))
            xp xp_path xn xn_path
            (fri_evidence_next_idx roots query_idxs target_round
              (Suc layer_idx))
            (fri_evidence_next_value roots challenges query_idxs target_round
              (Suc layer_idx) xp xn)
            (round_layers ! target_round ! Suc layer_idx)"
        and value_case:
          "(?next = fri_evidence_layer_idx roots query_idxs target_round
              (Suc layer_idx) \<and> v' = xp) \<or>
           (?next = fri_sibling_index
              (fri_evidence_layer_len roots (Suc layer_idx))
              (fri_evidence_layer_idx roots query_idxs target_round
                (Suc layer_idx)) \<and>
            v' = xn)"
        by blast
      from value_case show ?thesis
      proof
        assume raw_case:
          "?next = fri_evidence_layer_idx roots query_idxs target_round
              (Suc layer_idx) \<and> v' = xp"
        have "v = xp"
          by (rule generic_fri_no_successor_opening_conflict_matches_left
              [OF generic_fri_no_assignment_conflict_no_successor
                [OF no_conflict] round_bound target_bound layer_bound
                forced step])
            (use raw_case in simp)
        then show ?thesis
          using raw_case by simp
      next
        assume sibling_case:
          "?next = fri_sibling_index
              (fri_evidence_layer_len roots (Suc layer_idx))
              (fri_evidence_layer_idx roots query_idxs target_round
                (Suc layer_idx)) \<and>
            v' = xn"
        have "v = xn"
          by (rule generic_fri_no_successor_opening_conflict_matches_right
              [OF generic_fri_no_assignment_conflict_no_successor
                [OF no_conflict] round_bound target_bound layer_bound
                forced step])
            (use sibling_case in simp)
        then show ?thesis
          using sibling_case by simp
      qed
    qed
  qed
  have nth_next:
    "generic_fri_sampled_assignment_layer candidate_table roots challenges
      final_value query_idxs round_layers (Suc layer_idx) ! ?next = v"
    by (rule generic_fri_sampled_assignment_layer_nth_unique
        [OF next_bound suc_nonzero constraint unique])
  show ?thesis
    using nth_next unfolding layer_eq by simp
qed

lemma accepted_fri_opening_transcript_query_idx_bound:
  assumes
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      query_idxs trace_round_layers composition_round_layers"
    and "idx \<in> set query_idxs"
  shows "idx < clength * scale"
  using assms
  unfolding accepted_fri_opening_transcript_def by blast

lemma trace_fri_partial_candidate_opening_evidence_query_idx_bound:
  assumes
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table"
    and "idx \<in> set fri_query_idxs"
  shows "idx < clength * scale"
proof -
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    by (rule trace_fri_partial_candidate_opening_evidenceD(1)[OF assms(1)])
  show ?thesis
    by (rule accepted_fri_opening_transcript_query_idx_bound
        [OF fri_openings assms(2)])
qed

lemma composition_fri_partial_candidate_opening_evidence_query_idx_bound:
  assumes
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
    and "idx \<in> set fri_query_idxs"
  shows "idx < clength * scale"
proof -
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    by (rule composition_fri_partial_candidate_opening_evidenceD(1)
        [OF assms(1)])
  show ?thesis
    by (rule accepted_fri_opening_transcript_query_idx_bound
        [OF fri_openings assms(2)])
qed

lemma fri_layer_indices_nth_bound:
  assumes query_bound: "query_idx < len"
    and layer_bound: "layer_idx < n"
    and eval_power: "len = 2 ^ N"
    and rounds_bound: "n \<le> N"
  shows
    "fri_layer_indices n query_idx len ! layer_idx <
      fri_layer_lengths n len ! layer_idx"
  using layer_bound query_bound rounds_bound eval_power
proof (induction layer_idx arbitrary: n query_idx len N)
  case 0
  then show ?case
    by (cases n) simp_all
next
  case (Suc layer_idx)
  then obtain n' where n_eq: "n = Suc n'"
    by (cases n) auto
  have layer_bound': "layer_idx < n'"
    using Suc.prems(1) unfolding n_eq by simp
  have len_even: "2 dvd len"
    using Suc.prems(3,4) n_eq Suc.prems(1)
    by (cases N) simp_all
  have len_half_power:
    "\<exists>N'. len div 2 = 2 ^ N' \<and> n' \<le> N'"
  proof (cases N)
    case 0
    then show ?thesis
      using Suc.prems(3) n_eq by simp
  next
    case (Suc N')
    have "len div 2 = 2 ^ N'"
      using Suc.prems(4) unfolding Suc by simp
    moreover have "n' \<le> N'"
      using Suc.prems(3) unfolding n_eq Suc by simp
    ultimately show ?thesis by blast
  qed
  then obtain N' where len_half_eq: "len div 2 = 2 ^ N'"
    and rounds_bound': "n' \<le> N'"
    by blast
  have query_bound':
    "query_idx mod (len div 2) < len div 2"
    using len_half_eq by simp
  have ih:
    "fri_layer_indices n' (query_idx mod (len div 2)) (len div 2) !
        layer_idx <
      fri_layer_lengths n' (len div 2) ! layer_idx"
    by (rule Suc.IH[OF layer_bound' query_bound' rounds_bound'
          len_half_eq])
  show ?case
    using ih unfolding n_eq by simp
qed

lemma fri_evidence_layer_idx_bound_from_query_bound:
  assumes partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    and query_bound: "query_idx < clength * scale"
    and round_idx_eq: "query_idx = query_idxs ! round_idx"
    and layer_bound: "layer_idx < length challenges"
    and eval_power: "clength * scale = 2 ^ N"
    and rounds_bound: "length challenges \<le> N"
  shows
    "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
      fri_evidence_layer_len roots layer_idx"
proof -
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  show ?thesis
    unfolding fri_evidence_layer_idx_def fri_evidence_layer_len_def
    using fri_layer_indices_nth_bound
      [OF query_bound, of layer_idx "length roots" N]
      layer_bound roots_len eval_power rounds_bound round_idx_eq
    by simp
qed

lemma fri_evidence_layer_len_le_eval_domain:
  assumes partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    and layer_bound: "layer_idx < length challenges"
    and eval_power: "clength * scale = 2 ^ N"
  shows "fri_evidence_layer_len roots layer_idx \<le> clength * scale"
proof -
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have roots_bound: "layer_idx < length roots"
    using layer_bound roots_len by simp
  have len_eq:
    "fri_evidence_layer_len roots layer_idx =
      (clength * scale) div 2 ^ layer_idx"
    unfolding fri_evidence_layer_len_def
    by (rule fri_layer_lengths_nth_div[OF roots_bound])
  show ?thesis
    unfolding len_eq by simp
qed

lemma fri_evidence_sibling_index_bound_from_raw:
  assumes raw_bound:
    "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
      fri_evidence_layer_len roots layer_idx"
    and len_bound:
      "fri_evidence_layer_len roots layer_idx \<le> clength * scale"
  shows
    "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) <
      clength * scale"
proof -
  have len_pos: "0 < fri_evidence_layer_len roots layer_idx"
    using raw_bound by simp
  have sibling_lt:
    "fri_sibling_index (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx) <
      fri_evidence_layer_len roots layer_idx"
    unfolding fri_sibling_index_def
    using len_pos by simp
  then show ?thesis
    using len_bound by linarith
qed

lemma fri_evidence_next_idx_bound_from_raw:
  assumes raw_bound:
    "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
      fri_evidence_layer_len roots layer_idx"
    and len_bound:
      "fri_evidence_layer_len roots layer_idx \<le> clength * scale"
  shows
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      clength * scale"
proof -
  have len_pos: "0 < fri_evidence_layer_len roots layer_idx"
    using raw_bound by simp
  have half_le: "fri_evidence_layer_len roots layer_idx div 2 \<le>
      clength * scale"
    using len_bound by simp
  show ?thesis
  proof (cases "fri_evidence_layer_len roots layer_idx div 2 = 0")
    case True
    then show ?thesis
      unfolding fri_evidence_next_idx_def
      using raw_bound len_bound by simp
  next
    case False
    then have half_pos:
      "0 < fri_evidence_layer_len roots layer_idx div 2"
      by simp
    have mod_lt:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx mod
        (fri_evidence_layer_len roots layer_idx div 2) <
        fri_evidence_layer_len roots layer_idx div 2"
      by (rule mod_less_divisor[OF half_pos])
    then show ?thesis
      unfolding fri_evidence_next_idx_def
      using half_le by linarith
  qed
qed

lemma trace_fri_reachable_missing_sampled_layer_chain_None[simp]:
  "\<not> trace_fri_reachable_missing_sampled_layer_chain s None"
  unfolding trace_fri_reachable_missing_sampled_layer_chain_def
    trace_fri_bad_with_reachable_partial_candidate_def
    accepted_with_partial_trace_openings_def
  by simp

lemma composition_fri_reachable_missing_sampled_layer_chain_None[simp]:
  "\<not> composition_fri_reachable_missing_sampled_layer_chain s None"
  unfolding composition_fri_reachable_missing_sampled_layer_chain_def
    composition_fri_bad_with_reachable_partial_candidate_def
    accepted_with_partial_initial_openings_def
    accepted_with_partial_trace_openings_def
  by simp

lemma trace_fri_sampled_layer_assignment_obstruction_None[simp]:
  "\<not> trace_fri_sampled_layer_assignment_obstruction s None"
  unfolding trace_fri_sampled_layer_assignment_obstruction_def
    trace_fri_partial_candidate_opening_evidence_def
    accepted_fri_opening_transcript_def
  by simp

lemma composition_fri_sampled_layer_assignment_obstruction_None[simp]:
  "\<not> composition_fri_sampled_layer_assignment_obstruction s None"
  unfolding composition_fri_sampled_layer_assignment_obstruction_def
    composition_fri_partial_candidate_opening_evidence_def
    accepted_fri_opening_transcript_def
  by simp

lemma trace_fri_sampled_assignment_conflict_None[simp]:
  "\<not> trace_fri_sampled_assignment_conflict s None"
  unfolding trace_fri_sampled_assignment_conflict_def
    trace_fri_partial_candidate_opening_evidence_def
    accepted_fri_opening_transcript_def
  by simp

lemma composition_fri_sampled_assignment_conflict_None[simp]:
  "\<not> composition_fri_sampled_assignment_conflict s None"
  unfolding composition_fri_sampled_assignment_conflict_def
    composition_fri_partial_candidate_opening_evidence_def
    accepted_fri_opening_transcript_def
  by simp

lemma wp_trace_fri_assignment_obstruction_bound_from_conflict:
  assumes support_imp:
    "\<And>out. out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
      trace_fri_sampled_layer_assignment_obstruction s out \<Longrightarrow>
      trace_fri_sampled_assignment_conflict s out"
    and conflict_bound:
      "wp_event verify_monad (trace_fri_sampled_assignment_conflict s) s
        \<le> C"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction s) s \<le> C"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction s) s \<le>
    wp_event verify_monad (trace_fri_sampled_assignment_conflict s) s"
    by (rule wp_event_mono_on_support) (use support_imp in blast)
  also have "... \<le> C"
    by (rule conflict_bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_assignment_obstruction_bound_from_conflict:
  assumes support_imp:
    "\<And>out. out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
      composition_fri_sampled_layer_assignment_obstruction s out \<Longrightarrow>
      composition_fri_sampled_assignment_conflict s out"
    and conflict_bound:
      "wp_event verify_monad
        (composition_fri_sampled_assignment_conflict s) s \<le> C"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_layer_assignment_obstruction s) s \<le> C"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_layer_assignment_obstruction s) s \<le>
    wp_event verify_monad
      (composition_fri_sampled_assignment_conflict s) s"
    by (rule wp_event_mono_on_support) (use support_imp in blast)
  also have "... \<le> C"
    by (rule conflict_bound)
  finally show ?thesis .
qed

lemma trace_fri_reachable_missing_sampled_imp_assignment_obstruction_on_support:
  assumes support:
    "out \<in> set_dist (execute verify_monad s)"
    and missing:
    "trace_fri_reachable_missing_sampled_layer_chain s out"
  shows "trace_fri_sampled_layer_assignment_obstruction s out"
proof (cases out)
  case None
  then show ?thesis
    using missing
    unfolding trace_fri_reachable_missing_sampled_layer_chain_def
      trace_fri_bad_with_reachable_partial_candidate_def
      accepted_with_partial_trace_openings_def
    by simp
next
  case (Some pair)
  then obtain result final_state where pair: "pair = (result, final_state)"
    by (cases pair) simp
  have outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using support Some pair by simp
  show ?thesis
  proof (rule verify_monad_trace_fri_missing_sampled_extracts_opening_evidence
      [OF outcome])
    show
      "trace_fri_reachable_missing_sampled_layer_chain s
        (Some (result, final_state))"
      using missing Some pair by simp
  next
    fix trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
    assume evidence:
      "trace_fri_partial_candidate_opening_evidence s
        (Some (result, final_state)) trace_roots trace_bs trace_final dg
        composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers fr candidate_query_idxs
        trace_openings trace_table"
    assume no_chain:
      "\<And>doms layers. \<not>
        generic_fri_sampled_layer_chain_evidence trace_table_low_degree
          trace_table (clength - 1) trace_roots trace_bs trace_final
          fri_query_idxs trace_round_layers doms layers"
    have partial:
      "generic_fri_partial_evidence trace_table_low_degree trace_table
        (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
        trace_round_layers"
      by (rule trace_fri_partial_candidate_opening_evidence_generic_partial
          [OF evidence])
    have obstruction:
      "generic_fri_sampled_layer_assignment_obstruction
        trace_table_low_degree trace_table (clength - 1) trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers"
      unfolding generic_fri_sampled_layer_assignment_obstruction_def
      using partial no_chain by blast
    show "trace_fri_sampled_layer_assignment_obstruction s out"
      unfolding trace_fri_sampled_layer_assignment_obstruction_def
      using evidence obstruction Some pair by blast
  qed
qed

lemma composition_fri_reachable_missing_sampled_imp_assignment_obstruction_on_support:
  assumes support:
    "out \<in> set_dist (execute verify_monad s)"
    and missing:
    "composition_fri_reachable_missing_sampled_layer_chain s out"
  shows "composition_fri_sampled_layer_assignment_obstruction s out"
proof (cases out)
  case None
  then show ?thesis
    unfolding composition_fri_sampled_layer_assignment_obstruction_def
    using missing
    unfolding composition_fri_reachable_missing_sampled_layer_chain_def
      composition_fri_bad_with_reachable_partial_candidate_def
      accepted_with_partial_initial_openings_def
      accepted_with_partial_trace_openings_def
    by simp
next
  case (Some pair)
  then obtain result final_state where pair: "pair = (result, final_state)"
    by (cases pair) simp
  have outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using support Some pair by simp
  show ?thesis
  proof (rule
      verify_monad_composition_fri_missing_sampled_extracts_opening_evidence
        [OF outcome])
    show
      "composition_fri_reachable_missing_sampled_layer_chain s
        (Some (result, final_state))"
      using missing Some pair by simp
  next
    fix trace_roots trace_bs trace_final fri_dg opening_composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table
    assume evidence:
      "composition_fri_partial_candidate_opening_evidence s
        (Some (result, final_state)) trace_roots trace_bs trace_final
        fri_dg opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table"
    assume degree_bound: "to_nat fri_dg \<le> maxDegree"
    assume no_chain:
      "\<And>doms layers. \<not>
        generic_fri_sampled_layer_chain_evidence
          (composition_table_low_degree (to_nat fri_dg))
          composition_table (to_nat fri_dg) opening_composition_roots
          composition_bs composition_final fri_query_idxs
          composition_round_layers doms layers"
    have partial:
      "generic_fri_partial_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers"
      by (rule composition_fri_partial_candidate_opening_evidence_generic_partial
          [OF evidence])
    have obstruction:
      "generic_fri_sampled_layer_assignment_obstruction
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers"
      unfolding generic_fri_sampled_layer_assignment_obstruction_def
      using partial no_chain by blast
    show "composition_fri_sampled_layer_assignment_obstruction s out"
      unfolding composition_fri_sampled_layer_assignment_obstruction_def
      using evidence obstruction Some pair degree_bound by meson
  qed
qed

lemma wp_trace_fri_reachable_missing_sampled_bound_from_assignment_obstruction:
  assumes obstruction:
    "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction s) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain s) s \<le> M"
proof -
  have "wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain s) s
    \<le> wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction s) s"
    by (rule wp_event_mono_on_support)
      (rule trace_fri_reachable_missing_sampled_imp_assignment_obstruction_on_support)
  also have "... \<le> M"
    by (rule obstruction)
  finally show ?thesis .
qed

lemma wp_composition_fri_reachable_missing_sampled_bound_from_assignment_obstruction:
  assumes obstruction:
    "wp_event verify_monad
      (composition_fri_sampled_layer_assignment_obstruction s) s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_reachable_missing_sampled_layer_chain s) s \<le> M"
proof -
  have "wp_event verify_monad
      (composition_fri_reachable_missing_sampled_layer_chain s) s
    \<le> wp_event verify_monad
      (composition_fri_sampled_layer_assignment_obstruction s) s"
    by (rule wp_event_mono_on_support)
      (rule composition_fri_reachable_missing_sampled_imp_assignment_obstruction_on_support)
  also have "... \<le> M"
    by (rule obstruction)
  finally show ?thesis .
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_sampled_and_assignment_obstruction:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> R"
    and obstruction_bound:
    "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction s) s \<le> M"
    and total_bound: "R + M \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof (rule trace_fri_reachable_partial_candidate_reduction_from_sampled_and_missing)
  show "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> R"
    by (rule sampled_bound)
next
  show "wp_event verify_monad
      (trace_fri_reachable_missing_sampled_layer_chain s) s \<le> M"
    by (rule wp_trace_fri_reachable_missing_sampled_bound_from_assignment_obstruction
        [OF obstruction_bound])
next
  show "R + M \<le> trace_fri_error"
    by (rule total_bound)
qed

lemma composition_fri_reachable_partial_candidate_reduction_from_sampled_and_assignment_obstruction:
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le> R"
    and obstruction_bound:
    "wp_event verify_monad
      (composition_fri_sampled_layer_assignment_obstruction s) s \<le> M"
    and total_bound: "R + M \<le> composition_fri_error"
  shows "composition_fri_reachable_partial_candidate_reduction_assumption s"
proof (rule
    composition_fri_reachable_partial_candidate_reduction_from_sampled_and_missing)
  show "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le> R"
    by (rule sampled_bound)
next
  show "wp_event verify_monad
      (composition_fri_reachable_missing_sampled_layer_chain s) s \<le> M"
    by (rule
        wp_composition_fri_reachable_missing_sampled_bound_from_assignment_obstruction
          [OF obstruction_bound])
next
  show "R + M \<le> composition_fri_error"
    by (rule total_bound)
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_sampled_and_assignment_conflict:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> R"
    and support_imp:
      "\<And>out. out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
        trace_fri_sampled_layer_assignment_obstruction s out \<Longrightarrow>
        trace_fri_sampled_assignment_conflict s out"
    and conflict_bound:
      "wp_event verify_monad
        (trace_fri_sampled_assignment_conflict s) s \<le> M"
    and total_bound: "R + M \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof (rule
    trace_fri_reachable_partial_candidate_reduction_from_sampled_and_assignment_obstruction)
  show "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain s) s \<le> R"
    by (rule sampled_bound)
next
  show "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction s) s \<le> M"
    by (rule wp_trace_fri_assignment_obstruction_bound_from_conflict
        [OF support_imp conflict_bound])
next
  show "R + M \<le> trace_fri_error"
    by (rule total_bound)
qed

lemma composition_fri_reachable_partial_candidate_reduction_from_sampled_and_assignment_conflict:
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le> R"
    and support_imp:
      "\<And>out. out \<in> set_dist (execute verify_monad s) \<Longrightarrow>
        composition_fri_sampled_layer_assignment_obstruction s out \<Longrightarrow>
        composition_fri_sampled_assignment_conflict s out"
    and conflict_bound:
      "wp_event verify_monad
        (composition_fri_sampled_assignment_conflict s) s \<le> M"
    and total_bound: "R + M \<le> composition_fri_error"
  shows "composition_fri_reachable_partial_candidate_reduction_assumption s"
proof (rule
    composition_fri_reachable_partial_candidate_reduction_from_sampled_and_assignment_obstruction)
  show "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le> R"
    by (rule sampled_bound)
next
  show "wp_event verify_monad
      (composition_fri_sampled_layer_assignment_obstruction s) s \<le> M"
    by (rule wp_composition_fri_assignment_obstruction_bound_from_conflict
        [OF support_imp conflict_bound])
next
  show "R + M \<le> composition_fri_error"
    by (rule total_bound)
qed

lemma trace_fri_bad_with_partial_candidates_bound_from_sampled_and_assignment_obstruction:
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
    and obstruction_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_layer_assignment_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> R + M"
proof (rule trace_fri_bad_with_partial_candidates_bound_from_sampled_and_missing)
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le> R"
    by (rule sampled_bound[OF builder])
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
        (staged_proof_transcript data)) \<le> M"
    by (rule
        wp_trace_fri_reachable_missing_sampled_bound_from_assignment_obstruction)
      (rule obstruction_bound[OF builder])
qed

lemma composition_fri_bad_with_partial_candidates_bound_from_sampled_and_assignment_obstruction:
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
    and obstruction_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_layer_assignment_obstruction
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> R + M"
proof (rule
    composition_fri_bad_with_partial_candidates_bound_from_sampled_and_missing)
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le> R"
    by (rule sampled_bound[OF builder])
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
        (staged_proof_transcript data)) \<le> M"
    by (rule
        wp_composition_fri_reachable_missing_sampled_bound_from_assignment_obstruction)
      (rule obstruction_bound[OF builder])
qed

lemma trace_fri_bad_with_partial_candidates_bound_from_sampled_and_assignment_conflict:
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
    and support_imp:
    "\<And>data attacker_state out.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      out \<in> set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))) \<Longrightarrow>
      trace_fri_sampled_layer_assignment_obstruction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) out \<Longrightarrow>
      trace_fri_sampled_assignment_conflict
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) out"
    and conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> R + M"
proof (rule
    trace_fri_bad_with_partial_candidates_bound_from_sampled_and_assignment_obstruction)
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (trace_fri_bad_with_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le> R"
    by (rule sampled_bound[OF builder])
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (trace_fri_sampled_layer_assignment_obstruction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le> M"
    by (rule wp_trace_fri_assignment_obstruction_bound_from_conflict)
      (use builder support_imp conflict_bound in blast)+
qed

lemma composition_fri_bad_with_partial_candidates_bound_from_sampled_and_assignment_conflict:
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
    and support_imp:
    "\<And>data attacker_state out.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      out \<in> set_dist
        (execute verify_monad
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data))) \<Longrightarrow>
      composition_fri_sampled_layer_assignment_obstruction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) out \<Longrightarrow>
      composition_fri_sampled_assignment_conflict
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) out"
    and conflict_bound:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_assignment_conflict
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> M"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_partial_candidates)
      adversary_initial_state \<le> R + M"
proof (rule
    composition_fri_bad_with_partial_candidates_bound_from_sampled_and_assignment_obstruction)
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le> R"
    by (rule sampled_bound[OF builder])
next
  fix data attacker_state
  assume builder:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  show "wp_event verify_monad
      (composition_fri_sampled_layer_assignment_obstruction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)))
      (verifier_state_from_adversary attacker_state
        (staged_proof_transcript data)) \<le> M"
    by (rule wp_composition_fri_assignment_obstruction_bound_from_conflict)
      (use builder support_imp conflict_bound in blast)+
qed

end

end
