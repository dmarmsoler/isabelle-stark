(*  Title:      Stark/Soundness_FRI_Sampled_Assignment_Chain.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Sampled_Assignment_Chain
  imports Soundness_FRI_Sampled_Obstructions
begin

text \<open>
  Construction of sampled FRI layer-chain witnesses from verifier-local
  sampled assignment layers.  This theory is kept separate from the sampled
  obstruction-routing layer to keep that layer below the project size
  threshold.
\<close>

context soundness
begin

lemma ceil_log_le_power:
  assumes le_power: "m \<le> (2::nat) ^ N"
  shows "ceil_log m \<le> N"
proof (cases "m \<le> 1")
  case True
  then show ?thesis
    unfolding ceil_log_def by simp
next
  case False
  then have m_gt: "1 < m"
    by simp
  then have m_pred_pos: "0 < m - 1"
    by simp
  have m_pred_lt: "m - 1 < (2::nat) ^ N"
    using le_power m_gt by linarith
  have floor_less: "floor_log (m - 1) < N"
  proof (rule ccontr)
    assume "\<not> floor_log (m - 1) < N"
    then have N_le: "N \<le> floor_log (m - 1)"
      by simp
    then have "(2::nat) ^ N \<le> 2 ^ floor_log (m - 1)"
      by simp
    also have "... \<le> m - 1"
      by (rule floor_log_exp2_le[OF m_pred_pos])
    finally show False
      using m_pred_lt by simp
  qed
  then show ?thesis
    unfolding ceil_log_def using m_gt by simp
qed

lemma generic_fri_sampled_assignment_fold_at_step:
  assumes partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    and no_conflict:
      "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
        challenges final_value query_idxs round_layers"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
    and raw_bound:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
        fri_evidence_layer_len roots layer_idx"
    and len_bound:
      "fri_evidence_layer_len roots layer_idx \<le> clength * scale"
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
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      length (generic_fri_sampled_assignment_layers candidate_table roots
        challenges final_value query_idxs round_layers ! Suc layer_idx)"
    "fri_sampled_table_fold
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (fri_canonical_domains (length challenges) ! layer_idx)
      (generic_fri_sampled_assignment_layers candidate_table roots
        challenges final_value query_idxs round_layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      (generic_fri_sampled_assignment_layers candidate_table roots
        challenges final_value query_idxs round_layers ! Suc layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
proof -
  let ?layers =
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers"
  let ?len = "fri_evidence_layer_len roots layer_idx"
  let ?raw = "fri_evidence_layer_idx roots query_idxs round_idx layer_idx"
  let ?next = "fri_evidence_next_idx roots query_idxs round_idx layer_idx"
  let ?next_value =
    "fri_evidence_next_value roots challenges query_idxs round_idx layer_idx
      xp xn"
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have sibling_bound:
    "fri_sibling_index ?len ?raw < clength * scale"
    by (rule fri_evidence_sibling_index_bound_from_raw
        [OF raw_bound len_bound])
  have next_bound: "?next < clength * scale"
    by (rule fri_evidence_next_idx_bound_from_raw[OF raw_bound len_bound])
  have layer_next_len:
    "length (?layers ! Suc layer_idx) = clength * scale"
  proof -
    have "Suc layer_idx \<le> length challenges"
      using layer_bound by simp
    then have "?layers ! Suc layer_idx =
      generic_fri_sampled_assignment_layer candidate_table roots challenges
        final_value query_idxs round_layers (Suc layer_idx)"
      by (rule generic_fri_sampled_assignment_layers_nth)
    then show ?thesis by simp
  qed
  then show next_bound_layer:
    "?next < length (?layers ! Suc layer_idx)"
    using next_bound by simp
  have current_match:
    "fri_opening_matches_table ?len ?raw (?layers ! layer_idx) xp xn"
  proof (cases "layer_idx = 0")
    case True
    have challenges_nonempty: "0 < length challenges"
      using layer_bound by (cases challenges) auto
    have base_match:
      "fri_opening_matches_table (fri_evidence_layer_len roots 0)
        (fri_evidence_layer_idx roots query_idxs round_idx 0)
        (?layers ! 0) xp xn"
      by (rule generic_fri_sampled_assignment_base_matches_step
          [OF no_conflict challenges_nonempty round_bound])
        (use step True in simp)
    show ?thesis
      using base_match True by simp
  next
    case False
    then have layer_nonzero: "0 < layer_idx"
      by simp
    show ?thesis
      by (rule generic_fri_sampled_assignment_current_matches_step
          [OF no_conflict layer_nonzero layer_bound round_bound raw_bound
            len_bound sibling_bound step])
  qed
  have forced:
    "generic_fri_round_forced_next_value roots challenges query_idxs
      round_layers round_idx layer_idx ?next_value"
    unfolding generic_fri_round_forced_next_value_def
    using step by blast
  have next_value:
    "?layers ! Suc layer_idx ! ?next = ?next_value"
  proof (cases "Suc layer_idx < length challenges")
    case True
    show ?thesis
      by (rule generic_fri_sampled_assignment_successor_forced_value
          [OF no_conflict True round_bound next_bound forced])
  next
    case False
    have suc_eq: "Suc layer_idx = length challenges"
      using False layer_bound by simp
    have challenges_nonempty: "0 < length challenges"
      using layer_bound by (cases challenges) auto
    have layer_eq: "layer_idx = length challenges - 1"
      using suc_eq by simp
    have forced_last:
      "generic_fri_round_forced_next_value roots challenges query_idxs
        round_layers round_idx (length challenges - 1) ?next_value"
      using forced layer_eq by simp
    have next_bound_last:
      "fri_evidence_next_idx roots query_idxs round_idx
        (length challenges - 1) < clength * scale"
      using next_bound layer_eq by simp
    have final_next:
      "?layers ! length challenges !
        fri_evidence_next_idx roots query_idxs round_idx
          (length challenges - 1) = ?next_value"
      apply (rule generic_fri_sampled_final_layer_forced_value)
      using no_conflict challenges_nonempty round_bound next_bound_last forced_last
      by simp_all
    show ?thesis
      using final_next layer_eq suc_eq by simp
  qed
  have chunk:
    "fri_layer_opening_chunk ?len xp xp_path xn xn_path
      (round_layers ! round_idx ! layer_idx)"
    by (rule fri_layer_step_evidenceD(4)[OF step])
  have canonical_layer:
    "fri_canonical_domains (length challenges) ! layer_idx =
      fri_canonical_domain_at layer_idx"
    by (rule fri_canonical_domains_nth) (use layer_bound in simp)
  have canonical_len:
    "length (fri_canonical_domain_at layer_idx) = ?len"
    unfolding fri_canonical_domain_at_length fri_evidence_layer_len_def
    using roots_len fri_layer_lengths_nth_div
      [of layer_idx "length roots" "clength * scale"] layer_bound
    by simp
  have dom_raw:
    "fri_canonical_domains (length challenges) ! layer_idx ! ?raw =
      (h ^ ?raw * shift) ^ (2 ^ layer_idx)"
    unfolding canonical_layer
    by (rule fri_canonical_domain_at_nth)
      (use raw_bound canonical_len in simp)
  have fold:
    "fri_sampled_table_fold
      (challenges ! layer_idx) ?len ?raw (2 ^ layer_idx)
      (fri_canonical_domains (length challenges) ! layer_idx)
      (?layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      ?next_value"
    by (rule fri_layer_step_evidence_sampled_table_fold_if_matching_chunk
        [OF step dom_raw chunk current_match])
  then show
    "fri_sampled_table_fold
      (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (fri_canonical_domains (length challenges) ! layer_idx)
      (?layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      (?layers ! Suc layer_idx ! ?next)"
    using next_value by simp
qed

lemma generic_fri_sampled_assignment_layer_chain_evidence:
  assumes partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    and no_conflict:
      "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
        challenges final_value query_idxs round_layers"
    and challenges_nonempty: "0 < length challenges"
    and query_bounds:
      "\<And>round_idx. round_idx < length query_idxs \<Longrightarrow>
        query_idxs ! round_idx < clength * scale"
    and eval_power: "clength * scale = 2 ^ N"
    and rounds_bound: "length challenges \<le> N"
  shows
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges))
      (generic_fri_sampled_assignment_layers candidate_table roots
        challenges final_value query_idxs round_layers)"
proof -
  let ?doms = "fri_canonical_domains (length challenges)"
  let ?layers =
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers"
  have doms_len: "length ?doms = Suc (length challenges)"
    by (rule fri_canonical_domains_length)
  have layers_len: "length ?layers = Suc (length challenges)"
    by (rule generic_fri_sampled_assignment_layers_length)
  have doms0: "?doms ! 0 = eval_domain"
    by (rule fri_canonical_domains_first)
  have layers0: "?layers ! 0 = candidate_table"
    by simp
  have final:
    "fri_final_constant_consistent (?layers ! length challenges)
      final_value"
    by (rule generic_fri_sampled_final_assignment_layer_consistent
        [OF challenges_nonempty])
  have samples:
    "\<And>round_idx layer_idx.
      round_idx < length query_idxs \<Longrightarrow>
      layer_idx < length challenges \<Longrightarrow>
      fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        length (?layers ! Suc layer_idx) \<and>
      fri_sampled_table_fold
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (?doms ! layer_idx)
        (?layers ! layer_idx)
        (round_layers ! round_idx ! layer_idx)
        (?layers ! Suc layer_idx !
          fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
  proof -
    fix round_idx layer_idx
    assume round_bound: "round_idx < length query_idxs"
      and layer_bound: "layer_idx < length challenges"
    have roots_len: "length challenges = length roots"
      by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
    have all_layers:
      "fri_all_round_layer_evidence roots challenges query_idxs round_layers"
      by (rule generic_fri_partial_evidence_shapes(3)[OF partial])
    have layer_root_bound: "layer_idx < length roots"
      using layer_bound roots_len by simp
    have round_layer:
      "fri_round_layer_evidence roots challenges query_idxs round_idx
        layer_idx round_layers"
      by (rule fri_all_round_layer_evidenceD
          [OF all_layers round_bound layer_root_bound])
    then obtain xp xp_path xn xn_path where step:
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
      by (elim fri_round_layer_evidence_compactE)
    have raw_bound:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
        fri_evidence_layer_len roots layer_idx"
      by (rule fri_evidence_layer_idx_bound_from_query_bound
          [OF partial query_bounds[OF round_bound] refl layer_bound
            eval_power rounds_bound])
    have len_bound:
      "fri_evidence_layer_len roots layer_idx \<le> clength * scale"
      by (rule fri_evidence_layer_len_le_eval_domain
          [OF partial layer_bound eval_power])
    show
      "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        length (?layers ! Suc layer_idx) \<and>
      fri_sampled_table_fold
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (?doms ! layer_idx)
        (?layers ! layer_idx)
        (round_layers ! round_idx ! layer_idx)
        (?layers ! Suc layer_idx !
          fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
      by (rule conjI)
        (rule generic_fri_sampled_assignment_fold_at_step
          [OF partial no_conflict round_bound layer_bound raw_bound
            len_bound step])+
  qed
  show ?thesis
    unfolding generic_fri_sampled_layer_chain_evidence_def
    using partial doms_len layers_len doms0 layers0 final samples
    by blast
qed

lemma generic_fri_sampled_assignment_layer_chain_evidence_zero_round:
  assumes partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    and challenges_empty: "length challenges = 0"
    and final:
      "fri_final_constant_consistent candidate_table final_value"
  shows
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges))
      (generic_fri_sampled_assignment_layers candidate_table roots
        challenges final_value query_idxs round_layers)"
proof -
  let ?doms = "fri_canonical_domains (length challenges)"
  let ?layers =
    "generic_fri_sampled_assignment_layers candidate_table roots challenges
      final_value query_idxs round_layers"
  have doms_len: "length ?doms = Suc (length challenges)"
    by (rule fri_canonical_domains_length)
  have layers_len: "length ?layers = Suc (length challenges)"
    by (rule generic_fri_sampled_assignment_layers_length)
  have doms0: "?doms ! 0 = eval_domain"
    by (rule fri_canonical_domains_first)
  have layers0: "?layers ! 0 = candidate_table"
    by simp
  have final_layer:
    "fri_final_constant_consistent (?layers ! length challenges)
      final_value"
    using challenges_empty final by simp
  have samples:
    "\<And>round_idx layer_idx.
      round_idx < length query_idxs \<Longrightarrow>
      layer_idx < length challenges \<Longrightarrow>
      fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        length (?layers ! Suc layer_idx) \<and>
      fri_sampled_table_fold
        (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (?doms ! layer_idx)
        (?layers ! layer_idx)
        (round_layers ! round_idx ! layer_idx)
        (?layers ! Suc layer_idx !
          fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
    using challenges_empty by simp
  show ?thesis
    unfolding generic_fri_sampled_layer_chain_evidence_def
    using partial doms_len layers_len doms0 layers0 final_layer samples
    by blast
qed

lemma generic_fri_sampled_layer_assignment_obstruction_imp_conflict:
  assumes obstruction:
    "generic_fri_sampled_layer_assignment_obstruction low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers"
    and challenges_nonempty: "0 < length challenges"
    and query_bounds:
      "\<And>round_idx. round_idx < length query_idxs \<Longrightarrow>
        query_idxs ! round_idx < clength * scale"
    and eval_power: "clength * scale = 2 ^ N"
    and rounds_bound: "length challenges \<le> N"
  shows
    "generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
proof (rule ccontr)
  assume no_conflict:
    "\<not> generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers"
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_assignment_obstructionD(1)
        [OF obstruction])
  have no_chain:
    "\<And>doms layers. \<not>
      generic_fri_sampled_layer_chain_evidence low_degree candidate_table
        degree_bound roots challenges final_value query_idxs round_layers
        doms layers"
    by (rule generic_fri_sampled_layer_assignment_obstructionD(2)
        [OF obstruction])
  have chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges))
      (generic_fri_sampled_assignment_layers candidate_table roots
        challenges final_value query_idxs round_layers)"
    by (rule generic_fri_sampled_assignment_layer_chain_evidence
        [OF partial no_conflict challenges_nonempty query_bounds
          eval_power rounds_bound])
  show False
    using no_chain[of "fri_canonical_domains (length challenges)"
        "generic_fri_sampled_assignment_layers candidate_table roots
          challenges final_value query_idxs round_layers"] chain
    by blast
qed

lemma generic_fri_sampled_layer_assignment_obstruction_imp_conflict_or_zero_round_final:
  assumes obstruction:
    "generic_fri_sampled_layer_assignment_obstruction low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers"
    and query_bounds:
      "\<And>round_idx. round_idx < length query_idxs \<Longrightarrow>
        query_idxs ! round_idx < clength * scale"
    and eval_power: "clength * scale = 2 ^ N"
    and rounds_bound: "length challenges \<le> N"
  shows
    "generic_fri_sampled_assignment_conflict candidate_table roots
      challenges final_value query_idxs round_layers \<or>
     length challenges = 0 \<and>
      \<not> fri_final_constant_consistent candidate_table final_value"
proof (cases "0 < length challenges")
  case True
  then show ?thesis
    by (intro disjI1
        generic_fri_sampled_layer_assignment_obstruction_imp_conflict
          [OF obstruction _ query_bounds eval_power rounds_bound])
next
  case False
  then have challenges_empty: "length challenges = 0"
    by simp
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_assignment_obstructionD(1)
        [OF obstruction])
  have no_chain:
    "\<And>doms layers. \<not>
      generic_fri_sampled_layer_chain_evidence low_degree candidate_table
        degree_bound roots challenges final_value query_idxs round_layers
        doms layers"
    by (rule generic_fri_sampled_layer_assignment_obstructionD(2)
        [OF obstruction])
  show ?thesis
  proof (cases "fri_final_constant_consistent candidate_table final_value")
    case True
    have chain:
      "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
        degree_bound roots challenges final_value query_idxs round_layers
        (fri_canonical_domains (length challenges))
        (generic_fri_sampled_assignment_layers candidate_table roots
          challenges final_value query_idxs round_layers)"
      by (rule generic_fri_sampled_assignment_layer_chain_evidence_zero_round
          [OF partial challenges_empty True])
    then show ?thesis
      using no_chain by blast
  next
    case False
    then show ?thesis
      using challenges_empty by blast
  qed
qed

definition trace_fri_zero_round_final_obstruction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_zero_round_final_obstruction s out \<longleftrightarrow>
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
      \<not> fri_final_constant_consistent trace_table trace_final)"

definition composition_fri_zero_round_final_obstruction
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_zero_round_final_obstruction s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      length composition_bs = 0 \<and>
      \<not> fri_final_constant_consistent composition_table composition_final)"

lemma trace_fri_sampled_layer_assignment_obstruction_imp_conflict_if_nonempty:
  assumes obstruction: "trace_fri_sampled_layer_assignment_obstruction s out"
    and challenges_nonempty:
      "\<And>trace_roots trace_bs trace_final dg composition_roots
          composition_bs composition_final fri_query_idxs trace_round_layers
          composition_round_layers fr candidate_query_idxs trace_openings
          trace_table.
        trace_fri_partial_candidate_opening_evidence s out trace_roots
          trace_bs trace_final dg composition_roots composition_bs
          composition_final fri_query_idxs trace_round_layers
          composition_round_layers fr candidate_query_idxs trace_openings
          trace_table \<Longrightarrow>
        0 < length trace_bs"
  shows "trace_fri_sampled_assignment_conflict s out"
proof (rule trace_fri_sampled_layer_assignment_obstructionE[OF obstruction])
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
  assume obstruction_generic:
    "generic_fri_sampled_layer_assignment_obstruction
      trace_table_low_degree trace_table (clength - 1) trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers"
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have trace_rounds_le: "length trace_bs \<le> N"
  proof -
    have fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
      by (rule trace_fri_partial_candidate_opening_evidenceD(1)
          [OF evidence])
    have len: "length trace_bs = ceil_log clength"
      using accepted_fri_opening_transcript_shapes(1,2)[OF fri_openings]
      by simp
    have "clength \<le> clength * scale"
      using scale_pos by simp
    also have "... = 2 ^ N"
      by (rule eval_power)
    finally have "ceil_log clength \<le> N"
      by (rule ceil_log_le_power)
    then show ?thesis
      using len by simp
  qed
  have query_bounds:
    "\<And>round_idx. round_idx < length fri_query_idxs \<Longrightarrow>
      fri_query_idxs ! round_idx < clength * scale"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length fri_query_idxs"
    have "fri_query_idxs ! round_idx \<in> set fri_query_idxs"
      using round_bound by simp
    then show "fri_query_idxs ! round_idx < clength * scale"
      by (rule trace_fri_partial_candidate_opening_evidence_query_idx_bound
          [OF evidence])
  qed
  have conflict:
    "generic_fri_sampled_assignment_conflict trace_table trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers"
    by (rule generic_fri_sampled_layer_assignment_obstruction_imp_conflict
        [OF obstruction_generic challenges_nonempty[OF evidence]
          query_bounds eval_power trace_rounds_le])
  show ?thesis
    unfolding trace_fri_sampled_assignment_conflict_def
    using evidence conflict by blast
qed

lemma composition_fri_sampled_layer_assignment_obstruction_imp_conflict_if_nonempty:
  assumes support:
    "out \<in> set_dist (execute verify_monad s)"
    and obstruction:
    "composition_fri_sampled_layer_assignment_obstruction s out"
    and challenges_nonempty:
      "\<And>trace_roots trace_bs trace_final fri_dg opening_composition_roots
          composition_bs composition_final fri_query_idxs trace_round_layers
          composition_round_layers fr f_fri_roots f_final as dg
          composition_fri_roots final trace_query_idxs trace_openings
          composition_query_idxs composition_openings trace_table
          composition_table.
        composition_fri_partial_candidate_opening_evidence s out trace_roots
          trace_bs trace_final fri_dg opening_composition_roots
          composition_bs composition_final fri_query_idxs trace_round_layers
          composition_round_layers fr f_fri_roots f_final as dg
          composition_fri_roots final trace_query_idxs trace_openings
          composition_query_idxs composition_openings trace_table
          composition_table \<Longrightarrow>
        0 < length composition_bs"
  shows "composition_fri_sampled_assignment_conflict s out"
proof (rule composition_fri_sampled_layer_assignment_obstructionE
    [OF obstruction])
  fix trace_roots trace_bs trace_final fri_dg opening_composition_roots
    composition_bs composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr f_fri_roots f_final as dg
    composition_fri_roots final trace_query_idxs trace_openings
    composition_query_idxs composition_openings trace_table composition_table
  assume evidence:
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
  assume obstruction_generic:
    "generic_fri_sampled_layer_assignment_obstruction
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers"
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    by (rule composition_fri_partial_candidate_opening_evidenceD(1)
        [OF evidence])
  obtain result final_state where out_eq: "out = Some (result, final_state)"
    using fri_openings unfolding accepted_fri_opening_transcript_def by blast
  have outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using support out_eq by simp
  have challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs fri_dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF fri_openings]
      out_eq by simp
  have degree_bound: "to_nat fri_dg \<le> maxDegree"
    by (rule verify_monad_accepted_fri_challenges_degree_bound
        [OF outcome challenges])
  have composition_rounds_le: "length composition_bs \<le> N"
  proof -
    have len: "length composition_bs = ceil_log (to_nat fri_dg + 1)"
      using accepted_fri_opening_transcript_shapes(3,4)[OF fri_openings]
      by simp
    have "to_nat fri_dg + 1 \<le> clength * scale"
      using degree_bound maxDegree_less_eval_domain by linarith
    also have "... = 2 ^ N"
      by (rule eval_power)
    finally have "ceil_log (to_nat fri_dg + 1) \<le> N"
      by (rule ceil_log_le_power)
    then show ?thesis
      using len by simp
  qed
  have query_bounds:
    "\<And>round_idx. round_idx < length fri_query_idxs \<Longrightarrow>
      fri_query_idxs ! round_idx < clength * scale"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length fri_query_idxs"
    have "fri_query_idxs ! round_idx \<in> set fri_query_idxs"
      using round_bound by simp
    then show "fri_query_idxs ! round_idx < clength * scale"
      by (rule composition_fri_partial_candidate_opening_evidence_query_idx_bound
          [OF evidence])
  qed
  have conflict:
    "generic_fri_sampled_assignment_conflict composition_table
      opening_composition_roots composition_bs composition_final
      fri_query_idxs composition_round_layers"
    by (rule generic_fri_sampled_layer_assignment_obstruction_imp_conflict
        [OF obstruction_generic challenges_nonempty[OF evidence]
          query_bounds eval_power composition_rounds_le])
  show ?thesis
    unfolding composition_fri_sampled_assignment_conflict_def
    apply (intro exI conjI)
     apply (rule evidence)
    apply (rule conflict)
    done
qed

lemma trace_fri_sampled_layer_assignment_obstruction_imp_conflict_or_zero_round_final:
  assumes obstruction: "trace_fri_sampled_layer_assignment_obstruction s out"
  shows
    "trace_fri_sampled_assignment_conflict s out \<or>
     trace_fri_zero_round_final_obstruction s out"
proof (rule trace_fri_sampled_layer_assignment_obstructionE[OF obstruction])
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
  assume obstruction_generic:
    "generic_fri_sampled_layer_assignment_obstruction
      trace_table_low_degree trace_table (clength - 1) trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers"
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have trace_rounds_le: "length trace_bs \<le> N"
  proof -
    have fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
      by (rule trace_fri_partial_candidate_opening_evidenceD(1)
          [OF evidence])
    have len: "length trace_bs = ceil_log clength"
      using accepted_fri_opening_transcript_shapes(1,2)[OF fri_openings]
      by simp
    have "clength \<le> clength * scale"
      using scale_pos by simp
    also have "... = 2 ^ N"
      by (rule eval_power)
    finally have "ceil_log clength \<le> N"
      by (rule ceil_log_le_power)
    then show ?thesis
      using len by simp
  qed
  have query_bounds:
    "\<And>round_idx. round_idx < length fri_query_idxs \<Longrightarrow>
      fri_query_idxs ! round_idx < clength * scale"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length fri_query_idxs"
    have "fri_query_idxs ! round_idx \<in> set fri_query_idxs"
      using round_bound by simp
    then show "fri_query_idxs ! round_idx < clength * scale"
      by (rule trace_fri_partial_candidate_opening_evidence_query_idx_bound
          [OF evidence])
  qed
  have generic:
    "generic_fri_sampled_assignment_conflict trace_table trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers \<or>
     length trace_bs = 0 \<and>
      \<not> fri_final_constant_consistent trace_table trace_final"
    by (rule
        generic_fri_sampled_layer_assignment_obstruction_imp_conflict_or_zero_round_final
          [OF obstruction_generic query_bounds eval_power trace_rounds_le])
  then show ?thesis
  proof
    assume conflict:
      "generic_fri_sampled_assignment_conflict trace_table trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers"
    then show ?thesis
      unfolding trace_fri_sampled_assignment_conflict_def
      using evidence by blast
  next
    assume zero:
      "length trace_bs = 0 \<and>
        \<not> fri_final_constant_consistent trace_table trace_final"
    then show ?thesis
      unfolding trace_fri_zero_round_final_obstruction_def
      using evidence by blast
  qed
qed

lemma composition_fri_sampled_layer_assignment_obstruction_imp_conflict_or_zero_round_final:
  assumes support:
    "out \<in> set_dist (execute verify_monad s)"
    and obstruction:
    "composition_fri_sampled_layer_assignment_obstruction s out"
  shows
    "composition_fri_sampled_assignment_conflict s out \<or>
     composition_fri_zero_round_final_obstruction s out"
proof (rule composition_fri_sampled_layer_assignment_obstructionE
    [OF obstruction])
  fix trace_roots trace_bs trace_final fri_dg opening_composition_roots
    composition_bs composition_final fri_query_idxs trace_round_layers
    composition_round_layers fr f_fri_roots f_final as dg
    composition_fri_roots final trace_query_idxs trace_openings
    composition_query_idxs composition_openings trace_table composition_table
  assume evidence:
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr f_fri_roots f_final as dg
      composition_fri_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings trace_table
      composition_table"
  assume obstruction_generic:
    "generic_fri_sampled_layer_assignment_obstruction
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers"
  obtain N where eval_power: "clength * scale = 2 ^ N"
    using eval_domain_length_power by blast
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg opening_composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    by (rule composition_fri_partial_candidate_opening_evidenceD(1)
        [OF evidence])
  obtain result final_state where out_eq: "out = Some (result, final_state)"
    using fri_openings unfolding accepted_fri_opening_transcript_def by blast
  have outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using support out_eq by simp
  have challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs fri_dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF fri_openings]
      out_eq by simp
  have degree_bound: "to_nat fri_dg \<le> maxDegree"
    by (rule verify_monad_accepted_fri_challenges_degree_bound
        [OF outcome challenges])
  have composition_rounds_le: "length composition_bs \<le> N"
  proof -
    have len: "length composition_bs = ceil_log (to_nat fri_dg + 1)"
      using accepted_fri_opening_transcript_shapes(3,4)[OF fri_openings]
      by simp
    have "to_nat fri_dg + 1 \<le> clength * scale"
      using degree_bound maxDegree_less_eval_domain by linarith
    also have "... = 2 ^ N"
      by (rule eval_power)
    finally have "ceil_log (to_nat fri_dg + 1) \<le> N"
      by (rule ceil_log_le_power)
    then show ?thesis
      using len by simp
  qed
  have query_bounds:
    "\<And>round_idx. round_idx < length fri_query_idxs \<Longrightarrow>
      fri_query_idxs ! round_idx < clength * scale"
  proof -
    fix round_idx
    assume round_bound: "round_idx < length fri_query_idxs"
    have "fri_query_idxs ! round_idx \<in> set fri_query_idxs"
      using round_bound by simp
    then show "fri_query_idxs ! round_idx < clength * scale"
      by (rule composition_fri_partial_candidate_opening_evidence_query_idx_bound
          [OF evidence])
  qed
  have generic:
    "generic_fri_sampled_assignment_conflict composition_table
      opening_composition_roots composition_bs composition_final
      fri_query_idxs composition_round_layers \<or>
     length composition_bs = 0 \<and>
      \<not> fri_final_constant_consistent composition_table
        composition_final"
    by (rule
        generic_fri_sampled_layer_assignment_obstruction_imp_conflict_or_zero_round_final
          [OF obstruction_generic query_bounds eval_power
            composition_rounds_le])
  then show ?thesis
  proof
    assume conflict:
      "generic_fri_sampled_assignment_conflict composition_table
        opening_composition_roots composition_bs composition_final
        fri_query_idxs composition_round_layers"
    then show ?thesis
      unfolding composition_fri_sampled_assignment_conflict_def
      apply (intro disjI1 exI conjI)
       apply (rule evidence)
      apply assumption
      done
  next
    assume zero:
      "length composition_bs = 0 \<and>
        \<not> fri_final_constant_consistent composition_table
          composition_final"
    then show ?thesis
      unfolding composition_fri_zero_round_final_obstruction_def
      apply (intro disjI2 exI conjI)
       apply (rule evidence)
      using zero
      apply simp_all
      done
  qed
qed

end

end
