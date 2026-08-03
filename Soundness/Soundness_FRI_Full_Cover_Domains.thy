(*  Title:      Stark/Soundness_FRI_Full_Cover_Domains.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Full_Cover_Domains
  imports Soundness_FRI_Full_Cover_Lengths
begin

text \<open>
  Domain residuals for sampled full-cover FRI witnesses.

  This theory keeps the remaining domain issue explicitly verifier-sampled:
  a global full-cover domain failure is routed to missing sampled-index
  coverage or to sampled domain facts that still need to be bounded/extracted.
\<close>

context soundness
begin

definition fri_canonical_domain_at :: "nat \<Rightarrow> 'f list"
where
  "fri_canonical_domain_at layer_idx =
    map (\<lambda>idx. (h ^ idx * shift) ^ (2 ^ layer_idx))
      [0..<((clength * scale) div 2 ^ layer_idx)]"

definition fri_canonical_domains :: "nat \<Rightarrow> 'f list list"
where
  "fri_canonical_domains n =
    map fri_canonical_domain_at [0..<Suc n]"

definition generic_fri_canonical_sampled_layer_chain_evidence
  :: "('f list \<Rightarrow> bool) \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> 'f \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "generic_fri_canonical_sampled_layer_chain_evidence low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers \<longleftrightarrow>
    generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"

definition trace_fri_bad_with_canonical_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_canonical_sampled_layer_chain s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_canonical_sampled_layer_chain_evidence
        trace_table_low_degree trace_table (clength - 1) trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers layers)"

definition composition_fri_bad_with_canonical_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_bad_with_canonical_sampled_layer_chain s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg
        opening_composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers fr
        f_fri_roots f_final as dg composition_fri_roots final
        trace_query_idxs trace_openings composition_query_idxs
        composition_openings trace_table composition_table layers.
      composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table \<and>
      generic_fri_canonical_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers layers)"

definition trace_fri_sampled_missing_canonical_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_missing_canonical_sampled_layer_chain s out
    \<longleftrightarrow>
      trace_fri_bad_with_sampled_layer_chain s out \<and>
      \<not> trace_fri_bad_with_canonical_sampled_layer_chain s out"

definition composition_fri_sampled_missing_canonical_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_missing_canonical_sampled_layer_chain s out
    \<longleftrightarrow>
      composition_fri_bad_with_sampled_layer_chain s out \<and>
      \<not> composition_fri_bad_with_canonical_sampled_layer_chain s out"

definition generic_fri_canonical_raw_index_failure
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "generic_fri_canonical_raw_index_failure roots challenges query_idxs
    \<longleftrightarrow>
      (\<exists>round_idx < length query_idxs.
        \<exists>layer_idx < length challenges.
          fri_evidence_layer_idx roots query_idxs round_idx layer_idx \<ge>
            length (fri_canonical_domain_at layer_idx))"

definition trace_fri_canonical_raw_index_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_canonical_raw_index_failure s out \<longleftrightarrow>
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
      generic_fri_canonical_raw_index_failure trace_roots trace_bs
        fri_query_idxs)"

definition composition_fri_canonical_raw_index_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_canonical_raw_index_failure s out \<longleftrightarrow>
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
      generic_fri_canonical_raw_index_failure opening_composition_roots
        composition_bs fri_query_idxs)"

definition fri_sampled_successor_domains_square
  :: "'f list \<Rightarrow> nat list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "fri_sampled_successor_domains_square roots query_idxs doms \<longleftrightarrow>
    (\<forall>round_idx < length query_idxs.
      \<forall>layer_idx < length roots.
        doms ! Suc layer_idx !
          fri_evidence_next_idx roots query_idxs round_idx layer_idx =
        (doms ! layer_idx !
          fri_evidence_next_idx roots query_idxs round_idx layer_idx)\<^sup>2)"

definition generic_fri_full_cover_sampled_domain_failure
  :: "'f list \<Rightarrow> nat list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "generic_fri_full_cover_sampled_domain_failure roots query_idxs doms
    \<longleftrightarrow>
      \<not> fri_sampled_next_domains_align roots query_idxs doms \<or>
      \<not> fri_sampled_successor_domains_square roots query_idxs doms"

definition trace_fri_sampled_full_cover_sampled_domain_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_sampled_domain_failure s out \<longleftrightarrow>
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
      generic_fri_full_cover_sampled_domain_failure trace_roots
        fri_query_idxs doms)"

definition composition_fri_sampled_full_cover_sampled_domain_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_sampled_domain_failure s out
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
      generic_fri_full_cover_sampled_domain_failure
        opening_composition_roots fri_query_idxs doms)"

lemma fri_sampled_successor_domains_squareD:
  assumes "fri_sampled_successor_domains_square roots query_idxs doms"
    and "round_idx < length query_idxs"
    and "layer_idx < length roots"
  shows
    "doms ! Suc layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx =
      (doms ! layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx)\<^sup>2"
  using assms unfolding fri_sampled_successor_domains_square_def by blast

lemma fri_canonical_domain_at_length:
  "length (fri_canonical_domain_at layer_idx) =
    (clength * scale) div 2 ^ layer_idx"
  unfolding fri_canonical_domain_at_def by simp

lemma fri_canonical_domain_at_nth:
  assumes "idx < length (fri_canonical_domain_at layer_idx)"
  shows "fri_canonical_domain_at layer_idx ! idx =
    (h ^ idx * shift) ^ (2 ^ layer_idx)"
  using assms unfolding fri_canonical_domain_at_def by simp

lemma fri_canonical_domains_length:
  "length (fri_canonical_domains n) = Suc n"
  unfolding fri_canonical_domains_def by simp

lemma fri_canonical_domains_nth:
  assumes "layer_idx \<le> n"
  shows "fri_canonical_domains n ! layer_idx =
    fri_canonical_domain_at layer_idx"
proof -
  show ?thesis
  proof (cases "layer_idx < n")
    case True
    have in_left:
      "layer_idx < length (map fri_canonical_domain_at [0..<n])"
      using True by simp
    have append_nth:
      "(map fri_canonical_domain_at [0..<n] @
          [fri_canonical_domain_at n]) ! layer_idx =
        (if layer_idx < length (map fri_canonical_domain_at [0..<n])
         then map fri_canonical_domain_at [0..<n] ! layer_idx
         else [fri_canonical_domain_at n] !
          (layer_idx - length (map fri_canonical_domain_at [0..<n])))"
      by (rule nth_append)
    have "fri_canonical_domains n ! layer_idx =
        map fri_canonical_domain_at [0..<n] ! layer_idx"
      unfolding fri_canonical_domains_def
      using append_nth in_left by simp
    also have "... = fri_canonical_domain_at layer_idx"
      using True by simp
    finally show ?thesis .
  next
    case False
    then have "layer_idx = n"
      using assms by simp
    then have eq_n: "layer_idx = n" .
    have len_left: "length (map fri_canonical_domain_at [0..<n]) = n"
      by simp
    have append_nth:
      "(map fri_canonical_domain_at [0..<n] @
          [fri_canonical_domain_at n]) ! n =
        (if n < length (map fri_canonical_domain_at [0..<n])
         then map fri_canonical_domain_at [0..<n] ! n
         else [fri_canonical_domain_at n] !
          (n - length (map fri_canonical_domain_at [0..<n])))"
      by (rule nth_append)
    show ?thesis
      unfolding fri_canonical_domains_def
      using eq_n len_left append_nth by simp
  qed
qed

lemma fri_canonical_domain_at_0:
  "fri_canonical_domain_at 0 = eval_domain"
proof (rule nth_equalityI)
  show "length (fri_canonical_domain_at 0) = length eval_domain"
    by (simp add: fri_canonical_domain_at_length eval_domain_length)
next
  fix i
  assume i_bound: "i < length (fri_canonical_domain_at 0)"
  then have i_eval: "i < clength * scale"
    by (simp add: fri_canonical_domain_at_length)
  show "fri_canonical_domain_at 0 ! i = eval_domain ! i"
    using fri_canonical_domain_at_nth[OF i_bound] eval_domain_nth[OF i_eval]
    by simp
qed

lemma fri_canonical_domains_0:
  "0 < length (fri_canonical_domains n)"
  by (simp add: fri_canonical_domains_length)

lemma fri_canonical_domains_first:
  "fri_canonical_domains n ! 0 = eval_domain"
  using fri_canonical_domains_nth[of 0 n] fri_canonical_domain_at_0
  by simp

lemma fri_sampled_table_fold_to_canonical_domain:
  assumes fold:
    "fri_sampled_table_fold ch len raw (2 ^ layer_idx) fri_dom layer chunk
      next_value"
    and raw_bound: "raw < length (fri_canonical_domain_at layer_idx)"
  shows
    "fri_sampled_table_fold ch len raw (2 ^ layer_idx)
      (fri_canonical_domain_at layer_idx) layer chunk next_value"
proof -
  from fold obtain xp xp_path xn xn_path where
    chunk: "fri_layer_opening_chunk len xp xp_path xn xn_path chunk"
    and match: "fri_opening_matches_table len raw layer xp xn"
    and dom_raw:
      "fri_dom ! raw = (h ^ raw * shift) ^ (2 ^ layer_idx)"
    and next_eq:
      "next_value =
        fri_table_fold_value ch layer fri_dom len (2 ^ layer_idx) raw"
    by (elim fri_sampled_table_foldE)
  have canonical_raw:
    "fri_canonical_domain_at layer_idx ! raw =
      (h ^ raw * shift) ^ (2 ^ layer_idx)"
    by (rule fri_canonical_domain_at_nth[OF raw_bound])
  have fold_eq:
    "next_value =
      fri_table_fold_value ch layer (fri_canonical_domain_at layer_idx)
        len (2 ^ layer_idx) raw"
    using next_eq dom_raw canonical_raw
    unfolding fri_table_fold_value_def by simp
  show ?thesis
    by (rule fri_sampled_table_foldI
        [OF chunk match canonical_raw fold_eq])
qed

lemma generic_fri_sampled_layer_chain_to_canonical_domains:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
    and raw_bounds:
      "\<And>round_idx layer_idx.
        round_idx < length query_idxs \<Longrightarrow>
        layer_idx < length challenges \<Longrightarrow>
        fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
          length (fri_canonical_domain_at layer_idx)"
  shows
    "generic_fri_canonical_sampled_layer_chain_evidence low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
proof -
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have len_layers: "length layers = Suc (length challenges)"
    by (rule generic_fri_sampled_layer_chain_evidenceD(3)[OF chain])
  have layer0: "layers ! 0 = candidate_table"
    by (rule generic_fri_sampled_layer_chain_evidenceD(5)[OF chain])
  have final:
    "fri_final_constant_consistent (layers ! length challenges)
      final_value"
    by (rule generic_fri_sampled_layer_chain_evidenceD(6)[OF chain])
  have canonical_chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"
    unfolding generic_fri_sampled_layer_chain_evidence_def
  proof (intro conjI allI impI)
    show
      "generic_fri_partial_evidence low_degree candidate_table degree_bound
        roots challenges final_value query_idxs round_layers"
      by (rule partial)
  next
    show "length (fri_canonical_domains (length challenges)) =
      Suc (length challenges)"
      by (rule fri_canonical_domains_length)
  next
    show "length layers = Suc (length challenges)"
      by (rule len_layers)
  next
    show "fri_canonical_domains (length challenges) ! 0 = eval_domain"
      by (rule fri_canonical_domains_first)
  next
    show "layers ! 0 = candidate_table"
      by (rule layer0)
  next
    show
      "fri_final_constant_consistent (layers ! length challenges)
        final_value"
      by (rule final)
  next
    fix round_idx layer_idx
    assume round_bound: "round_idx < length query_idxs"
    assume layer_bound: "layer_idx < length challenges"
    show
      "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        length (layers ! Suc layer_idx)"
      by (rule generic_fri_sampled_layer_chain_evidence_sample(1)
          [OF chain round_bound layer_bound])
  next
    fix round_idx layer_idx
    assume round_bound: "round_idx < length query_idxs"
    assume layer_bound: "layer_idx < length challenges"
    have old_fold:
      "fri_sampled_table_fold (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (doms ! layer_idx)
        (layers ! layer_idx)
        (round_layers ! round_idx ! layer_idx)
        (layers ! Suc layer_idx !
          fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
      by (rule generic_fri_sampled_layer_chain_evidence_sample(2)
          [OF chain round_bound layer_bound])
    have canonical_at:
      "fri_sampled_table_fold (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_canonical_domain_at layer_idx)
        (layers ! layer_idx)
        (round_layers ! round_idx ! layer_idx)
        (layers ! Suc layer_idx !
          fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
      by (rule fri_sampled_table_fold_to_canonical_domain
          [OF old_fold raw_bounds[OF round_bound layer_bound]])
    have dom_nth:
      "fri_canonical_domains (length challenges) ! layer_idx =
        fri_canonical_domain_at layer_idx"
      by (rule fri_canonical_domains_nth) (use layer_bound in simp)
    show
      "fri_sampled_table_fold (challenges ! layer_idx)
        (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (2 ^ layer_idx)
        (fri_canonical_domains (length challenges) ! layer_idx)
        (layers ! layer_idx)
        (round_layers ! round_idx ! layer_idx)
        (layers ! Suc layer_idx !
          fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
      using canonical_at dom_nth by simp
  qed
  show ?thesis
    using canonical_chain
    unfolding generic_fri_canonical_sampled_layer_chain_evidence_def
    by simp
qed

lemma generic_fri_canonical_sampled_layer_chain_evidenceD:
  assumes
    "generic_fri_canonical_sampled_layer_chain_evidence low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
  shows
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"
  using assms
  unfolding generic_fri_canonical_sampled_layer_chain_evidence_def by simp

lemma generic_fri_canonical_sampled_layer_chain_evidenceI:
  assumes
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"
  shows
    "generic_fri_canonical_sampled_layer_chain_evidence low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
  using assms
  unfolding generic_fri_canonical_sampled_layer_chain_evidence_def by simp

lemma generic_fri_sampled_missing_canonical_imp_raw_index_failure:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
    and missing:
      "\<not> generic_fri_canonical_sampled_layer_chain_evidence low_degree
        candidate_table degree_bound roots challenges final_value query_idxs
        round_layers layers"
  shows "generic_fri_canonical_raw_index_failure roots challenges query_idxs"
proof (rule ccontr)
  assume not_failure:
    "\<not> generic_fri_canonical_raw_index_failure roots challenges
      query_idxs"
  have raw_bounds:
    "\<And>round_idx layer_idx.
      round_idx < length query_idxs \<Longrightarrow>
      layer_idx < length challenges \<Longrightarrow>
      fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
        length (fri_canonical_domain_at layer_idx)"
    using not_failure
    unfolding generic_fri_canonical_raw_index_failure_def by force
  have canonical:
    "generic_fri_canonical_sampled_layer_chain_evidence low_degree
      candidate_table degree_bound roots challenges final_value query_idxs
      round_layers layers"
    by (rule generic_fri_sampled_layer_chain_to_canonical_domains
        [OF chain raw_bounds])
  show False
    using missing canonical by contradiction
qed

lemma trace_fri_missing_canonical_sampled_imp_raw_index_failure:
  assumes missing:
    "trace_fri_sampled_missing_canonical_sampled_layer_chain s out"
  shows "trace_fri_canonical_raw_index_failure s out"
proof -
  from missing have sampled:
    "trace_fri_bad_with_sampled_layer_chain s out"
    and not_canonical:
      "\<not> trace_fri_bad_with_canonical_sampled_layer_chain s out"
    unfolding trace_fri_sampled_missing_canonical_sampled_layer_chain_def
    by blast+
  from sampled obtain trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr candidate_query_idxs
      trace_openings trace_table doms layers
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
  have generic_missing:
    "\<not> generic_fri_canonical_sampled_layer_chain_evidence
      trace_table_low_degree trace_table (clength - 1) trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers layers"
  proof
    assume canonical:
      "generic_fri_canonical_sampled_layer_chain_evidence
        trace_table_low_degree trace_table (clength - 1) trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers layers"
    then have "trace_fri_bad_with_canonical_sampled_layer_chain s out"
      unfolding trace_fri_bad_with_canonical_sampled_layer_chain_def
      using evidence by blast
    then show False
      using not_canonical by contradiction
  qed
  have raw_failure:
    "generic_fri_canonical_raw_index_failure trace_roots trace_bs
      fri_query_idxs"
    by (rule generic_fri_sampled_missing_canonical_imp_raw_index_failure
        [OF chain generic_missing])
  show ?thesis
    unfolding trace_fri_canonical_raw_index_failure_def
    using evidence chain raw_failure by blast
qed

lemma composition_fri_missing_canonical_sampled_imp_raw_index_failure:
  assumes missing:
    "composition_fri_sampled_missing_canonical_sampled_layer_chain s out"
  shows "composition_fri_canonical_raw_index_failure s out"
proof -
  from missing have sampled:
    "composition_fri_bad_with_sampled_layer_chain s out"
    and not_canonical:
      "\<not> composition_fri_bad_with_canonical_sampled_layer_chain s out"
    unfolding composition_fri_sampled_missing_canonical_sampled_layer_chain_def
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
  have generic_missing:
    "\<not> generic_fri_canonical_sampled_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers layers"
  proof
    assume canonical:
      "generic_fri_canonical_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers layers"
    then have "composition_fri_bad_with_canonical_sampled_layer_chain s out"
      unfolding composition_fri_bad_with_canonical_sampled_layer_chain_def
      using evidence by meson
    then show False
      using not_canonical by contradiction
  qed
  have raw_failure:
    "generic_fri_canonical_raw_index_failure opening_composition_roots
      composition_bs fri_query_idxs"
    by (rule generic_fri_sampled_missing_canonical_imp_raw_index_failure
        [OF chain generic_missing])
  show ?thesis
    unfolding composition_fri_canonical_raw_index_failure_def
    using evidence chain raw_failure by meson
qed

lemma wp_trace_fri_missing_canonical_sampled_bound_from_raw_index:
  assumes raw_index:
    "wp_event verify_monad (trace_fri_canonical_raw_index_failure s) s
      \<le> R"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_missing_canonical_sampled_layer_chain s) s \<le> R"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_missing_canonical_sampled_layer_chain s) s
      \<le> wp_event verify_monad
        (trace_fri_canonical_raw_index_failure s) s"
    by (rule wp_event_mono)
      (rule trace_fri_missing_canonical_sampled_imp_raw_index_failure)
  also have "... \<le> R"
    by (rule raw_index)
  finally show ?thesis .
qed

lemma wp_composition_fri_missing_canonical_sampled_bound_from_raw_index:
  assumes raw_index:
    "wp_event verify_monad (composition_fri_canonical_raw_index_failure s) s
      \<le> R"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_missing_canonical_sampled_layer_chain s) s
      \<le> R"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_missing_canonical_sampled_layer_chain s) s
      \<le> wp_event verify_monad
        (composition_fri_canonical_raw_index_failure s) s"
    by (rule wp_event_mono)
      (rule composition_fri_missing_canonical_sampled_imp_raw_index_failure)
  also have "... \<le> R"
    by (rule raw_index)
  finally show ?thesis .
qed

lemma generic_fri_sampled_layer_chain_no_canonical_raw_index_failure:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
  shows "\<not> generic_fri_canonical_raw_index_failure roots challenges
    query_idxs"
proof
  assume failure:
    "generic_fri_canonical_raw_index_failure roots challenges query_idxs"
  then obtain round_idx layer_idx where round_bound:
      "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
    and raw_ge:
      "fri_evidence_layer_idx roots query_idxs round_idx layer_idx \<ge>
        length (fri_canonical_domain_at layer_idx)"
    unfolding generic_fri_canonical_raw_index_failure_def by blast
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have roots_challenges: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have roots_bound: "layer_idx < length roots"
    using layer_bound roots_challenges by simp
  have fold:
    "fri_sampled_table_fold (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (doms ! layer_idx)
      (layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      (layers ! Suc layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
    by (rule generic_fri_sampled_layer_chain_evidence_sample(2)
        [OF chain round_bound layer_bound])
  from fold obtain xp xp_path xn xn_path where
    match:
      "fri_opening_matches_table (fri_evidence_layer_len roots layer_idx)
        (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
        (layers ! layer_idx) xp xn"
    by (elim fri_sampled_table_foldE)
  have raw_lt_len:
    "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
      fri_evidence_layer_len roots layer_idx"
    by (rule fri_opening_matches_tableD(1)[OF match])
  have len_eq:
    "fri_evidence_layer_len roots layer_idx =
      length (fri_canonical_domain_at layer_idx)"
    unfolding fri_evidence_layer_len_def fri_canonical_domain_at_length
    using fri_layer_lengths_nth_div[OF roots_bound, of "clength * scale"]
    by simp
  show False
    using raw_lt_len raw_ge unfolding len_eq by simp
qed

lemma trace_fri_canonical_raw_index_failure_false:
  "\<not> trace_fri_canonical_raw_index_failure s out"
proof
  assume raw: "trace_fri_canonical_raw_index_failure s out"
  then obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table doms layers
    where chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
    and failure:
      "generic_fri_canonical_raw_index_failure trace_roots trace_bs
        fri_query_idxs"
    unfolding trace_fri_canonical_raw_index_failure_def by blast
  have "\<not> generic_fri_canonical_raw_index_failure trace_roots trace_bs
      fri_query_idxs"
    by (rule generic_fri_sampled_layer_chain_no_canonical_raw_index_failure
        [OF chain])
  then show False
    using failure by contradiction
qed

lemma composition_fri_canonical_raw_index_failure_false:
  "\<not> composition_fri_canonical_raw_index_failure s out"
proof
  assume raw: "composition_fri_canonical_raw_index_failure s out"
  then obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table doms layers
    where chain:
      "generic_fri_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers doms layers"
    and failure:
      "generic_fri_canonical_raw_index_failure opening_composition_roots
        composition_bs fri_query_idxs"
    unfolding composition_fri_canonical_raw_index_failure_def by meson
  have "\<not> generic_fri_canonical_raw_index_failure
      opening_composition_roots composition_bs fri_query_idxs"
    by (rule generic_fri_sampled_layer_chain_no_canonical_raw_index_failure
        [OF chain])
  then show False
    using failure by contradiction
qed

lemma wp_trace_fri_canonical_raw_index_failure_zero:
  "wp_event verify_monad (trace_fri_canonical_raw_index_failure s) s \<le> 0"
proof -
  have "wp_event verify_monad (trace_fri_canonical_raw_index_failure s) s
      \<le> wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono)
      (simp add: trace_fri_canonical_raw_index_failure_false)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis .
qed

lemma wp_composition_fri_canonical_raw_index_failure_zero:
  "wp_event verify_monad
    (composition_fri_canonical_raw_index_failure s) s \<le> 0"
proof -
  have "wp_event verify_monad
      (composition_fri_canonical_raw_index_failure s) s
      \<le> wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono)
      (simp add: composition_fri_canonical_raw_index_failure_false)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis .
qed

lemma wp_trace_fri_missing_canonical_sampled_zero:
  "wp_event verify_monad
    (trace_fri_sampled_missing_canonical_sampled_layer_chain s) s \<le> 0"
  by (rule wp_trace_fri_missing_canonical_sampled_bound_from_raw_index)
    (rule wp_trace_fri_canonical_raw_index_failure_zero)

lemma wp_composition_fri_missing_canonical_sampled_zero:
  "wp_event verify_monad
    (composition_fri_sampled_missing_canonical_sampled_layer_chain s) s
    \<le> 0"
  by (rule wp_composition_fri_missing_canonical_sampled_bound_from_raw_index)
    (rule wp_composition_fri_canonical_raw_index_failure_zero)

lemma trace_fri_bad_with_canonical_sampled_layer_chain_imp_sampled:
  assumes "trace_fri_bad_with_canonical_sampled_layer_chain s out"
  shows "trace_fri_bad_with_sampled_layer_chain s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and chain:
      "generic_fri_canonical_sampled_layer_chain_evidence
        trace_table_low_degree trace_table (clength - 1) trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers layers"
    unfolding trace_fri_bad_with_canonical_sampled_layer_chain_def by blast
  have sampled:
    "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers
      (fri_canonical_domains (length trace_bs)) layers"
    by (rule generic_fri_canonical_sampled_layer_chain_evidenceD[OF chain])
  show ?thesis
    unfolding trace_fri_bad_with_sampled_layer_chain_def
    using evidence sampled by blast
qed

lemma composition_fri_bad_with_canonical_sampled_layer_chain_imp_sampled:
  assumes "composition_fri_bad_with_canonical_sampled_layer_chain s out"
  shows "composition_fri_bad_with_sampled_layer_chain s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      opening_composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr
      f_fri_roots f_final as dg composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table layers
    where evidence:
      "composition_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final fri_dg opening_composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr f_fri_roots f_final as dg
        composition_fri_roots final trace_query_idxs trace_openings
        composition_query_idxs composition_openings trace_table
        composition_table"
    and chain:
      "generic_fri_canonical_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers layers"
    unfolding composition_fri_bad_with_canonical_sampled_layer_chain_def
    by meson
  have sampled:
    "generic_fri_sampled_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers
      (fri_canonical_domains (length composition_bs)) layers"
    by (rule generic_fri_canonical_sampled_layer_chain_evidenceD[OF chain])
  show ?thesis
    unfolding composition_fri_bad_with_sampled_layer_chain_def
    using evidence sampled by meson
qed

lemma trace_fri_sampled_layer_chain_canonical_or_missing:
  assumes "trace_fri_bad_with_sampled_layer_chain s out"
  shows
    "trace_fri_bad_with_canonical_sampled_layer_chain s out \<or>
     trace_fri_sampled_missing_canonical_sampled_layer_chain s out"
  using assms
  unfolding trace_fri_sampled_missing_canonical_sampled_layer_chain_def
  by blast

lemma composition_fri_sampled_layer_chain_canonical_or_missing:
  assumes "composition_fri_bad_with_sampled_layer_chain s out"
  shows
    "composition_fri_bad_with_canonical_sampled_layer_chain s out \<or>
     composition_fri_sampled_missing_canonical_sampled_layer_chain s out"
  using assms
  unfolding
    composition_fri_sampled_missing_canonical_sampled_layer_chain_def
  by blast

lemma wp_trace_fri_sampled_bound_from_canonical_and_missing:
  assumes canonical:
    "wp_event verify_monad
      (trace_fri_bad_with_canonical_sampled_layer_chain s) s \<le> C"
    and missing:
    "wp_event verify_monad
      (trace_fri_sampled_missing_canonical_sampled_layer_chain s) s \<le> M"
  shows
    "wp_event verify_monad (trace_fri_bad_with_sampled_layer_chain s) s
      \<le> C + M"
proof -
  have "wp_event verify_monad (trace_fri_bad_with_sampled_layer_chain s) s
      \<le> wp_event verify_monad
        (\<lambda>out. trace_fri_bad_with_canonical_sampled_layer_chain s out \<or>
          trace_fri_sampled_missing_canonical_sampled_layer_chain s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_layer_chain_canonical_or_missing)
  also have "... \<le> C + M"
    by (rule order_trans[OF wp_event_union_bound
        add_mono[OF canonical missing]])
  finally show ?thesis .
qed

lemma wp_composition_fri_sampled_bound_from_canonical_and_missing:
  assumes canonical:
    "wp_event verify_monad
      (composition_fri_bad_with_canonical_sampled_layer_chain s) s \<le> C"
    and missing:
    "wp_event verify_monad
      (composition_fri_sampled_missing_canonical_sampled_layer_chain s) s
      \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le> C + M"
proof -
  have "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s
      \<le> wp_event verify_monad
        (\<lambda>out.
          composition_fri_bad_with_canonical_sampled_layer_chain s out \<or>
          composition_fri_sampled_missing_canonical_sampled_layer_chain s out)
        s"
    by (rule wp_event_mono)
      (rule composition_fri_sampled_layer_chain_canonical_or_missing)
  also have "... \<le> C + M"
    by (rule order_trans[OF wp_event_union_bound
        add_mono[OF canonical missing]])
  finally show ?thesis .
qed

lemma wp_trace_fri_sampled_bound_from_canonical:
  assumes canonical:
    "wp_event verify_monad
      (trace_fri_bad_with_canonical_sampled_layer_chain s) s \<le> C"
  shows
    "wp_event verify_monad (trace_fri_bad_with_sampled_layer_chain s) s
      \<le> C"
proof -
  have "wp_event verify_monad (trace_fri_bad_with_sampled_layer_chain s) s
      \<le> C + 0"
    by (rule wp_trace_fri_sampled_bound_from_canonical_and_missing
        [OF canonical wp_trace_fri_missing_canonical_sampled_zero])
  then show ?thesis by simp
qed

lemma wp_composition_fri_sampled_bound_from_canonical:
  assumes canonical:
    "wp_event verify_monad
      (composition_fri_bad_with_canonical_sampled_layer_chain s) s \<le> C"
  shows
    "wp_event verify_monad (composition_fri_bad_with_sampled_layer_chain s) s
      \<le> C"
proof -
  have "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le> C + 0"
    by (rule wp_composition_fri_sampled_bound_from_canonical_and_missing
        [OF canonical wp_composition_fri_missing_canonical_sampled_zero])
  then show ?thesis by simp
qed

lemma wp_trace_fri_canonical_sampled_bound_from_sampled:
  assumes sampled:
    "wp_event verify_monad (trace_fri_bad_with_sampled_layer_chain s) s
      \<le> R"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_canonical_sampled_layer_chain s) s \<le> R"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_canonical_sampled_layer_chain s) s \<le>
    wp_event verify_monad (trace_fri_bad_with_sampled_layer_chain s) s"
    by (rule wp_event_mono)
      (rule trace_fri_bad_with_canonical_sampled_layer_chain_imp_sampled)
  then show ?thesis
    by (rule order_trans[OF _ sampled])
qed

lemma wp_composition_fri_canonical_sampled_bound_from_sampled:
  assumes sampled:
    "wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s \<le> R"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_canonical_sampled_layer_chain s) s \<le> R"
proof -
  have "wp_event verify_monad
      (composition_fri_bad_with_canonical_sampled_layer_chain s) s \<le>
    wp_event verify_monad
      (composition_fri_bad_with_sampled_layer_chain s) s"
    by (rule wp_event_mono)
      (rule composition_fri_bad_with_canonical_sampled_layer_chain_imp_sampled)
  then show ?thesis
    by (rule order_trans[OF _ sampled])
qed

lemma wp_trace_fri_canonical_sampled_bound_from_full_cover_and_missing:
  assumes full_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_full_cover_layer_chain s bad) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_canonical_sampled_layer_chain s) s \<le> R + M"
  by (rule wp_trace_fri_canonical_sampled_bound_from_sampled)
    (rule wp_trace_fri_sampled_bound_from_full_cover_and_missing
      [OF full_bound missing_bound])

lemma wp_composition_fri_canonical_sampled_bound_from_full_cover_and_missing:
  assumes full_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_full_cover_layer_chain s bad) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_canonical_sampled_layer_chain s) s
      \<le> R + M"
  by (rule wp_composition_fri_canonical_sampled_bound_from_sampled)
    (rule wp_composition_fri_sampled_bound_from_full_cover_and_missing
      [OF full_bound missing_bound])

lemma verify_monad_trace_fri_missing_canonical_sampled_extracts_evidence:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and missing:
      "trace_fri_sampled_missing_canonical_sampled_layer_chain s
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
    "\<And>canonical_layers. \<not>
      generic_fri_canonical_sampled_layer_chain_evidence
        trace_table_low_degree trace_table (clength - 1) trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers
        canonical_layers"
proof -
  have sampled:
    "trace_fri_bad_with_sampled_layer_chain s
      (Some (result, final_state))"
    and not_canonical:
      "\<not> trace_fri_bad_with_canonical_sampled_layer_chain s
        (Some (result, final_state))"
    using missing
    unfolding trace_fri_sampled_missing_canonical_sampled_layer_chain_def
    by blast+
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
  have no_canonical:
    "\<And>canonical_layers. \<not>
      generic_fri_canonical_sampled_layer_chain_evidence
        trace_table_low_degree trace_table (clength - 1) trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers
        canonical_layers"
  proof
    fix canonical_layers
    assume canonical:
      "generic_fri_canonical_sampled_layer_chain_evidence
        trace_table_low_degree trace_table (clength - 1) trace_roots
        trace_bs trace_final fri_query_idxs trace_round_layers
        canonical_layers"
    have "trace_fri_bad_with_canonical_sampled_layer_chain s
        (Some (result, final_state))"
      unfolding trace_fri_bad_with_canonical_sampled_layer_chain_def
      using evidence canonical by blast
    then show False
      using not_canonical by contradiction
  qed
  show ?thesis
    by (rule that[OF evidence chain no_canonical])
qed

lemma verify_monad_composition_fri_missing_canonical_sampled_extracts_evidence:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and missing:
      "composition_fri_sampled_missing_canonical_sampled_layer_chain s
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
    "\<And>canonical_layers. \<not>
      generic_fri_canonical_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        canonical_layers"
proof -
  have sampled:
    "composition_fri_bad_with_sampled_layer_chain s
      (Some (result, final_state))"
    and not_canonical:
      "\<not> composition_fri_bad_with_canonical_sampled_layer_chain s
        (Some (result, final_state))"
    using missing
    unfolding
      composition_fri_sampled_missing_canonical_sampled_layer_chain_def
    by blast+
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
    unfolding composition_fri_bad_with_sampled_layer_chain_def by meson
  have no_canonical:
    "\<And>canonical_layers. \<not>
      generic_fri_canonical_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        canonical_layers"
  proof
    fix canonical_layers
    assume canonical:
      "generic_fri_canonical_sampled_layer_chain_evidence
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        canonical_layers"
    have "composition_fri_bad_with_canonical_sampled_layer_chain s
        (Some (result, final_state))"
      unfolding composition_fri_bad_with_canonical_sampled_layer_chain_def
      using evidence canonical by meson
    then show False
      using not_canonical by contradiction
  qed
  show ?thesis
    by (rule that[OF evidence chain no_canonical])
qed

lemma fri_canonical_domain_successor_square:
  assumes next_bound:
    "idx < length (fri_canonical_domain_at (Suc layer_idx))"
    and cur_bound:
    "idx < length (fri_canonical_domain_at layer_idx)"
  shows "fri_canonical_domain_at (Suc layer_idx) ! idx =
    (fri_canonical_domain_at layer_idx ! idx)\<^sup>2"
proof -
  have next_val:
    "fri_canonical_domain_at (Suc layer_idx) ! idx =
      (h ^ idx * shift) ^ (2 ^ Suc layer_idx)"
    by (rule fri_canonical_domain_at_nth[OF next_bound])
  have cur_val:
    "fri_canonical_domain_at layer_idx ! idx =
      (h ^ idx * shift) ^ (2 ^ layer_idx)"
    by (rule fri_canonical_domain_at_nth[OF cur_bound])
  have square:
    "(h ^ idx * shift) ^ (2 ^ Suc layer_idx) =
      ((h ^ idx * shift) ^ (2 ^ layer_idx))\<^sup>2"
    by (metis mult.commute power2_eq_square power_Suc power_mult)
  show ?thesis
    using next_val cur_val square by simp
qed

lemma fri_canonical_domains_successor_square:
  assumes layer_bound: "Suc layer_idx \<le> n"
    and idx_bound:
      "idx < length (fri_canonical_domains n ! Suc layer_idx)"
    and cur_idx_bound:
      "idx < length (fri_canonical_domains n ! layer_idx)"
  shows "fri_canonical_domains n ! Suc layer_idx ! idx =
    (fri_canonical_domains n ! layer_idx ! idx)\<^sup>2"
proof -
  have cur_bound: "layer_idx \<le> n"
    using layer_bound by simp
  have next_dom:
    "fri_canonical_domains n ! Suc layer_idx =
      fri_canonical_domain_at (Suc layer_idx)"
    by (rule fri_canonical_domains_nth[OF layer_bound])
  have cur_dom:
    "fri_canonical_domains n ! layer_idx =
      fri_canonical_domain_at layer_idx"
    by (rule fri_canonical_domains_nth[OF cur_bound])
  show ?thesis
    using fri_canonical_domain_successor_square
      [of idx layer_idx] idx_bound cur_idx_bound
    unfolding next_dom cur_dom by simp
qed

lemma fri_canonical_domains_sampled_next_align:
  assumes roots_bound: "length roots \<le> n"
    and idx_bound:
      "\<And>round_idx layer_idx.
        round_idx < length query_idxs \<Longrightarrow>
        layer_idx < length roots \<Longrightarrow>
        fri_evidence_next_idx roots query_idxs round_idx layer_idx <
          length (fri_canonical_domain_at layer_idx)"
  shows
    "fri_sampled_next_domains_align roots query_idxs
      (fri_canonical_domains n)"
  unfolding fri_sampled_next_domains_align_def
proof (intro allI impI)
  fix round_idx layer_idx
  assume round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length roots"
  have layer_le: "layer_idx \<le> n"
    using layer_bound roots_bound by simp
  have dom_eq:
    "fri_canonical_domains n ! layer_idx =
      fri_canonical_domain_at layer_idx"
    by (rule fri_canonical_domains_nth[OF layer_le])
  have idx:
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      length (fri_canonical_domain_at layer_idx)"
    by (rule idx_bound[OF round_bound layer_bound])
  show
    "fri_canonical_domains n ! layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx =
      (h ^ fri_evidence_next_idx roots query_idxs round_idx layer_idx *
        shift) ^ (2 ^ layer_idx)"
    unfolding dom_eq
    by (rule fri_canonical_domain_at_nth[OF idx])
qed

lemma fri_canonical_domains_sampled_successor_square:
  assumes roots_bound: "length roots \<le> n"
    and cur_idx_bound:
      "\<And>round_idx layer_idx.
        round_idx < length query_idxs \<Longrightarrow>
        layer_idx < length roots \<Longrightarrow>
        fri_evidence_next_idx roots query_idxs round_idx layer_idx <
          length (fri_canonical_domains n ! layer_idx)"
    and next_idx_bound:
      "\<And>round_idx layer_idx.
        round_idx < length query_idxs \<Longrightarrow>
        layer_idx < length roots \<Longrightarrow>
        fri_evidence_next_idx roots query_idxs round_idx layer_idx <
          length (fri_canonical_domains n ! Suc layer_idx)"
  shows
    "fri_sampled_successor_domains_square roots query_idxs
      (fri_canonical_domains n)"
  unfolding fri_sampled_successor_domains_square_def
proof (intro allI impI)
  fix round_idx layer_idx
  assume round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length roots"
  have layer_le: "Suc layer_idx \<le> n"
    using layer_bound roots_bound by simp
  show
    "fri_canonical_domains n ! Suc layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx =
      (fri_canonical_domains n ! layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx)\<^sup>2"
    by (rule fri_canonical_domains_successor_square[OF layer_le])
      (rule next_idx_bound[OF round_bound layer_bound],
       rule cur_idx_bound[OF round_bound layer_bound])
qed

lemma fri_canonical_domains_no_sampled_domain_failure:
  assumes roots_bound: "length roots \<le> n"
    and canonical_next_bound:
      "\<And>round_idx layer_idx.
        round_idx < length query_idxs \<Longrightarrow>
        layer_idx < length roots \<Longrightarrow>
        fri_evidence_next_idx roots query_idxs round_idx layer_idx <
          length (fri_canonical_domain_at layer_idx)"
    and canonical_successor_bound:
      "\<And>round_idx layer_idx.
        round_idx < length query_idxs \<Longrightarrow>
        layer_idx < length roots \<Longrightarrow>
        fri_evidence_next_idx roots query_idxs round_idx layer_idx <
          length (fri_canonical_domains n ! Suc layer_idx)"
  shows "\<not> generic_fri_full_cover_sampled_domain_failure roots query_idxs
    (fri_canonical_domains n)"
proof -
  have next_align:
    "fri_sampled_next_domains_align roots query_idxs
      (fri_canonical_domains n)"
    by (rule fri_canonical_domains_sampled_next_align
        [OF roots_bound canonical_next_bound])
  have cur_bound:
    "\<And>round_idx layer_idx.
      round_idx < length query_idxs \<Longrightarrow>
      layer_idx < length roots \<Longrightarrow>
      fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        length (fri_canonical_domains n ! layer_idx)"
  proof -
    fix round_idx layer_idx
    assume round_bound: "round_idx < length query_idxs"
      and layer_bound: "layer_idx < length roots"
    have layer_le: "layer_idx \<le> n"
      using layer_bound roots_bound by simp
    have dom_eq:
      "fri_canonical_domains n ! layer_idx =
        fri_canonical_domain_at layer_idx"
      by (rule fri_canonical_domains_nth[OF layer_le])
    show
      "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        length (fri_canonical_domains n ! layer_idx)"
      unfolding dom_eq
      by (rule canonical_next_bound[OF round_bound layer_bound])
  qed
  have succ_square:
    "fri_sampled_successor_domains_square roots query_idxs
      (fri_canonical_domains n)"
    by (rule fri_canonical_domains_sampled_successor_square
        [OF roots_bound cur_bound canonical_successor_bound])
  show ?thesis
    unfolding generic_fri_full_cover_sampled_domain_failure_def
    using next_align succ_square by simp
qed

lemma generic_fri_full_cover_domain_failure_imp_index_or_sampled_domain:
  assumes roots_len: "length challenges = length roots"
    and domain: "generic_fri_full_cover_domain_failure roots challenges doms"
  shows
    "generic_fri_full_cover_index_failure roots query_idxs \<or>
     generic_fri_full_cover_sampled_domain_failure roots query_idxs doms"
proof (cases "generic_fri_full_cover_index_failure roots query_idxs")
  case True
  then show ?thesis by simp
next
  case False
  have covers: "fri_sampled_layers_cover_fold_indices roots query_idxs"
    using False unfolding generic_fri_full_cover_index_failure_def by simp
  show ?thesis
  proof (cases
      "generic_fri_full_cover_sampled_domain_failure roots query_idxs doms")
    case True
    then show ?thesis by simp
  next
    case no_sampled: False
    have next_align: "fri_sampled_next_domains_align roots query_idxs doms"
      and succ_square:
        "fri_sampled_successor_domains_square roots query_idxs doms"
      using no_sampled
      unfolding generic_fri_full_cover_sampled_domain_failure_def
      by simp_all
    have no_square_fail:
      "\<forall>layer_idx < length challenges.
        \<forall>idx < fri_evidence_layer_len roots layer_idx div 2.
          doms ! Suc layer_idx ! idx =
            (doms ! layer_idx ! idx)\<^sup>2"
    proof (intro allI impI)
      fix layer_idx idx
      assume layer_bound: "layer_idx < length challenges"
        and idx_bound: "idx < fri_evidence_layer_len roots layer_idx div 2"
      have layer_root_bound: "layer_idx < length roots"
        using layer_bound roots_len by simp
      obtain round_idx where round_bound: "round_idx < length query_idxs"
        and idx_eq:
          "fri_evidence_next_idx roots query_idxs round_idx layer_idx = idx"
        by (rule fri_sampled_layers_cover_fold_indicesD
            [OF covers layer_root_bound idx_bound])
      show "doms ! Suc layer_idx ! idx =
          (doms ! layer_idx ! idx)\<^sup>2"
        using fri_sampled_successor_domains_squareD
          [OF succ_square round_bound layer_root_bound] idx_eq
        by simp
    qed
    have no_norm_fail:
      "\<forall>layer_idx < length challenges.
        \<forall>idx < fri_evidence_layer_len roots layer_idx div 2.
          doms ! layer_idx ! idx =
            (h ^ idx * shift) ^ (2 ^ layer_idx)"
    proof (intro allI impI)
      fix layer_idx idx
      assume layer_bound: "layer_idx < length challenges"
        and idx_bound: "idx < fri_evidence_layer_len roots layer_idx div 2"
      have layer_root_bound: "layer_idx < length roots"
        using layer_bound roots_len by simp
      obtain round_idx where round_bound: "round_idx < length query_idxs"
        and idx_eq:
          "fri_evidence_next_idx roots query_idxs round_idx layer_idx = idx"
        by (rule fri_sampled_layers_cover_fold_indicesD
            [OF covers layer_root_bound idx_bound])
      show "doms ! layer_idx ! idx =
          (h ^ idx * shift) ^ (2 ^ layer_idx)"
        using fri_sampled_next_domains_alignD
          [OF next_align round_bound layer_root_bound] idx_eq
        by simp
    qed
    have False
      using domain no_square_fail no_norm_fail
      unfolding generic_fri_full_cover_domain_failure_def by simp
    then show ?thesis by simp
  qed
qed

lemma trace_fri_sampled_full_cover_domain_imp_index_or_sampled_domain:
  assumes domain: "trace_fri_sampled_full_cover_domain_failure s out"
  shows
    "trace_fri_sampled_full_cover_index_failure s out \<or>
     trace_fri_sampled_full_cover_sampled_domain_failure s out"
proof -
  from domain obtain trace_roots trace_bs trace_final dg composition_roots
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
    and generic_domain:
      "generic_fri_full_cover_domain_failure trace_roots trace_bs doms"
    unfolding trace_fri_sampled_full_cover_domain_failure_def by blast
  have partial:
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have roots_len: "length trace_bs = length trace_roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have split:
    "generic_fri_full_cover_index_failure trace_roots fri_query_idxs \<or>
     generic_fri_full_cover_sampled_domain_failure trace_roots
      fri_query_idxs doms"
    by (rule generic_fri_full_cover_domain_failure_imp_index_or_sampled_domain
        [OF roots_len generic_domain])
  then show ?thesis
  proof
    assume "generic_fri_full_cover_index_failure trace_roots fri_query_idxs"
    then show ?thesis
      unfolding trace_fri_sampled_full_cover_index_failure_def
      using evidence chain by blast
  next
    assume
      "generic_fri_full_cover_sampled_domain_failure trace_roots
        fri_query_idxs doms"
    then show ?thesis
      unfolding trace_fri_sampled_full_cover_sampled_domain_failure_def
      using evidence chain by blast
  qed
qed

lemma composition_fri_sampled_full_cover_domain_imp_index_or_sampled_domain:
  assumes domain: "composition_fri_sampled_full_cover_domain_failure s out"
  shows
    "composition_fri_sampled_full_cover_index_failure s out \<or>
     composition_fri_sampled_full_cover_sampled_domain_failure s out"
proof -
  from domain obtain trace_roots trace_bs trace_final fri_dg
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
    and generic_domain:
      "generic_fri_full_cover_domain_failure opening_composition_roots
        composition_bs doms"
    unfolding composition_fri_sampled_full_cover_domain_failure_def
    by meson
  have partial:
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have roots_len: "length composition_bs = length opening_composition_roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have split:
    "generic_fri_full_cover_index_failure opening_composition_roots
      fri_query_idxs \<or>
     generic_fri_full_cover_sampled_domain_failure
      opening_composition_roots fri_query_idxs doms"
    by (rule generic_fri_full_cover_domain_failure_imp_index_or_sampled_domain
        [OF roots_len generic_domain])
  then show ?thesis
  proof
    assume
      "generic_fri_full_cover_index_failure opening_composition_roots
        fri_query_idxs"
    then show ?thesis
      unfolding composition_fri_sampled_full_cover_index_failure_def
      using evidence chain by meson
  next
    assume
      "generic_fri_full_cover_sampled_domain_failure
        opening_composition_roots fri_query_idxs doms"
    then show ?thesis
      unfolding composition_fri_sampled_full_cover_sampled_domain_failure_def
      using evidence chain by meson
  qed
qed

lemma wp_trace_fri_sampled_full_cover_domain_bound_from_index_or_sampled_domain:
  assumes index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and sampled_domain:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_sampled_domain_failure s) s \<le> SD"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_failure s) s \<le> I + SD"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_failure s) s
    \<le> wp_event verify_monad
      (\<lambda>out. trace_fri_sampled_full_cover_index_failure s out \<or>
        trace_fri_sampled_full_cover_sampled_domain_failure s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_full_cover_domain_imp_index_or_sampled_domain)
  also have "... \<le> I + SD"
    by (rule order_trans[OF wp_event_union_bound
        add_mono[OF index sampled_domain]])
  finally show ?thesis .
qed

lemma
  wp_composition_fri_sampled_full_cover_domain_bound_from_index_or_sampled_domain:
  assumes index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and sampled_domain:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_sampled_domain_failure s) s
      \<le> SD"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_failure s) s \<le> I + SD"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_failure s) s
    \<le> wp_event verify_monad
      (\<lambda>out. composition_fri_sampled_full_cover_index_failure s out \<or>
        composition_fri_sampled_full_cover_sampled_domain_failure s out) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_sampled_full_cover_domain_imp_index_or_sampled_domain)
  also have "... \<le> I + SD"
    by (rule order_trans[OF wp_event_union_bound
        add_mono[OF index sampled_domain]])
  finally show ?thesis .
qed

lemma wp_trace_fri_sampled_missing_full_cover_bound_from_domain_split:
  assumes proximity:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and domain_length:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_length_failure s) s \<le> DL"
    and sampled_domain:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_sampled_domain_failure s) s \<le> SD"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + (I + DL) + (I + SD)"
  by (rule wp_trace_fri_sampled_missing_full_cover_bound_from_length_split
      [OF proximity index domain_length
        wp_trace_fri_sampled_full_cover_domain_bound_from_index_or_sampled_domain])
    (rule index, rule sampled_domain)

lemma wp_composition_fri_sampled_missing_full_cover_bound_from_domain_split:
  assumes proximity:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and domain_length:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_length_failure s) s \<le> DL"
    and sampled_domain:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_sampled_domain_failure s) s
      \<le> SD"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + (I + DL) + (I + SD)"
  by (rule
      wp_composition_fri_sampled_missing_full_cover_bound_from_length_split
      [OF proximity index domain_length
        wp_composition_fri_sampled_full_cover_domain_bound_from_index_or_sampled_domain])
    (rule index, rule sampled_domain)

end

end
