(*  Title:      Stark/Soundness_FRI_Full_Cover_Lengths.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Full_Cover_Lengths
  imports Soundness_FRI_Full_Cover_Reasons
begin

text \<open>
  Length residuals for sampled full-cover FRI witnesses.

  Arithmetic shape failures are impossible, and table-layer length failures
  follow from sampled fold coverage.  This theory factors the remaining
  witness-length residual into domain-length/final-length obligations plus the
  already-classified sampled-index coverage failure.
\<close>

context soundness
begin

definition generic_fri_full_cover_domain_length_failure
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list list \<Rightarrow> 'f list list \<Rightarrow> bool"
where
  "generic_fri_full_cover_domain_length_failure roots challenges doms layers
    \<longleftrightarrow>
      \<not> (\<forall>layer_idx < length challenges.
        fri_evidence_layer_len roots layer_idx \<le>
          length (doms ! layer_idx)) \<or>
      \<not> (\<forall>layer_idx < length challenges.
        fri_evidence_layer_len roots layer_idx div 2 \<le>
          length (doms ! Suc layer_idx)) \<or>
      length (doms ! length challenges) \<noteq>
        length (layers ! length challenges)"

definition trace_fri_sampled_full_cover_domain_length_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_full_cover_domain_length_failure s out \<longleftrightarrow>
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
      generic_fri_full_cover_domain_length_failure trace_roots trace_bs
        doms layers)"

definition composition_fri_sampled_full_cover_domain_length_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_full_cover_domain_length_failure s out
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
      generic_fri_full_cover_domain_length_failure
        opening_composition_roots composition_bs doms layers)"

lemma generic_fri_sampled_layer_chain_next_layer_lengths_if_cover:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
    and covers: "fri_sampled_layers_cover_fold_indices roots query_idxs"
    and layer_bound: "layer_idx < length challenges"
  shows
    "fri_evidence_layer_len roots layer_idx div 2 \<le>
      length (layers ! Suc layer_idx)"
proof (rule ccontr)
  assume not_len:
    "\<not> fri_evidence_layer_len roots layer_idx div 2 \<le>
      length (layers ! Suc layer_idx)"
  let ?idx = "length (layers ! Suc layer_idx)"
  have idx_bound:
    "?idx < fri_evidence_layer_len roots layer_idx div 2"
    using not_len by simp
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  obtain round_idx where round_bound: "round_idx < length query_idxs"
    and next_eq:
      "fri_evidence_next_idx roots query_idxs round_idx layer_idx = ?idx"
    by (rule fri_sampled_layers_cover_fold_indicesD
        [OF covers _ idx_bound])
      (use layer_bound roots_len in simp)
  have "?idx < length (layers ! Suc layer_idx)"
    using generic_fri_sampled_layer_chain_evidence_sample(1)
        [OF chain round_bound layer_bound]
      next_eq by simp
  then show False by simp
qed

lemma generic_fri_sampled_layer_chain_layer_lengths_if_cover:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
    and covers: "fri_sampled_layers_cover_fold_indices roots query_idxs"
    and base_len: "length candidate_table = clength * scale"
    and layer_bound: "layer_idx < length challenges"
  shows "fri_evidence_layer_len roots layer_idx \<le>
    length (layers ! layer_idx)"
proof (cases layer_idx)
  case 0
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have roots_nonempty: "0 < length roots"
    using layer_bound roots_len unfolding 0 by simp
  then obtain n where roots_len_suc: "length roots = Suc n"
    by (cases "length roots") auto
  have len0: "fri_evidence_layer_len roots 0 = clength * scale"
    using roots_len_suc unfolding 0 fri_evidence_layer_len_def by simp
  have layer0: "layers ! 0 = candidate_table"
    by (rule generic_fri_sampled_layer_chain_evidenceD(5)[OF chain])
  show ?thesis
    using len0 layer0 base_len unfolding 0 by simp
next
  case (Suc j)
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have j_bound: "j < length challenges"
    using layer_bound unfolding Suc by simp
  have len_suc:
    "fri_evidence_layer_len roots (Suc j) =
      fri_evidence_layer_len roots j div 2"
    using fri_layer_lengths_Suc_nth[of j "length roots" "clength * scale"]
      layer_bound roots_len
    unfolding fri_evidence_layer_len_def Suc by simp
  have next_len:
    "fri_evidence_layer_len roots j div 2 \<le> length (layers ! Suc j)"
    by (rule generic_fri_sampled_layer_chain_next_layer_lengths_if_cover
        [OF chain covers j_bound])
  show ?thesis
    using len_suc next_len unfolding Suc by simp
qed

lemma generic_fri_witness_length_failure_imp_domain_length_if_cover:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      doms layers"
    and no_index:
      "\<not> generic_fri_full_cover_index_failure roots query_idxs"
    and base_len: "length candidate_table = clength * scale"
    and witness:
      "generic_fri_full_cover_witness_length_failure roots challenges
        doms layers"
  shows "generic_fri_full_cover_domain_length_failure roots challenges
    doms layers"
proof -
  have covers: "fri_sampled_layers_cover_fold_indices roots query_idxs"
    using no_index unfolding generic_fri_full_cover_index_failure_def by simp
  have layer_len:
    "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
      fri_evidence_layer_len roots layer_idx \<le>
        length (layers ! layer_idx)"
    by (rule generic_fri_sampled_layer_chain_layer_lengths_if_cover
        [OF chain covers base_len])
  have next_layer_len:
    "\<And>layer_idx. layer_idx < length challenges \<Longrightarrow>
      fri_evidence_layer_len roots layer_idx div 2 \<le>
        length (layers ! Suc layer_idx)"
    by (rule generic_fri_sampled_layer_chain_next_layer_lengths_if_cover
        [OF chain covers])
  show ?thesis
    using witness layer_len next_layer_len
    unfolding generic_fri_full_cover_witness_length_failure_def
      generic_fri_full_cover_domain_length_failure_def
    by blast
qed

lemma trace_fri_sampled_full_cover_witness_length_imp_index_or_domain_length:
  assumes witness:
    "trace_fri_sampled_full_cover_witness_length_failure s out"
  shows
    "trace_fri_sampled_full_cover_index_failure s out \<or>
     trace_fri_sampled_full_cover_domain_length_failure s out"
proof -
  from witness obtain trace_roots trace_bs trace_final dg composition_roots
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
    and generic_witness:
      "generic_fri_full_cover_witness_length_failure trace_roots trace_bs
        doms layers"
    unfolding trace_fri_sampled_full_cover_witness_length_failure_def
    by blast
  show ?thesis
  proof (cases
      "generic_fri_full_cover_index_failure trace_roots fri_query_idxs")
    case True
    then show ?thesis
      unfolding trace_fri_sampled_full_cover_index_failure_def
      using evidence chain by blast
  next
    case False
    have partial:
      "trace_fri_partial_candidate_evidence s out fr candidate_query_idxs
        trace_openings trace_table"
      by (rule trace_fri_partial_candidate_opening_evidenceD(2)
          [OF evidence])
    have cand:
      "partial_trace_table_candidate trace_table trace_openings"
      by (rule trace_fri_partial_candidate_evidenceD(2)[OF partial])
    have base_len: "length trace_table = clength * scale"
      using cand unfolding partial_trace_table_candidate_def by simp
    have domain_length:
      "generic_fri_full_cover_domain_length_failure trace_roots trace_bs
        doms layers"
      by (rule generic_fri_witness_length_failure_imp_domain_length_if_cover
          [OF chain False base_len generic_witness])
    then show ?thesis
      unfolding trace_fri_sampled_full_cover_domain_length_failure_def
      using evidence chain by blast
  qed
qed

lemma composition_fri_sampled_full_cover_witness_length_imp_index_or_domain_length:
  assumes witness:
    "composition_fri_sampled_full_cover_witness_length_failure s out"
  shows
    "composition_fri_sampled_full_cover_index_failure s out \<or>
     composition_fri_sampled_full_cover_domain_length_failure s out"
proof -
  from witness obtain trace_roots trace_bs trace_final fri_dg
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
    and generic_witness:
      "generic_fri_full_cover_witness_length_failure
        opening_composition_roots composition_bs doms layers"
    unfolding composition_fri_sampled_full_cover_witness_length_failure_def
    by meson
  show ?thesis
  proof (cases
      "generic_fri_full_cover_index_failure opening_composition_roots
        fri_query_idxs")
    case True
    then show ?thesis
      unfolding composition_fri_sampled_full_cover_index_failure_def
      using evidence chain by meson
  next
    case False
    have partial:
      "composition_fri_partial_candidate_evidence s out fr f_fri_roots
        f_final as dg composition_fri_roots final trace_query_idxs
        trace_openings composition_query_idxs composition_openings
        trace_table composition_table"
      by (rule composition_fri_partial_candidate_opening_evidenceD(2)
          [OF evidence])
    have cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
      by (rule composition_fri_partial_candidate_evidenceD(3)[OF partial])
    have base_len: "length composition_table = clength * scale"
      using cand unfolding partial_composition_table_candidate_def by simp
    have domain_length:
      "generic_fri_full_cover_domain_length_failure
        opening_composition_roots composition_bs doms layers"
      by (rule generic_fri_witness_length_failure_imp_domain_length_if_cover
          [OF chain False base_len generic_witness])
    then show ?thesis
      unfolding composition_fri_sampled_full_cover_domain_length_failure_def
      using evidence chain by meson
  qed
qed

lemma wp_trace_fri_sampled_full_cover_witness_length_bound_from_index_or_domain_length:
  assumes index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and domain_length:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_length_failure s) s \<le> DL"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_witness_length_failure s) s
      \<le> I + DL"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_full_cover_witness_length_failure s) s
    \<le> wp_event verify_monad
      (\<lambda>out. trace_fri_sampled_full_cover_index_failure s out \<or>
        trace_fri_sampled_full_cover_domain_length_failure s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_full_cover_witness_length_imp_index_or_domain_length)
  also have "... \<le> I + DL"
    by (rule order_trans[OF wp_event_union_bound
        add_mono[OF index domain_length]])
  finally show ?thesis .
qed

lemma wp_composition_fri_sampled_full_cover_witness_length_bound_from_index_or_domain_length:
  assumes index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and domain_length:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_length_failure s) s \<le> DL"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_witness_length_failure s) s
      \<le> I + DL"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_full_cover_witness_length_failure s) s
    \<le> wp_event verify_monad
      (\<lambda>out. composition_fri_sampled_full_cover_index_failure s out \<or>
        composition_fri_sampled_full_cover_domain_length_failure s out) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_sampled_full_cover_witness_length_imp_index_or_domain_length)
  also have "... \<le> I + DL"
    by (rule order_trans[OF wp_event_union_bound
        add_mono[OF index domain_length]])
  finally show ?thesis .
qed

lemma wp_trace_fri_sampled_missing_full_cover_bound_from_length_split:
  assumes proximity:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and domain_length:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_length_failure s) s \<le> DL"
    and domain:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_domain_failure s) s \<le> D"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + (I + DL) + D"
  by (rule wp_trace_fri_sampled_missing_full_cover_bound_from_witness_length_subcases
      [OF proximity index
        wp_trace_fri_sampled_full_cover_witness_length_bound_from_index_or_domain_length
        domain])
    (rule index, rule domain_length)

lemma wp_composition_fri_sampled_missing_full_cover_bound_from_length_split:
  assumes proximity:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and domain_length:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_length_failure s) s \<le> DL"
    and domain:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_domain_failure s) s \<le> D"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s
      \<le> P + I + (I + DL) + D"
  by (rule
      wp_composition_fri_sampled_missing_full_cover_bound_from_witness_length_subcases
      [OF proximity index
        wp_composition_fri_sampled_full_cover_witness_length_bound_from_index_or_domain_length
        domain])
    (rule index, rule domain_length)

end

end
