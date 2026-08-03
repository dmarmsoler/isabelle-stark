(*  Title:      Stark/Soundness_FRI_Canonical_Full_Cover_Failure.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Canonical_Full_Cover_Failure
  imports Soundness_FRI_Sampled_Challenge_Cover
begin

text \<open>
  Canonical full-cover failure events for sampled-query FRI.

  The broad sampled full-cover failure predicates quantify over arbitrary
  domain witnesses.  The sampled-query split, however, produces the failure on
  the canonical FRI domains.  This layer names that narrower event so later
  bounds do not have to prove facts about unused arbitrary domain entries.
\<close>

context soundness
begin

definition trace_fri_sampled_canonical_full_cover_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_sampled_canonical_full_cover_failure s bad out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table layers.
      trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table \<and>
      generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
        trace_roots trace_bs trace_final fri_query_idxs trace_round_layers
        layers \<and>
      generic_fri_sampled_full_cover_failure trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers
        (fri_canonical_domains (length trace_bs)) layers
        (bad trace_table))"

definition composition_fri_sampled_canonical_full_cover_failure
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      ('f \<Rightarrow> 'f list \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'f set) \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_sampled_canonical_full_cover_failure s bad out
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
      generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat fri_dg))
        (Not \<circ> composition_table_low_degree maxDegree) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers layers \<and>
      generic_fri_sampled_full_cover_failure
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        (fri_canonical_domains (length composition_bs)) layers
        (bad fri_dg composition_table))"

lemma trace_fri_sampled_canonical_full_cover_failure_not_None[simp]:
  "\<not> trace_fri_sampled_canonical_full_cover_failure s bad None"
  unfolding trace_fri_sampled_canonical_full_cover_failure_def
    trace_fri_partial_candidate_opening_evidence_def
    accepted_fri_opening_transcript_def
  by simp

lemma composition_fri_sampled_canonical_full_cover_failure_not_None[simp]:
  "\<not> composition_fri_sampled_canonical_full_cover_failure s bad None"
  unfolding composition_fri_sampled_canonical_full_cover_failure_def
    composition_fri_partial_candidate_opening_evidence_def
    accepted_fri_opening_transcript_def
  by simp

lemma trace_fri_sampled_canonical_full_cover_failure_imp_broad:
  assumes "trace_fri_sampled_canonical_full_cover_failure s bad out"
  shows "trace_fri_sampled_full_cover_failure s bad out"
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
    and candidate:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
        trace_roots trace_bs trace_final fri_query_idxs trace_round_layers
        layers"
    and failure:
      "generic_fri_sampled_full_cover_failure trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers
        (fri_canonical_domains (length trace_bs)) layers
        (bad trace_table)"
    unfolding trace_fri_sampled_canonical_full_cover_failure_def by blast
  have canonical:
    "generic_fri_canonical_sampled_layer_chain_evidence trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers layers"
    by (rule generic_fri_sampled_query_candidate_evidenceD(1)[OF candidate])
  have sampled:
    "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers
      (fri_canonical_domains (length trace_bs)) layers"
    by (rule generic_fri_canonical_sampled_layer_chain_evidenceD
        [OF canonical])
  show ?thesis
    unfolding trace_fri_sampled_full_cover_failure_def
    using evidence sampled failure by blast
qed

lemma composition_fri_sampled_canonical_full_cover_failure_imp_broad:
  assumes "composition_fri_sampled_canonical_full_cover_failure s bad out"
  shows "composition_fri_sampled_full_cover_failure s bad out"
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
    and candidate:
      "generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat fri_dg))
        (Not \<circ> composition_table_low_degree maxDegree) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers layers"
    and failure:
      "generic_fri_sampled_full_cover_failure
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        (fri_canonical_domains (length composition_bs)) layers
        (bad fri_dg composition_table)"
    unfolding composition_fri_sampled_canonical_full_cover_failure_def
    by meson
  have canonical:
    "generic_fri_canonical_sampled_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers layers"
    by (rule generic_fri_sampled_query_candidate_evidenceD(1)[OF candidate])
  have sampled:
    "generic_fri_sampled_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers
      (fri_canonical_domains (length composition_bs)) layers"
    by (rule generic_fri_canonical_sampled_layer_chain_evidenceD
        [OF canonical])
  show ?thesis
    unfolding composition_fri_sampled_full_cover_failure_def
    using evidence sampled failure by meson
qed

lemma generic_fri_canonical_sampled_layer_chain_next_idx_current_bound:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length challenges"
  shows
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      length (fri_canonical_domain_at layer_idx)"
proof -
  have fold:
    "fri_sampled_table_fold (challenges ! layer_idx)
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (2 ^ layer_idx)
      (fri_canonical_domains (length challenges) ! layer_idx)
      (layers ! layer_idx)
      (round_layers ! round_idx ! layer_idx)
      (layers ! Suc layer_idx !
        fri_evidence_next_idx roots query_idxs round_idx layer_idx)"
    by (rule generic_fri_sampled_layer_chain_evidence_sample(2)
        [OF chain round_bound layer_bound])
  from fold obtain xp xp_path xn xn_path where match:
    "fri_opening_matches_table
      (fri_evidence_layer_len roots layer_idx)
      (fri_evidence_layer_idx roots query_idxs round_idx layer_idx)
      (layers ! layer_idx) xp xn"
    by (elim fri_sampled_table_foldE)
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have roots_bound: "layer_idx < length roots"
    using layer_bound roots_len by simp
  have len_eq:
    "fri_evidence_layer_len roots layer_idx =
      length (fri_canonical_domain_at layer_idx)"
    unfolding fri_evidence_layer_len_def fri_canonical_domain_at_length
    using fri_layer_lengths_nth_div[OF roots_bound, of "clength * scale"]
    by simp
  have raw_bound:
    "fri_evidence_layer_idx roots query_idxs round_idx layer_idx <
      length (fri_canonical_domain_at layer_idx)"
    using fri_opening_matches_tableD(1)[OF match] unfolding len_eq .
  show ?thesis
  proof (cases "fri_evidence_layer_len roots layer_idx div 2 = 0")
    case True
    then show ?thesis
      using raw_bound unfolding fri_evidence_next_idx_def by simp
  next
    case False
    have half_bound:
      "fri_evidence_layer_len roots layer_idx div 2 \<le>
        length (fri_canonical_domain_at layer_idx)"
      unfolding len_eq by simp
    have
      "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        fri_evidence_layer_len roots layer_idx div 2"
      unfolding fri_evidence_next_idx_def
      by (rule mod_less_divisor) (use False in simp)
    then show ?thesis
      using half_bound by linarith
  qed
qed

lemma generic_fri_canonical_sampled_layer_chain_next_idx_successor_bound:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"
    and no_shape:
      "\<not> generic_fri_full_cover_shape_failure roots challenges
        (fri_canonical_domains (length challenges)) layers"
    and round_bound: "round_idx < length query_idxs"
    and layer_bound: "layer_idx < length roots"
  shows
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      length (fri_canonical_domains (length challenges) ! Suc layer_idx)"
proof -
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have layer_challenge_bound: "layer_idx < length challenges"
    using layer_bound roots_len by simp
  have no_arith:
    "\<not> generic_fri_full_cover_arithmetic_shape_failure roots challenges"
    using no_shape
    unfolding generic_fri_full_cover_shape_failure_def
      generic_fri_full_cover_arithmetic_shape_failure_def
    by blast
  have even_len:
    "2 dvd fri_evidence_layer_len roots layer_idx"
    using no_arith layer_challenge_bound
    unfolding generic_fri_full_cover_arithmetic_shape_failure_def by blast
  have roots_bound: "layer_idx < length roots"
    by (rule layer_bound)
  have len_eq:
    "fri_evidence_layer_len roots layer_idx =
      length (fri_canonical_domain_at layer_idx)"
    unfolding fri_evidence_layer_len_def fri_canonical_domain_at_length
    using fri_layer_lengths_nth_div[OF roots_bound, of "clength * scale"]
    by simp
  have next_dom_eq:
    "fri_canonical_domains (length challenges) ! Suc layer_idx =
      fri_canonical_domain_at (Suc layer_idx)"
    by (rule fri_canonical_domains_nth)
      (use layer_challenge_bound in simp)
  have next_len:
    "length (fri_canonical_domains (length challenges) ! Suc layer_idx) =
      fri_evidence_layer_len roots layer_idx div 2"
  proof -
    have "length (fri_canonical_domains (length challenges) ! Suc layer_idx) =
        (clength * scale) div 2 ^ Suc layer_idx"
      unfolding next_dom_eq fri_canonical_domain_at_length by simp
    also have "... = ((clength * scale) div 2 ^ layer_idx) div 2"
      by (metis div_mult2_eq mult.commute power_Suc)
    also have "... = fri_evidence_layer_len roots layer_idx div 2"
      unfolding fri_evidence_layer_len_def
      using fri_layer_lengths_nth_div[OF roots_bound, of "clength * scale"]
      by simp
    finally show ?thesis .
  qed
  have raw_current:
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      length (fri_canonical_domain_at layer_idx)"
    by (rule generic_fri_canonical_sampled_layer_chain_next_idx_current_bound
        [OF chain round_bound layer_challenge_bound])
  have half_pos:
    "0 < fri_evidence_layer_len roots layer_idx div 2"
    using raw_current even_len unfolding len_eq by auto
  have
    "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
      fri_evidence_layer_len roots layer_idx div 2"
    unfolding fri_evidence_next_idx_def
    by (rule mod_less_divisor[OF half_pos])
  then show ?thesis
    unfolding next_len .
qed

lemma generic_fri_canonical_sampled_domain_failure_imp_shape:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"
    and sampled_domain:
      "generic_fri_full_cover_sampled_domain_failure roots query_idxs
        (fri_canonical_domains (length challenges))"
  shows
    "generic_fri_full_cover_shape_failure roots challenges
      (fri_canonical_domains (length challenges)) layers"
proof (rule ccontr)
  assume no_shape:
    "\<not> generic_fri_full_cover_shape_failure roots challenges
      (fri_canonical_domains (length challenges)) layers"
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have roots_bound: "length roots \<le> length challenges"
    using roots_len by simp
  have no_sampled:
    "\<not> generic_fri_full_cover_sampled_domain_failure roots query_idxs
      (fri_canonical_domains (length challenges))"
  proof (rule fri_canonical_domains_no_sampled_domain_failure
      [OF roots_bound])
    fix round_idx layer_idx
    assume round_bound: "round_idx < length query_idxs"
      and layer_bound: "layer_idx < length roots"
    show "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        length (fri_canonical_domain_at layer_idx)"
      by (rule generic_fri_canonical_sampled_layer_chain_next_idx_current_bound
          [OF chain round_bound])
        (use layer_bound roots_len in simp)
  next
    fix round_idx layer_idx
    assume round_bound: "round_idx < length query_idxs"
      and layer_bound: "layer_idx < length roots"
    show "fri_evidence_next_idx roots query_idxs round_idx layer_idx <
        length (fri_canonical_domains (length challenges) ! Suc layer_idx)"
      by (rule
          generic_fri_canonical_sampled_layer_chain_next_idx_successor_bound
          [OF chain no_shape round_bound layer_bound])
  qed
  show False
    using sampled_domain no_sampled by contradiction
qed

lemma generic_fri_canonical_domain_failure_imp_index_or_shape:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence low_degree candidate_table
      degree_bound roots challenges final_value query_idxs round_layers
      (fri_canonical_domains (length challenges)) layers"
    and domain:
      "generic_fri_full_cover_domain_failure roots challenges
        (fri_canonical_domains (length challenges))"
  shows
    "generic_fri_full_cover_index_failure roots query_idxs \<or>
     generic_fri_full_cover_shape_failure roots challenges
      (fri_canonical_domains (length challenges)) layers"
proof (cases "generic_fri_full_cover_index_failure roots query_idxs")
  case True
  then show ?thesis by simp
next
  case no_index: False
  have partial:
    "generic_fri_partial_evidence low_degree candidate_table degree_bound
      roots challenges final_value query_idxs round_layers"
    by (rule generic_fri_sampled_layer_chain_evidenceD(1)[OF chain])
  have roots_len: "length challenges = length roots"
    by (rule generic_fri_partial_evidence_shapes(2)[OF partial])
  have sampled_domain:
    "generic_fri_full_cover_sampled_domain_failure roots query_idxs
      (fri_canonical_domains (length challenges))"
    using generic_fri_full_cover_domain_failure_imp_index_or_sampled_domain
        [OF roots_len domain, of query_idxs] no_index
    by blast
  then have shape:
    "generic_fri_full_cover_shape_failure roots challenges
      (fri_canonical_domains (length challenges)) layers"
    by (rule generic_fri_canonical_sampled_domain_failure_imp_shape
        [OF chain])
  then show ?thesis by simp
qed

lemma trace_fri_sampled_canonical_full_cover_failure_split_no_domain:
  assumes "trace_fri_sampled_canonical_full_cover_failure s bad out"
  shows
    "trace_fri_sampled_full_cover_proximity_failure s bad out \<or>
     trace_fri_sampled_full_cover_index_failure s out \<or>
     trace_fri_sampled_full_cover_shape_failure s out \<or>
     trace_fri_sampled_full_cover_start_low_failure s out"
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
    and candidate:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
        trace_roots trace_bs trace_final fri_query_idxs trace_round_layers
        layers"
    and failure:
      "generic_fri_sampled_full_cover_failure trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers
        (fri_canonical_domains (length trace_bs)) layers
        (bad trace_table)"
    unfolding trace_fri_sampled_canonical_full_cover_failure_def by blast
  have canonical:
    "generic_fri_canonical_sampled_layer_chain_evidence
      trace_table_low_degree trace_table (clength - 1) trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers layers"
    by (rule generic_fri_sampled_query_candidate_evidenceD(1)
        [OF candidate])
  have chain:
    "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers
      (fri_canonical_domains (length trace_bs)) layers"
    by (rule generic_fri_canonical_sampled_layer_chain_evidenceD
        [OF canonical])
  have cases:
    "generic_fri_full_cover_proximity_failure (clength - 1) trace_bs
      (fri_canonical_domains (length trace_bs)) layers
      (bad trace_table) \<or>
     generic_fri_full_cover_index_failure trace_roots fri_query_idxs \<or>
     generic_fri_full_cover_shape_failure trace_roots trace_bs
      (fri_canonical_domains (length trace_bs)) layers \<or>
     generic_fri_full_cover_domain_failure trace_roots trace_bs
      (fri_canonical_domains (length trace_bs)) \<or>
     generic_fri_full_cover_start_low_failure (clength - 1)
      trace_table \<or>
     generic_fri_full_cover_final_low_failure (clength - 1) trace_bs
      (fri_canonical_domains (length trace_bs)) layers"
    by (rule generic_fri_sampled_full_cover_failure_cases[OF failure])
  from cases show ?thesis
  proof
    assume proximity:
      "generic_fri_full_cover_proximity_failure (clength - 1) trace_bs
        (fri_canonical_domains (length trace_bs)) layers
        (bad trace_table)"
    then show ?thesis
      unfolding trace_fri_sampled_full_cover_proximity_failure_def
      using evidence chain by blast
  next
    assume rest:
      "generic_fri_full_cover_index_failure trace_roots fri_query_idxs \<or>
       generic_fri_full_cover_shape_failure trace_roots trace_bs
        (fri_canonical_domains (length trace_bs)) layers \<or>
       generic_fri_full_cover_domain_failure trace_roots trace_bs
        (fri_canonical_domains (length trace_bs)) \<or>
       generic_fri_full_cover_start_low_failure (clength - 1)
        trace_table \<or>
       generic_fri_full_cover_final_low_failure (clength - 1) trace_bs
        (fri_canonical_domains (length trace_bs)) layers"
    then show ?thesis
    proof
      assume index:
        "generic_fri_full_cover_index_failure trace_roots fri_query_idxs"
      then show ?thesis
        unfolding trace_fri_sampled_full_cover_index_failure_def
        using evidence chain by blast
    next
      assume rest':
        "generic_fri_full_cover_shape_failure trace_roots trace_bs
          (fri_canonical_domains (length trace_bs)) layers \<or>
         generic_fri_full_cover_domain_failure trace_roots trace_bs
          (fri_canonical_domains (length trace_bs)) \<or>
         generic_fri_full_cover_start_low_failure (clength - 1)
          trace_table \<or>
         generic_fri_full_cover_final_low_failure (clength - 1) trace_bs
          (fri_canonical_domains (length trace_bs)) layers"
      then show ?thesis
      proof
        assume shape:
          "generic_fri_full_cover_shape_failure trace_roots trace_bs
            (fri_canonical_domains (length trace_bs)) layers"
        then show ?thesis
          unfolding trace_fri_sampled_full_cover_shape_failure_def
          using evidence chain by blast
      next
        assume rest'':
          "generic_fri_full_cover_domain_failure trace_roots trace_bs
            (fri_canonical_domains (length trace_bs)) \<or>
           generic_fri_full_cover_start_low_failure (clength - 1)
            trace_table \<or>
           generic_fri_full_cover_final_low_failure (clength - 1)
            trace_bs (fri_canonical_domains (length trace_bs)) layers"
        then show ?thesis
        proof
          assume domain:
            "generic_fri_full_cover_domain_failure trace_roots trace_bs
              (fri_canonical_domains (length trace_bs))"
          have index_or_shape:
            "generic_fri_full_cover_index_failure trace_roots
              fri_query_idxs \<or>
             generic_fri_full_cover_shape_failure trace_roots trace_bs
              (fri_canonical_domains (length trace_bs)) layers"
            by (rule generic_fri_canonical_domain_failure_imp_index_or_shape
                [OF chain domain])
          then show ?thesis
          proof
            assume "generic_fri_full_cover_index_failure trace_roots
                fri_query_idxs"
            then show ?thesis
              unfolding trace_fri_sampled_full_cover_index_failure_def
              using evidence chain by blast
          next
            assume "generic_fri_full_cover_shape_failure trace_roots
                trace_bs (fri_canonical_domains (length trace_bs)) layers"
            then show ?thesis
              unfolding trace_fri_sampled_full_cover_shape_failure_def
              using evidence chain by blast
          qed
        next
          assume rest''':
            "generic_fri_full_cover_start_low_failure (clength - 1)
              trace_table \<or>
             generic_fri_full_cover_final_low_failure (clength - 1)
              trace_bs (fri_canonical_domains (length trace_bs)) layers"
          then show ?thesis
          proof
            assume start:
              "generic_fri_full_cover_start_low_failure (clength - 1)
                trace_table"
            then show ?thesis
              unfolding trace_fri_sampled_full_cover_start_low_failure_def
              using evidence chain by blast
          next
            assume final:
              "generic_fri_full_cover_final_low_failure (clength - 1)
                trace_bs (fri_canonical_domains (length trace_bs)) layers"
            have final_event:
              "trace_fri_sampled_full_cover_final_low_failure s out"
              unfolding trace_fri_sampled_full_cover_final_low_failure_def
              using evidence chain final by blast
            then have shape_event:
              "trace_fri_sampled_full_cover_shape_failure s out"
              by (rule trace_fri_sampled_full_cover_final_low_imp_shape)
            then show ?thesis by simp
          qed
        qed
      qed
    qed
  qed
qed

lemma composition_fri_sampled_canonical_full_cover_failure_split_no_domain:
  assumes "composition_fri_sampled_canonical_full_cover_failure s bad out"
  shows
    "composition_fri_sampled_full_cover_proximity_failure s bad out \<or>
     composition_fri_sampled_full_cover_index_failure s out \<or>
     composition_fri_sampled_full_cover_shape_failure s out \<or>
     composition_fri_sampled_full_cover_start_low_failure s out"
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
    and candidate:
      "generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat fri_dg))
        (Not \<circ> composition_table_low_degree maxDegree) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers layers"
    and failure:
      "generic_fri_sampled_full_cover_failure
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        (fri_canonical_domains (length composition_bs)) layers
        (bad fri_dg composition_table)"
    unfolding composition_fri_sampled_canonical_full_cover_failure_def
    by meson
  have canonical:
    "generic_fri_canonical_sampled_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers layers"
    by (rule generic_fri_sampled_query_candidate_evidenceD(1)
        [OF candidate])
  have chain:
    "generic_fri_sampled_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) opening_composition_roots composition_bs
      composition_final fri_query_idxs composition_round_layers
      (fri_canonical_domains (length composition_bs)) layers"
    by (rule generic_fri_canonical_sampled_layer_chain_evidenceD
        [OF canonical])
  have cases:
    "generic_fri_full_cover_proximity_failure (to_nat fri_dg)
      composition_bs (fri_canonical_domains (length composition_bs))
      layers (bad fri_dg composition_table) \<or>
     generic_fri_full_cover_index_failure opening_composition_roots
      fri_query_idxs \<or>
     generic_fri_full_cover_shape_failure opening_composition_roots
      composition_bs (fri_canonical_domains (length composition_bs))
      layers \<or>
     generic_fri_full_cover_domain_failure opening_composition_roots
      composition_bs (fri_canonical_domains (length composition_bs)) \<or>
     generic_fri_full_cover_start_low_failure (to_nat fri_dg)
      composition_table \<or>
     generic_fri_full_cover_final_low_failure (to_nat fri_dg) composition_bs
      (fri_canonical_domains (length composition_bs)) layers"
    by (rule generic_fri_sampled_full_cover_failure_cases[OF failure])
  from cases show ?thesis
  proof
    assume proximity:
      "generic_fri_full_cover_proximity_failure (to_nat fri_dg)
        composition_bs (fri_canonical_domains (length composition_bs))
        layers (bad fri_dg composition_table)"
    then show ?thesis
      unfolding composition_fri_sampled_full_cover_proximity_failure_def
      using evidence chain by meson
  next
    assume rest:
      "generic_fri_full_cover_index_failure opening_composition_roots
        fri_query_idxs \<or>
       generic_fri_full_cover_shape_failure opening_composition_roots
        composition_bs (fri_canonical_domains (length composition_bs))
        layers \<or>
       generic_fri_full_cover_domain_failure opening_composition_roots
        composition_bs (fri_canonical_domains (length composition_bs)) \<or>
       generic_fri_full_cover_start_low_failure (to_nat fri_dg)
        composition_table \<or>
       generic_fri_full_cover_final_low_failure (to_nat fri_dg)
        composition_bs (fri_canonical_domains (length composition_bs))
        layers"
    then show ?thesis
    proof
      assume index:
        "generic_fri_full_cover_index_failure opening_composition_roots
          fri_query_idxs"
      then show ?thesis
        unfolding composition_fri_sampled_full_cover_index_failure_def
        using evidence chain by meson
    next
      assume rest':
        "generic_fri_full_cover_shape_failure opening_composition_roots
          composition_bs (fri_canonical_domains (length composition_bs))
          layers \<or>
         generic_fri_full_cover_domain_failure opening_composition_roots
          composition_bs (fri_canonical_domains (length composition_bs)) \<or>
         generic_fri_full_cover_start_low_failure (to_nat fri_dg)
          composition_table \<or>
         generic_fri_full_cover_final_low_failure (to_nat fri_dg)
          composition_bs (fri_canonical_domains (length composition_bs))
          layers"
      then show ?thesis
      proof
        assume shape:
          "generic_fri_full_cover_shape_failure opening_composition_roots
            composition_bs (fri_canonical_domains (length composition_bs))
            layers"
        then show ?thesis
          unfolding composition_fri_sampled_full_cover_shape_failure_def
          using evidence chain by meson
      next
        assume rest'':
          "generic_fri_full_cover_domain_failure opening_composition_roots
            composition_bs (fri_canonical_domains (length composition_bs)) \<or>
           generic_fri_full_cover_start_low_failure (to_nat fri_dg)
            composition_table \<or>
           generic_fri_full_cover_final_low_failure (to_nat fri_dg)
            composition_bs (fri_canonical_domains (length composition_bs))
            layers"
        then show ?thesis
        proof
          assume domain:
            "generic_fri_full_cover_domain_failure opening_composition_roots
              composition_bs (fri_canonical_domains (length composition_bs))"
          have index_or_shape:
            "generic_fri_full_cover_index_failure opening_composition_roots
              fri_query_idxs \<or>
             generic_fri_full_cover_shape_failure opening_composition_roots
              composition_bs (fri_canonical_domains (length composition_bs))
              layers"
            by (rule generic_fri_canonical_domain_failure_imp_index_or_shape
                [OF chain domain])
          then show ?thesis
          proof
            assume "generic_fri_full_cover_index_failure
                opening_composition_roots fri_query_idxs"
            then show ?thesis
              unfolding composition_fri_sampled_full_cover_index_failure_def
              using evidence chain by meson
          next
            assume "generic_fri_full_cover_shape_failure
                opening_composition_roots composition_bs
                (fri_canonical_domains (length composition_bs)) layers"
            then show ?thesis
              unfolding composition_fri_sampled_full_cover_shape_failure_def
              using evidence chain by meson
          qed
        next
          assume rest''':
            "generic_fri_full_cover_start_low_failure (to_nat fri_dg)
              composition_table \<or>
             generic_fri_full_cover_final_low_failure (to_nat fri_dg)
              composition_bs (fri_canonical_domains (length composition_bs))
              layers"
          then show ?thesis
          proof
            assume start:
              "generic_fri_full_cover_start_low_failure (to_nat fri_dg)
                composition_table"
            then show ?thesis
              unfolding
                composition_fri_sampled_full_cover_start_low_failure_def
              using evidence chain by meson
          next
            assume final:
              "generic_fri_full_cover_final_low_failure (to_nat fri_dg)
                composition_bs (fri_canonical_domains (length composition_bs))
                layers"
            have final_event:
              "composition_fri_sampled_full_cover_final_low_failure s out"
              unfolding
                composition_fri_sampled_full_cover_final_low_failure_def
              using evidence chain final by meson
            then have shape_event:
              "composition_fri_sampled_full_cover_shape_failure s out"
              by (rule composition_fri_sampled_full_cover_final_low_imp_shape)
            then show ?thesis by simp
          qed
        qed
      qed
    qed
  qed
qed

lemma wp_trace_fri_sampled_canonical_full_cover_failure_bound_from_shape_subcases:
  assumes proximity:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_canonical_full_cover_failure s bad) s
      \<le> P + I + Sh"
proof -
  have "wp_event verify_monad
      (trace_fri_sampled_canonical_full_cover_failure s bad) s
    \<le> wp_event verify_monad
      (\<lambda>out.
        trace_fri_sampled_full_cover_proximity_failure s bad out \<or>
        trace_fri_sampled_full_cover_index_failure s out \<or>
        trace_fri_sampled_full_cover_shape_failure s out \<or>
        trace_fri_sampled_full_cover_start_low_failure s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_sampled_canonical_full_cover_failure_split_no_domain)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure s bad) s +
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure s) s +
      wp_event verify_monad
        (trace_fri_sampled_full_cover_shape_failure s) s +
      wp_event verify_monad
        (trace_fri_sampled_full_cover_start_low_failure s) s"
    by (rule wp_event_union_bound4)
  also have "... \<le> P + I + Sh + 0"
    using proximity index shape
      wp_trace_fri_sampled_full_cover_start_low_failure_zero[of s]
    by (intro add_mono)
  finally show ?thesis
    by simp
qed

lemma wp_composition_fri_sampled_canonical_full_cover_failure_bound_from_shape_subcases:
  assumes proximity:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and shape:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_shape_failure s) s \<le> Sh"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_canonical_full_cover_failure s bad) s
      \<le> P + I + Sh"
proof -
  have "wp_event verify_monad
      (composition_fri_sampled_canonical_full_cover_failure s bad) s
    \<le> wp_event verify_monad
      (\<lambda>out.
        composition_fri_sampled_full_cover_proximity_failure s bad out \<or>
        composition_fri_sampled_full_cover_index_failure s out \<or>
        composition_fri_sampled_full_cover_shape_failure s out \<or>
        composition_fri_sampled_full_cover_start_low_failure s out) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_sampled_canonical_full_cover_failure_split_no_domain)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure s bad) s +
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure s) s +
      wp_event verify_monad
        (composition_fri_sampled_full_cover_shape_failure s) s +
      wp_event verify_monad
        (composition_fri_sampled_full_cover_start_low_failure s) s"
    by (rule wp_event_union_bound4)
  also have "... \<le> P + I + Sh + 0"
    using proximity index shape
      wp_composition_fri_sampled_full_cover_start_low_failure_zero[of s]
    by (intro add_mono)
  finally show ?thesis
    by simp
qed

lemma wp_trace_fri_sampled_canonical_full_cover_failure_bound_from_witness_shape:
  assumes proximity:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_index_failure s) s \<le> I"
    and witness:
    "wp_event verify_monad
      (trace_fri_sampled_full_cover_witness_length_failure s) s \<le> W"
  shows
    "wp_event verify_monad
      (trace_fri_sampled_canonical_full_cover_failure s bad) s
      \<le> P + I + W"
  by (rule
      wp_trace_fri_sampled_canonical_full_cover_failure_bound_from_shape_subcases
      [OF proximity index])
    (rule wp_trace_fri_sampled_full_cover_shape_bound_from_witness_length
      [OF witness])

lemma wp_composition_fri_sampled_canonical_full_cover_failure_bound_from_witness_shape:
  assumes proximity:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_proximity_failure s bad) s \<le> P"
    and index:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_index_failure s) s \<le> I"
    and witness:
    "wp_event verify_monad
      (composition_fri_sampled_full_cover_witness_length_failure s) s
      \<le> W"
  shows
    "wp_event verify_monad
      (composition_fri_sampled_canonical_full_cover_failure s bad) s
      \<le> P + I + W"
  by (rule
      wp_composition_fri_sampled_canonical_full_cover_failure_bound_from_shape_subcases
      [OF proximity index])
    (rule
      wp_composition_fri_sampled_full_cover_shape_bound_from_witness_length
      [OF witness])

lemma checked_staged_security_trace_fri_sampled_canonical_full_cover_failure_bound_from_shape_subcases:
  assumes proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and shape:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_shape_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Sh"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_canonical_full_cover_failure s bad))
      adversary_initial_state \<le> P + I + Sh"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show
    "\<And>s. \<not> trace_fri_sampled_canonical_full_cover_failure s bad None"
    by simp
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (trace_fri_sampled_canonical_full_cover_failure ?s bad) ?s
      \<le> P + I + Sh"
    by (rule
        wp_trace_fri_sampled_canonical_full_cover_failure_bound_from_shape_subcases)
      (rule proximity[OF support], rule index[OF support],
       rule shape[OF support])
qed

lemma checked_staged_security_trace_fri_sampled_canonical_full_cover_failure_bound_from_witness_shape:
  assumes proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and witness:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (trace_fri_sampled_full_cover_witness_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> W"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_canonical_full_cover_failure s bad))
      adversary_initial_state \<le> P + I + W"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show
    "\<And>s. \<not> trace_fri_sampled_canonical_full_cover_failure s bad None"
    by simp
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (trace_fri_sampled_canonical_full_cover_failure ?s bad) ?s
      \<le> P + I + W"
    by (rule
        wp_trace_fri_sampled_canonical_full_cover_failure_bound_from_witness_shape)
      (rule proximity[OF support], rule index[OF support],
       rule witness[OF support])
qed

lemma checked_staged_security_composition_fri_sampled_canonical_full_cover_failure_bound_from_shape_subcases:
  assumes proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and shape:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_shape_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> Sh"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_canonical_full_cover_failure s bad))
      adversary_initial_state \<le> P + I + Sh"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show
    "\<And>s. \<not> composition_fri_sampled_canonical_full_cover_failure s bad
      None"
    by simp
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (composition_fri_sampled_canonical_full_cover_failure ?s bad) ?s
      \<le> P + I + Sh"
    by (rule
        wp_composition_fri_sampled_canonical_full_cover_failure_bound_from_shape_subcases)
      (rule proximity[OF support], rule index[OF support],
       rule shape[OF support])
qed

lemma checked_staged_security_composition_fri_sampled_canonical_full_cover_failure_bound_from_witness_shape:
  assumes proximity:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_proximity_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)) bad)
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> P"
    and index:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_index_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> I"
    and witness:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      wp_event verify_monad
        (composition_fri_sampled_full_cover_witness_length_failure
          (verifier_state_from_adversary attacker_state
            (staged_proof_transcript data)))
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data)) \<le> W"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_canonical_full_cover_failure s bad))
      adversary_initial_state \<le> P + I + W"
proof (rule checked_staged_security_with_data_state_verifier_event_bound_from_cont)
  show
    "\<And>s. \<not> composition_fri_sampled_canonical_full_cover_failure s bad
      None"
    by simp
next
  fix data attacker_state
  assume support:
    "Some (data, attacker_state) \<in>
      set_dist (execute (checked_staged_transcript_program A)
        adversary_initial_state)"
  let ?s =
    "verifier_state_from_adversary attacker_state
      (staged_proof_transcript data)"
  show "wp_event verify_monad
      (composition_fri_sampled_canonical_full_cover_failure ?s bad) ?s
      \<le> P + I + W"
    by (rule
        wp_composition_fri_sampled_canonical_full_cover_failure_bound_from_witness_shape)
      (rule proximity[OF support], rule index[OF support],
       rule witness[OF support])
qed

lemma trace_fri_sampled_query_bad_candidate_imp_no_full_cover_or_canonical_failure:
  assumes sampled: "trace_fri_sampled_query_bad_candidate s out"
  shows
    "trace_fri_sampled_query_no_full_cover_failure_candidate s bad out \<or>
     trace_fri_sampled_canonical_full_cover_failure s bad out"
proof -
  from sampled obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table layers
    where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr candidate_query_idxs trace_openings
        trace_table"
    and candidate:
      "generic_fri_sampled_query_candidate_evidence trace_table_low_degree
        (Not \<circ> trace_table_low_degree) trace_table (clength - 1)
        trace_roots trace_bs trace_final fri_query_idxs trace_round_layers
        layers"
    unfolding trace_fri_sampled_query_bad_candidate_def by blast
  show ?thesis
  proof (cases
      "generic_fri_sampled_full_cover_failure trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers
        (fri_canonical_domains (length trace_bs)) layers
        (bad trace_table)")
    case False
    then have
      "trace_fri_sampled_query_no_full_cover_failure_candidate s bad out"
      unfolding trace_fri_sampled_query_no_full_cover_failure_candidate_def
      using evidence candidate by blast
    then show ?thesis by simp
  next
    case True
    then have
      "trace_fri_sampled_canonical_full_cover_failure s bad out"
      unfolding trace_fri_sampled_canonical_full_cover_failure_def
      using evidence candidate by blast
    then show ?thesis by simp
  qed
qed

lemma composition_fri_sampled_query_bad_candidate_imp_no_full_cover_or_canonical_failure:
  assumes sampled: "composition_fri_sampled_query_bad_candidate s out"
  shows
    "composition_fri_sampled_query_no_full_cover_failure_candidate s bad out \<or>
     composition_fri_sampled_canonical_full_cover_failure s bad out"
proof -
  from sampled obtain trace_roots trace_bs trace_final fri_dg
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
    and candidate:
      "generic_fri_sampled_query_candidate_evidence
        (composition_table_low_degree (to_nat fri_dg))
        (Not \<circ> composition_table_low_degree maxDegree) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers layers"
    unfolding composition_fri_sampled_query_bad_candidate_def by meson
  show ?thesis
  proof (cases
      "generic_fri_sampled_full_cover_failure
        (composition_table_low_degree (to_nat fri_dg)) composition_table
        (to_nat fri_dg) opening_composition_roots composition_bs
        composition_final fri_query_idxs composition_round_layers
        (fri_canonical_domains (length composition_bs)) layers
        (bad fri_dg composition_table)")
    case False
    then have
      "composition_fri_sampled_query_no_full_cover_failure_candidate s bad out"
      unfolding
        composition_fri_sampled_query_no_full_cover_failure_candidate_def
      using evidence candidate by meson
    then show ?thesis by simp
  next
    case True
    then have
      "composition_fri_sampled_canonical_full_cover_failure s bad out"
      unfolding composition_fri_sampled_canonical_full_cover_failure_def
      using evidence candidate by meson
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_sampled_query_bad_candidate_bound_from_no_full_cover_or_canonical_failure:
  assumes no_failure_bound:
    "wp_event verify_monad
      (trace_fri_sampled_query_no_full_cover_failure_candidate s bad) s
      \<le> N"
    and failure_bound:
      "wp_event verify_monad
        (trace_fri_sampled_canonical_full_cover_failure s bad) s \<le> F"
  shows
    "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le> N + F"
proof -
  have "wp_event verify_monad (trace_fri_sampled_query_bad_candidate s) s
      \<le> wp_event verify_monad
        (\<lambda>out.
          trace_fri_sampled_query_no_full_cover_failure_candidate s bad out \<or>
          trace_fri_sampled_canonical_full_cover_failure s bad out) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_sampled_query_bad_candidate_imp_no_full_cover_or_canonical_failure)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_sampled_query_no_full_cover_failure_candidate s bad) s +
      wp_event verify_monad
        (trace_fri_sampled_canonical_full_cover_failure s bad) s"
    by (rule wp_event_union_bound)
  also have "... \<le> N + F"
    by (rule add_mono[OF no_failure_bound failure_bound])
  finally show ?thesis .
qed

lemma wp_composition_fri_sampled_query_bad_candidate_bound_from_no_full_cover_or_canonical_failure:
  assumes no_failure_bound:
    "wp_event verify_monad
      (composition_fri_sampled_query_no_full_cover_failure_candidate s bad) s
      \<le> N"
    and failure_bound:
      "wp_event verify_monad
        (composition_fri_sampled_canonical_full_cover_failure s bad) s \<le> F"
  shows
    "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s
      \<le> N + F"
proof -
  have "wp_event verify_monad (composition_fri_sampled_query_bad_candidate s) s
      \<le> wp_event verify_monad
        (\<lambda>out.
          composition_fri_sampled_query_no_full_cover_failure_candidate s bad
            out \<or>
          composition_fri_sampled_canonical_full_cover_failure s bad out) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_sampled_query_bad_candidate_imp_no_full_cover_or_canonical_failure)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_sampled_query_no_full_cover_failure_candidate s bad)
        s +
      wp_event verify_monad
        (composition_fri_sampled_canonical_full_cover_failure s bad) s"
    by (rule wp_event_union_bound)
  also have "... \<le> N + F"
    by (rule add_mono[OF no_failure_bound failure_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_trace_fri_sampled_query_bad_candidate_bound_from_no_full_cover_or_canonical_failure:
  assumes no_failure_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_query_no_full_cover_failure_candidate s bad))
      adversary_initial_state \<le> N"
    and failure_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_canonical_full_cover_failure s bad))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> N + F"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        trace_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_sampled_query_no_full_cover_failure_candidate s
            bad) out \<or>
        staged_security_with_data_state_verifier_event
          (\<lambda>s. trace_fri_sampled_canonical_full_cover_failure s bad) out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest:
          trace_fri_sampled_query_bad_candidate_imp_no_full_cover_or_canonical_failure
        split: option.splits prod.splits)
  also have "... \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_query_no_full_cover_failure_candidate s bad))
      adversary_initial_state +
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. trace_fri_sampled_canonical_full_cover_failure s bad))
      adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> N + F"
    by (rule add_mono[OF no_failure_bound failure_bound])
  finally show ?thesis .
qed

lemma checked_staged_security_composition_fri_sampled_query_bad_candidate_bound_from_no_full_cover_or_canonical_failure:
  assumes no_failure_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          composition_fri_sampled_query_no_full_cover_failure_candidate s
            bad))
      adversary_initial_state \<le> N"
    and failure_bound:
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_canonical_full_cover_failure s bad))
      adversary_initial_state \<le> F"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le> N + F"
proof -
  have "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_sampled_query_bad_candidate)
      adversary_initial_state \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (\<lambda>out.
        staged_security_with_data_state_verifier_event
          (\<lambda>s.
            composition_fri_sampled_query_no_full_cover_failure_candidate s
              bad) out \<or>
        staged_security_with_data_state_verifier_event
          (\<lambda>s. composition_fri_sampled_canonical_full_cover_failure s bad)
          out)
      adversary_initial_state"
    by (rule wp_event_mono)
      (auto simp: staged_security_with_data_state_verifier_event_def
        dest:
          composition_fri_sampled_query_bad_candidate_imp_no_full_cover_or_canonical_failure
        split: option.splits prod.splits)
  also have "... \<le>
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s.
          composition_fri_sampled_query_no_full_cover_failure_candidate s
            bad))
      adversary_initial_state +
    wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        (\<lambda>s. composition_fri_sampled_canonical_full_cover_failure s bad))
      adversary_initial_state"
    by (rule wp_event_union_bound)
  also have "... \<le> N + F"
    by (rule add_mono[OF no_failure_bound failure_bound])
  finally show ?thesis .
qed

end

end
