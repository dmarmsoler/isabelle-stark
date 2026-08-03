(*  Title:      Stark/Soundness_FRI_Trace_Sibling_Evidence.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Trace_Sibling_Evidence
  imports Soundness_FRI_Value_Aligned_Events
begin

text \<open>
  Proof-only refinement of the trace FRI sibling mismatch branch.

  The existing trace candidate predicate records agreement with the trace-query
  openings only.  The first trace FRI sibling value is read from the FRI layer
  transcript, so the sibling branch cannot be closed from the current candidate
  predicate alone.  This theory isolates the exact missing evidence: a trace
  candidate must also agree with the recorded first-layer FRI sibling values.
\<close>

context soundness
begin

definition trace_table_agrees_with_recorded_first_fri_siblings
  :: "'f list \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow>
      'f list list list \<Rightarrow> bool"
where
  "trace_table_agrees_with_recorded_first_fri_siblings trace_table
      trace_roots trace_bs query_idxs trace_round_layers \<longleftrightarrow>
    (\<forall>round_idx xp xp_path xn xn_path.
      round_idx < length query_idxs \<longrightarrow>
      0 < length trace_roots \<longrightarrow>
      0 < length trace_bs \<longrightarrow>
      fri_layer_step_evidence
        (trace_roots ! 0)
        (trace_bs ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots query_idxs round_idx 0)
        (fri_evidence_next_value trace_roots trace_bs query_idxs
          round_idx 0 xp xn)
        (trace_round_layers ! round_idx ! 0) \<longrightarrow>
      trace_table !
        fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots query_idxs round_idx 0) =
        xn)"

definition partial_trace_table_candidate_with_recorded_first_fri_siblings
  :: "'f list \<Rightarrow> 'f authenticated_opening list list \<Rightarrow>
      'f list \<Rightarrow> 'f list \<Rightarrow> nat list \<Rightarrow> 'f list list list \<Rightarrow>
      bool"
where
  "partial_trace_table_candidate_with_recorded_first_fri_siblings
      trace_table trace_openings trace_roots trace_bs query_idxs
      trace_round_layers \<longleftrightarrow>
    partial_trace_table_candidate trace_table trace_openings \<and>
    trace_table_agrees_with_recorded_first_fri_siblings trace_table
      trace_roots trace_bs query_idxs trace_round_layers"

lemma partial_trace_table_candidate_with_recorded_first_fri_siblingsD:
  assumes
    "partial_trace_table_candidate_with_recorded_first_fri_siblings
      trace_table trace_openings trace_roots trace_bs query_idxs
      trace_round_layers"
  shows "partial_trace_table_candidate trace_table trace_openings"
    and "trace_table_agrees_with_recorded_first_fri_siblings trace_table
      trace_roots trace_bs query_idxs trace_round_layers"
  using assms
  unfolding partial_trace_table_candidate_with_recorded_first_fri_siblings_def
  by blast+

definition trace_fri_header_tied_recorded_sibling_candidate_mismatch
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_recorded_sibling_candidate_mismatch s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        round_idx xp xp_path xn xn_path result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      trace_table_agrees_with_recorded_first_fri_siblings trace_table
        trace_roots trace_bs fri_query_idxs trace_round_layers \<and>
      \<not> trace_table_low_degree trace_table \<and>
      round_idx < length fri_query_idxs \<and>
      0 < length trace_bs \<and>
      trace_openings ! round_idx \<noteq> [] \<and>
      opening_index (hd (trace_openings ! round_idx)) =
        fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0 \<and>
      opening_value (hd (trace_openings ! round_idx)) = xp \<and>
      fri_layer_step_evidence
        (trace_roots ! 0)
        (trace_bs ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
          round_idx 0 xp xn)
        (trace_round_layers ! round_idx ! 0) \<and>
      trace_table !
        fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        \<noteq> xn)"

definition trace_fri_header_tied_recorded_sibling_candidate_missing
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_recorded_sibling_candidate_missing s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        round_idx xp xp_path xn xn_path result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      \<not> trace_table_agrees_with_recorded_first_fri_siblings trace_table
        trace_roots trace_bs fri_query_idxs trace_round_layers \<and>
      \<not> trace_table_low_degree trace_table \<and>
      round_idx < length fri_query_idxs \<and>
      0 < length trace_bs \<and>
      trace_openings ! round_idx \<noteq> [] \<and>
      opening_index (hd (trace_openings ! round_idx)) =
        fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0 \<and>
      opening_value (hd (trace_openings ! round_idx)) = xp \<and>
      fri_layer_step_evidence
        (trace_roots ! 0)
        (trace_bs ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
          round_idx 0 xp xn)
        (trace_round_layers ! round_idx ! 0) \<and>
      trace_table !
        fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        \<noteq> xn)"

lemma generic_trace_sampled_layer_chain_evidence_recorded_first_sibling_agreement:
  assumes chain:
    "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers doms layers"
  shows
    "trace_table_agrees_with_recorded_first_fri_siblings trace_table
      trace_roots trace_bs fri_query_idxs trace_round_layers"
proof (unfold trace_table_agrees_with_recorded_first_fri_siblings_def,
    intro allI impI)
  fix round_idx xp xp_path xn xn_path
  assume round_bound: "round_idx < length fri_query_idxs"
    and roots_nonempty: "0 < length trace_roots"
    and challenges_nonempty: "0 < length trace_bs"
    and step:
      "fri_layer_step_evidence
        (trace_roots ! 0)
        (trace_bs ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
          round_idx 0 xp xn)
        (trace_round_layers ! round_idx ! 0)"
  have layer0: "layers ! 0 = trace_table"
    by (rule generic_fri_sampled_layer_chain_evidenceD(5)[OF chain])
  have sampled:
    "fri_sampled_table_fold
      (trace_bs ! 0)
      (fri_evidence_layer_len trace_roots 0)
      (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
      (2 ^ 0)
      (doms ! 0)
      (layers ! 0)
      (trace_round_layers ! round_idx ! 0)
      (layers ! Suc 0 !
        fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)"
    by (rule generic_fri_sampled_layer_chain_evidence_sample(2)
        [OF chain round_bound challenges_nonempty])
  from sampled obtain yp yp_path yn yn_path
    where chunk:
      "fri_layer_opening_chunk (fri_evidence_layer_len trace_roots 0)
        yp yp_path yn yn_path (trace_round_layers ! round_idx ! 0)"
    and match:
      "fri_opening_matches_table (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        (layers ! 0) yp yn"
    by (elim fri_sampled_table_foldE)
  have step_chunk:
    "fri_layer_opening_chunk (fri_evidence_layer_len trace_roots 0)
      xp xp_path xn xn_path (trace_round_layers ! round_idx ! 0)"
    by (rule fri_layer_step_evidenceD(4)[OF step])
  have yn_eq: "yn = xn"
    using fri_layer_opening_chunk_values_unique(2)[OF chunk step_chunk]
    by simp
  have "(layers ! 0) !
      fri_sibling_index (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0) =
      yn"
    by (rule fri_opening_matches_tableD(4)[OF match])
  then show
    "trace_table !
      fri_sibling_index (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0) =
      xn"
    using layer0 yn_eq by simp
qed

lemma generic_trace_sampled_layer_chain_evidence_augments_partial_trace_candidate:
  assumes cand: "partial_trace_table_candidate trace_table trace_openings"
    and chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        query_idxs trace_round_layers doms layers"
  shows
    "partial_trace_table_candidate_with_recorded_first_fri_siblings
      trace_table trace_openings trace_roots trace_bs query_idxs
      trace_round_layers"
  unfolding partial_trace_table_candidate_with_recorded_first_fri_siblings_def
  by (intro conjI cand
      generic_trace_sampled_layer_chain_evidence_recorded_first_sibling_agreement
      [OF chain])

definition trace_fri_bad_with_header_tied_augmented_partial_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_header_tied_augmented_partial_candidate s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate_with_recorded_first_fri_siblings
        trace_table trace_openings trace_roots trace_bs fri_query_idxs
        trace_round_layers \<and>
      \<not> trace_table_low_degree trace_table)"

definition trace_fri_bad_with_header_tied_augmented_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        doms layers.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate_with_recorded_first_fri_siblings
        trace_table trace_openings trace_roots trace_bs fri_query_idxs
        trace_round_layers \<and>
      \<not> trace_table_low_degree trace_table \<and>
      generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers)"

definition trace_fri_header_tied_augmented_missing_sampled_layer_chain
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_augmented_missing_sampled_layer_chain s out
    \<longleftrightarrow>
    trace_fri_bad_with_header_tied_augmented_partial_candidate s out \<and>
    \<not> trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s out"

definition trace_fri_header_tied_unaugmented_partial_candidate
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_unaugmented_partial_candidate s out
    \<longleftrightarrow>
    trace_fri_bad_with_header_tied_partial_candidate s out \<and>
    \<not> trace_fri_bad_with_header_tied_augmented_partial_candidate s out"

lemma trace_fri_bad_with_header_tied_augmented_partial_candidate_imp_plain:
  assumes
    "trace_fri_bad_with_header_tied_augmented_partial_candidate s out"
  shows "trace_fri_bad_with_header_tied_partial_candidate s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
    where fri:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand:
      "partial_trace_table_candidate_with_recorded_first_fri_siblings
        trace_table trace_openings trace_roots trace_bs fri_query_idxs
        trace_round_layers"
    and nonlow: "\<not> trace_table_low_degree trace_table"
    unfolding trace_fri_bad_with_header_tied_augmented_partial_candidate_def
    by blast
  have plain: "partial_trace_table_candidate trace_table trace_openings"
    by (rule
        partial_trace_table_candidate_with_recorded_first_fri_siblingsD(1)
        [OF cand])
  show ?thesis
    unfolding trace_fri_bad_with_header_tied_partial_candidate_def
    by (intro exI conjI)
      (rule fri, rule header, rule partial, rule plain, rule nonlow)
qed

lemma trace_fri_bad_with_header_tied_partial_candidate_imp_augmented_or_unaugmented:
  assumes "trace_fri_bad_with_header_tied_partial_candidate s out"
  shows
    "trace_fri_bad_with_header_tied_augmented_partial_candidate s out \<or>
     trace_fri_header_tied_unaugmented_partial_candidate s out"
  using assms
  unfolding trace_fri_header_tied_unaugmented_partial_candidate_def
  by blast

lemma wp_trace_fri_header_tied_partial_candidate_bound_from_augmented_and_unaugmented:
  assumes augmented_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_partial_candidate s) s
      \<le> A"
    and unaugmented_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_unaugmented_partial_candidate s) s \<le> U"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le> A + U"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_bad_with_header_tied_augmented_partial_candidate s out \<or>
          trace_fri_header_tied_unaugmented_partial_candidate s out) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_bad_with_header_tied_partial_candidate_imp_augmented_or_unaugmented)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_augmented_partial_candidate s) s +
      wp_event verify_monad
        (trace_fri_header_tied_unaugmented_partial_candidate s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> A + U"
    by (rule add_mono[OF augmented_bound unaugmented_bound])
  finally show ?thesis .
qed

lemma trace_fri_bad_with_header_tied_augmented_sampled_layer_chain_imp_plain:
  assumes
    "trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s out"
  shows "trace_fri_bad_with_header_tied_sampled_layer_chain s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table doms
      layers
    where fri:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand:
      "partial_trace_table_candidate_with_recorded_first_fri_siblings
        trace_table trace_openings trace_roots trace_bs fri_query_idxs
        trace_round_layers"
    and nonlow: "\<not> trace_table_low_degree trace_table"
    and chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
    unfolding
      trace_fri_bad_with_header_tied_augmented_sampled_layer_chain_def
    by blast
  have plain: "partial_trace_table_candidate trace_table trace_openings"
    by (rule
        partial_trace_table_candidate_with_recorded_first_fri_siblingsD(1)
        [OF cand])
  show ?thesis
    unfolding trace_fri_bad_with_header_tied_sampled_layer_chain_def
    by (intro exI conjI)
      (rule fri, rule header, rule partial, rule plain, rule nonlow,
        rule chain)
qed

lemma trace_fri_bad_with_header_tied_sampled_layer_chain_imp_augmented:
  assumes "trace_fri_bad_with_header_tied_sampled_layer_chain s out"
  shows "trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table doms
      layers
    where fri:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and nonlow: "\<not> trace_table_low_degree trace_table"
    and chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
    unfolding trace_fri_bad_with_header_tied_sampled_layer_chain_def
    by blast
  have augmented:
    "partial_trace_table_candidate_with_recorded_first_fri_siblings
      trace_table trace_openings trace_roots trace_bs fri_query_idxs
      trace_round_layers"
    by (rule
        generic_trace_sampled_layer_chain_evidence_augments_partial_trace_candidate
        [OF cand chain])
  show ?thesis
    unfolding
      trace_fri_bad_with_header_tied_augmented_sampled_layer_chain_def
    by (intro exI conjI)
      (rule fri, rule header, rule partial, rule augmented, rule nonlow,
        rule chain)
qed

lemma wp_trace_fri_header_tied_augmented_sampled_layer_chain_bound_from_plain:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s) s
      \<le> R"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s) s
      \<le> wp_event verify_monad
        (trace_fri_bad_with_header_tied_sampled_layer_chain s) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_bad_with_header_tied_augmented_sampled_layer_chain_imp_plain)
  then show ?thesis
    by (rule order_trans[OF _ sampled_bound])
qed

lemma wp_trace_fri_header_tied_sampled_layer_chain_bound_from_augmented:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s) s
      \<le> R"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s
      \<le> wp_event verify_monad
        (trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s) s"
    by (rule wp_event_mono)
      (rule trace_fri_bad_with_header_tied_sampled_layer_chain_imp_augmented)
  then show ?thesis
    by (rule order_trans[OF _ sampled_bound])
qed

lemma trace_fri_header_tied_augmented_missing_sampled_imp_assignment_obstruction:
  assumes missing:
    "trace_fri_header_tied_augmented_missing_sampled_layer_chain s out"
  shows
    "trace_fri_header_tied_sampled_layer_assignment_obstruction s out"
proof -
  have bad:
    "trace_fri_bad_with_header_tied_augmented_partial_candidate s out"
    and not_sampled:
      "\<not> trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s out"
    using missing
    unfolding trace_fri_header_tied_augmented_missing_sampled_layer_chain_def
    by blast+
  from bad obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
    where fri:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and augmented:
      "partial_trace_table_candidate_with_recorded_first_fri_siblings
        trace_table trace_openings trace_roots trace_bs fri_query_idxs
        trace_round_layers"
    and nonlow: "\<not> trace_table_low_degree trace_table"
    unfolding trace_fri_bad_with_header_tied_augmented_partial_candidate_def
    by blast
  have cand: "partial_trace_table_candidate trace_table trace_openings"
    by (rule
        partial_trace_table_candidate_with_recorded_first_fri_siblingsD(1)
        [OF augmented])
  have partial_generic:
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
    by (rule accepted_fri_opening_transcript_trace_generic_partial_evidence
        [OF fri])
  have no_chain:
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
    have "trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s out"
      unfolding
        trace_fri_bad_with_header_tied_augmented_sampled_layer_chain_def
      by (intro exI conjI)
        (rule fri, rule header, rule partial, rule augmented, rule nonlow,
          rule chain)
    then show False
      using not_sampled by contradiction
  qed
  have obstruction:
    "generic_fri_sampled_layer_assignment_obstruction
      trace_table_low_degree trace_table (clength - 1) trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers"
    unfolding generic_fri_sampled_layer_assignment_obstruction_def
    using partial_generic no_chain by blast
  show ?thesis
    unfolding trace_fri_header_tied_sampled_layer_assignment_obstruction_def
    by (intro exI conjI)
      (rule fri, rule header, rule partial, rule cand, rule nonlow,
        rule obstruction)
qed

lemma wp_trace_fri_header_tied_augmented_missing_sampled_bound_from_assignment_obstruction:
  assumes obstruction_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_layer_assignment_obstruction s) s
      \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_augmented_missing_sampled_layer_chain s) s
      \<le> M"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_augmented_missing_sampled_layer_chain s) s
      \<le> wp_event verify_monad
        (trace_fri_header_tied_sampled_layer_assignment_obstruction s) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_augmented_missing_sampled_imp_assignment_obstruction)
  then show ?thesis
    by (rule order_trans[OF _ obstruction_bound])
qed

lemma wp_trace_fri_header_tied_augmented_partial_candidate_bound_from_sampled_and_missing:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s) s
      \<le> R"
    and missing_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_augmented_missing_sampled_layer_chain s) s
        \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_partial_candidate s) s
      \<le> R + M"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_partial_candidate s) s
      \<le> wp_event verify_monad
        (\<lambda>out.
          trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s out \<or>
          trace_fri_header_tied_augmented_missing_sampled_layer_chain s out) s"
    unfolding trace_fri_header_tied_augmented_missing_sampled_layer_chain_def
    by (rule wp_event_mono) blast
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s) s +
      wp_event verify_monad
        (trace_fri_header_tied_augmented_missing_sampled_layer_chain s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> R + M"
    by (rule add_mono[OF sampled_bound missing_bound])
  finally show ?thesis .
qed

lemma wp_trace_fri_header_tied_augmented_partial_candidate_bound_from_sampled_conflict_and_zero:
  assumes sampled_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s) s
      \<le> R"
    and conflict_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_augmented_partial_candidate s) s
      \<le> R + (C + Z)"
proof -
  have obstruction_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_layer_assignment_obstruction s) s
      \<le> C + Z"
    by (rule
        wp_trace_fri_header_tied_assignment_obstruction_bound_from_conflict_and_zero
        [OF conflict_bound zero_bound])
  have missing_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_augmented_missing_sampled_layer_chain s) s
      \<le> C + Z"
    by (rule
        wp_trace_fri_header_tied_augmented_missing_sampled_bound_from_assignment_obstruction
        [OF obstruction_bound])
  show ?thesis
    by (rule
        wp_trace_fri_header_tied_augmented_partial_candidate_bound_from_sampled_and_missing
        [OF sampled_bound missing_bound])
qed

lemma trace_fri_header_tied_augmented_partial_candidate_imp_sampled_conflict_or_zero:
  assumes bad:
    "trace_fri_bad_with_header_tied_augmented_partial_candidate s out"
  shows
    "trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s out \<or>
     trace_fri_header_tied_sampled_assignment_conflict s out \<or>
     trace_fri_header_tied_zero_round_final_obstruction s out"
proof (cases
    "trace_fri_bad_with_header_tied_augmented_sampled_layer_chain s out")
  case True
  then show ?thesis by blast
next
  case False
  have missing:
    "trace_fri_header_tied_augmented_missing_sampled_layer_chain s out"
    unfolding trace_fri_header_tied_augmented_missing_sampled_layer_chain_def
    using bad False by blast
  have obstruction:
    "trace_fri_header_tied_sampled_layer_assignment_obstruction s out"
    by (rule
        trace_fri_header_tied_augmented_missing_sampled_imp_assignment_obstruction
        [OF missing])
  then show ?thesis
    using trace_fri_header_tied_assignment_obstruction_imp_conflict_or_zero
    by blast
qed

lemma trace_fri_header_tied_recorded_sibling_candidate_mismatch_false:
  "\<not> trace_fri_header_tied_recorded_sibling_candidate_mismatch s out"
proof
  assume bad:
    "trace_fri_header_tied_recorded_sibling_candidate_mismatch s out"
  from bad obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      round_idx xp xp_path xn xn_path result final_state where
    fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers"
    and agrees:
      "trace_table_agrees_with_recorded_first_fri_siblings trace_table
        trace_roots trace_bs fri_query_idxs trace_round_layers"
    and round_bound: "round_idx < length fri_query_idxs"
    and bs_nonempty: "0 < length trace_bs"
    and step:
      "fri_layer_step_evidence
        (trace_roots ! 0)
        (trace_bs ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
          round_idx 0 xp xn)
        (trace_round_layers ! round_idx ! 0)"
    and neq:
      "trace_table !
        fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        \<noteq> xn"
    unfolding trace_fri_header_tied_recorded_sibling_candidate_mismatch_def
    by blast
  have roots_nonempty: "0 < length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings]
      bs_nonempty by simp
  have eq:
    "trace_table !
      fri_sibling_index (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0) =
      xn"
    using agrees round_bound roots_nonempty bs_nonempty step
    unfolding trace_table_agrees_with_recorded_first_fri_siblings_def
    by blast
  show False
    using eq neq by simp
qed

lemma trace_fri_header_tied_value_aligned_sibling_mismatch_imp_recorded_sibling_missing:
  assumes mismatch:
    "trace_fri_header_tied_value_aligned_sibling_mismatch s out"
  shows
    "trace_fri_header_tied_recorded_sibling_candidate_missing s out"
proof -
  from mismatch obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
      round_idx xp xp_path xn xn_path result final_state where
    out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
        dg composition_roots composition_bs composition_final fri_query_idxs
        trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and nonlow: "\<not> trace_table_low_degree trace_table"
    and round_bound: "round_idx < length fri_query_idxs"
    and bs_nonempty: "0 < length trace_bs"
    and openings_nonempty: "trace_openings ! round_idx \<noteq> []"
    and hd_idx:
      "opening_index (hd (trace_openings ! round_idx)) =
        fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0"
    and hd_value:
      "opening_value (hd (trace_openings ! round_idx)) = xp"
    and step:
      "fri_layer_step_evidence
        (trace_roots ! 0)
        (trace_bs ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
          round_idx 0 xp xn)
        (trace_round_layers ! round_idx ! 0)"
    and neq:
      "trace_table !
        fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        \<noteq> xn"
    unfolding trace_fri_header_tied_value_aligned_sibling_mismatch_def
    by auto
  have roots_nonempty: "0 < length trace_roots"
    using accepted_fri_opening_transcript_shapes(2)[OF fri_openings]
      bs_nonempty by simp
  have missing:
    "\<not> trace_table_agrees_with_recorded_first_fri_siblings trace_table
      trace_roots trace_bs fri_query_idxs trace_round_layers"
    unfolding trace_table_agrees_with_recorded_first_fri_siblings_def
    using round_bound roots_nonempty bs_nonempty step neq by blast
  show ?thesis
    unfolding trace_fri_header_tied_recorded_sibling_candidate_missing_def
    by (intro exI conjI)
      (rule out_eq, rule fri_openings, rule header, rule partial, rule cand,
       rule missing, rule nonlow, rule round_bound, rule bs_nonempty,
       rule openings_nonempty, rule hd_idx, rule hd_value, rule step, rule neq)
qed

lemma trace_fri_header_tied_sibling_mismatch_structural_gap_imp_recorded_sibling_missing:
  assumes gap: "trace_fri_header_tied_sibling_mismatch_structural_gap s out"
  shows "trace_fri_header_tied_recorded_sibling_candidate_missing s out"
  using gap
  unfolding trace_fri_header_tied_sibling_mismatch_structural_gap_def
  by (blast intro:
      trace_fri_header_tied_value_aligned_sibling_mismatch_imp_recorded_sibling_missing)

lemma trace_fri_header_tied_unaugmented_partial_candidate_imp_missing_or_base_gap:
  assumes unaugmented:
    "trace_fri_header_tied_unaugmented_partial_candidate s out"
  shows
    "trace_fri_header_tied_recorded_sibling_candidate_missing s out \<or>
     trace_fri_header_tied_base_value_alignment_gap s out"
proof -
  from unaugmented have plain:
    "trace_fri_bad_with_header_tied_partial_candidate s out"
    and not_augmented:
      "\<not> trace_fri_bad_with_header_tied_augmented_partial_candidate s out"
    unfolding trace_fri_header_tied_unaugmented_partial_candidate_def
    by simp_all
  from plain obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    unfolding trace_fri_bad_with_header_tied_partial_candidate_def
    by blast
  have not_agrees:
    "\<not> trace_table_agrees_with_recorded_first_fri_siblings trace_table
      trace_roots trace_bs fri_query_idxs trace_round_layers"
  proof
    assume agrees:
      "trace_table_agrees_with_recorded_first_fri_siblings trace_table
        trace_roots trace_bs fri_query_idxs trace_round_layers"
    have augmented_candidate:
      "partial_trace_table_candidate_with_recorded_first_fri_siblings
        trace_table trace_openings trace_roots trace_bs fri_query_idxs
        trace_round_layers"
      unfolding
        partial_trace_table_candidate_with_recorded_first_fri_siblings_def
      by (intro conjI cand agrees)
    have "trace_fri_bad_with_header_tied_augmented_partial_candidate s out"
      unfolding trace_fri_bad_with_header_tied_augmented_partial_candidate_def
      by (intro exI conjI)
        (rule fri_openings, rule header, rule partial,
          rule augmented_candidate, rule not_low)
    then show False
      using not_augmented by contradiction
  qed
  from not_agrees obtain round_idx xp xp_path xn xn_path where
    round_bound: "round_idx < length fri_query_idxs"
    and roots_nonempty: "0 < length trace_roots"
    and trace_bs_nonempty: "0 < length trace_bs"
    and step:
      "fri_layer_step_evidence
        (trace_roots ! 0)
        (trace_bs ! 0)
        (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
          round_idx 0 xp xn)
        (trace_round_layers ! round_idx ! 0)"
    and sibling_neq:
      "trace_table !
        fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        \<noteq> xn"
    unfolding trace_table_agrees_with_recorded_first_fri_siblings_def
    by blast
  have no_match:
    "\<not> fri_opening_matches_table (fri_evidence_layer_len trace_roots 0)
      (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
      trace_table xp xn"
  proof
    assume match:
      "fri_opening_matches_table (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
        trace_table xp xn"
    have "trace_table !
        fri_sibling_index (fri_evidence_layer_len trace_roots 0)
          (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0) =
        xn"
      by (rule fri_opening_matches_tableD(4)[OF match])
    then show False
      using sibling_neq by contradiction
  qed
  have generic_base:
    "generic_fri_sampled_base_opening_conflict trace_table trace_roots
      trace_bs fri_query_idxs trace_round_layers"
    unfolding generic_fri_sampled_base_opening_conflict_def
    by (intro exI conjI)
      (rule trace_bs_nonempty, rule round_bound, rule step, rule no_match)
  have sampled_base:
    "trace_fri_header_tied_sampled_base_opening_conflict s out"
    unfolding trace_fri_header_tied_sampled_base_opening_conflict_def
    by (intro exI conjI)
      (rule fri_openings, rule header, rule partial, rule cand, rule not_low,
        rule generic_base)
  show ?thesis
  proof (cases
      "trace_fri_header_tied_value_aligned_base_opening_conflict s out")
    case True
    have "trace_fri_header_tied_value_aligned_sibling_mismatch s out"
      by (rule trace_fri_header_tied_value_aligned_base_imp_sibling_mismatch
          [OF True])
    then show ?thesis
      by (blast intro:
          trace_fri_header_tied_value_aligned_sibling_mismatch_imp_recorded_sibling_missing)
  next
    case False
    then have "trace_fri_header_tied_base_value_alignment_gap s out"
      using sampled_base
      unfolding trace_fri_header_tied_base_value_alignment_gap_def
      by simp
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_header_tied_unaugmented_partial_candidate_bound_from_recorded_missing_and_base_gap:
  fixes M G :: prob
  assumes missing_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_recorded_sibling_candidate_missing s) s \<le> M"
    and gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_unaugmented_partial_candidate s) s \<le> M + G"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_unaugmented_partial_candidate s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_recorded_sibling_candidate_missing s out \<or>
          trace_fri_header_tied_base_value_alignment_gap s out) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_unaugmented_partial_candidate_imp_missing_or_base_gap)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing s) s +
      wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> M + G"
    by (rule add_mono[OF missing_bound gap_bound])
  finally show ?thesis .
qed

lemma wp_trace_fri_header_tied_sibling_structural_gap_bound_from_recorded_sibling_missing:
  assumes missing_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_recorded_sibling_candidate_missing s) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> M"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le>
      wp_event verify_monad
        (trace_fri_header_tied_recorded_sibling_candidate_missing s) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_sibling_mismatch_structural_gap_imp_recorded_sibling_missing)
  then show ?thesis
    by (rule order_trans[OF _ missing_bound])
qed

lemma trace_fri_header_tied_sibling_structural_gap_without_recorded_missing_false:
  assumes gap: "trace_fri_header_tied_sibling_mismatch_structural_gap s out"
    and not_missing:
      "\<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out"
  shows False
  using trace_fri_header_tied_sibling_mismatch_structural_gap_imp_recorded_sibling_missing
    [OF gap] not_missing
  by contradiction

lemma wp_trace_fri_header_tied_sibling_structural_gap_without_recorded_missing_zero:
  "wp_event verify_monad
    (\<lambda>out. trace_fri_header_tied_sibling_mismatch_structural_gap s out \<and>
      \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
    \<le> 0"
proof -
  have "wp_event verify_monad
      (\<lambda>out. trace_fri_header_tied_sibling_mismatch_structural_gap s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono)
      (auto dest:
        trace_fri_header_tied_sibling_structural_gap_without_recorded_missing_false)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis .
qed

lemma trace_fri_header_tied_value_aligned_sibling_mismatch_without_recorded_missing_imp_partial_merkle:
  assumes mismatch:
    "trace_fri_header_tied_value_aligned_sibling_mismatch s out"
    and not_missing:
      "\<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out"
  shows "partial_merkle_inconsistency_bad s out"
proof -
  have split:
    "partial_merkle_inconsistency_bad s out \<or>
     trace_fri_header_tied_sibling_mismatch_structural_gap s out"
    by (rule
        trace_fri_header_tied_value_aligned_sibling_mismatch_imp_partial_merkle_or_structural_gap
        [OF mismatch])
  then show ?thesis
    using not_missing
      trace_fri_header_tied_sibling_mismatch_structural_gap_imp_recorded_sibling_missing
    by blast
qed

lemma wp_trace_fri_header_tied_value_aligned_sibling_mismatch_without_recorded_missing_bound_from_partial_merkle:
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
  shows
    "wp_event verify_monad
      (\<lambda>out. trace_fri_header_tied_value_aligned_sibling_mismatch s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> P"
proof -
  have "wp_event verify_monad
      (\<lambda>out. trace_fri_header_tied_value_aligned_sibling_mismatch s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> wp_event verify_monad (partial_merkle_inconsistency_bad s) s"
    by (rule wp_event_mono)
      (auto dest:
        trace_fri_header_tied_value_aligned_sibling_mismatch_without_recorded_missing_imp_partial_merkle)
  then show ?thesis
    by (rule order_trans[OF _ merkle_bound])
qed

lemma wp_trace_fri_header_tied_value_aligned_base_without_recorded_missing_bound_from_partial_merkle:
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
  shows
    "wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_value_aligned_base_opening_conflict s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> P"
proof -
  have "wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_value_aligned_base_opening_conflict s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> wp_event verify_monad
        (\<lambda>out. trace_fri_header_tied_value_aligned_sibling_mismatch s out \<and>
          \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s"
    by (rule wp_event_mono)
      (auto intro: trace_fri_header_tied_value_aligned_base_imp_sibling_mismatch)
  also have "... \<le> P"
    by (rule
        wp_trace_fri_header_tied_value_aligned_sibling_mismatch_without_recorded_missing_bound_from_partial_merkle
        [OF merkle_bound])
  finally show ?thesis .
qed

lemma wp_trace_fri_header_tied_sampled_base_without_recorded_missing_bound_from_partial_merkle_and_gap:
  fixes P G :: prob
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_sampled_base_opening_conflict s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> P + G"
proof -
  have "wp_event verify_monad
      (\<lambda>out.
        trace_fri_header_tied_sampled_base_opening_conflict s out \<and>
        \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s
      \<le> wp_event verify_monad
        (\<lambda>out.
          (trace_fri_header_tied_value_aligned_base_opening_conflict s out \<and>
            \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) \<or>
          trace_fri_header_tied_base_value_alignment_gap s out) s"
    by (rule wp_event_mono)
      (auto dest:
        trace_fri_header_tied_sampled_base_imp_value_aligned_or_gap)
  also have "... \<le>
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_header_tied_value_aligned_base_opening_conflict s out \<and>
          \<not> trace_fri_header_tied_recorded_sibling_candidate_missing s out) s +
      wp_event verify_monad
        (trace_fri_header_tied_base_value_alignment_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> P + G"
    by (intro add_mono gap_bound
        wp_trace_fri_header_tied_value_aligned_base_without_recorded_missing_bound_from_partial_merkle
        [OF merkle_bound])
  finally show ?thesis .
qed

lemma trace_fri_header_tied_recorded_sibling_candidate_missingE:
  assumes missing:
    "trace_fri_header_tied_recorded_sibling_candidate_missing s out"
  obtains result final_state trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table round_idx xp xp_path xn xn_path
  where
    "out = Some (result, final_state)"
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers"
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "\<not> trace_table_agrees_with_recorded_first_fri_siblings trace_table
      trace_roots trace_bs fri_query_idxs trace_round_layers"
    "\<not> trace_table_low_degree trace_table"
    "round_idx < length fri_query_idxs"
    "0 < length trace_bs"
    "trace_openings ! round_idx \<noteq> []"
    "opening_index (hd (trace_openings ! round_idx)) =
      fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0"
    "opening_value (hd (trace_openings ! round_idx)) = xp"
    "fri_layer_step_evidence
      (trace_roots ! 0)
      (trace_bs ! 0)
      (fri_evidence_layer_len trace_roots 0)
      (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
      1
      (fri_sibling_index (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0))
      xp xp_path xn xn_path
      (fri_evidence_next_idx trace_roots fri_query_idxs round_idx 0)
      (fri_evidence_next_value trace_roots trace_bs fri_query_idxs
        round_idx 0 xp xn)
      (trace_round_layers ! round_idx ! 0)"
    "trace_table !
      fri_sibling_index (fri_evidence_layer_len trace_roots 0)
        (fri_evidence_layer_idx trace_roots fri_query_idxs round_idx 0)
      \<noteq> xn"
  using missing
  unfolding trace_fri_header_tied_recorded_sibling_candidate_missing_def
  apply (elim exE conjE)
  apply (rule that)
  apply assumption+
  done

lemma trace_fri_header_tied_recorded_sibling_candidate_missing_no_same_sampled_chain:
  assumes missing:
    "trace_fri_header_tied_recorded_sibling_candidate_missing s out"
  obtains result final_state trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table round_idx xp xp_path xn xn_path
  where
    "out = Some (result, final_state)"
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers"
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "\<not> trace_table_low_degree trace_table"
    "\<And>doms layers.
      \<not> generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
proof -
  from missing show thesis
  proof (rule trace_fri_header_tied_recorded_sibling_candidate_missingE)
    fix result final_state trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table round_idx xp xp_path xn xn_path
    assume out_eq: "out = Some (result, final_state)"
      and fri_openings:
        "accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final dg composition_roots composition_bs composition_final
          fri_query_idxs trace_round_layers composition_round_layers"
      and header:
        "verifier_header_transcript s fr trace_roots trace_final as dg
          composition_roots composition_final rest"
      and partial:
        "accepted_with_partial_trace_openings s out fr fri_query_idxs
          trace_openings"
      and candidate:
        "partial_trace_table_candidate trace_table trace_openings"
      and no_agree:
        "\<not> trace_table_agrees_with_recorded_first_fri_siblings trace_table
          trace_roots trace_bs fri_query_idxs trace_round_layers"
      and nonlow: "\<not> trace_table_low_degree trace_table"
  have no_chain:
    "\<And>doms layers.
      \<not> generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
  proof
    fix doms layers
    assume chain:
      "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
        trace_table (clength - 1) trace_roots trace_bs trace_final
        fri_query_idxs trace_round_layers doms layers"
    have "trace_table_agrees_with_recorded_first_fri_siblings trace_table
        trace_roots trace_bs fri_query_idxs trace_round_layers"
      by (rule
          generic_trace_sampled_layer_chain_evidence_recorded_first_sibling_agreement
          [OF chain])
    then show False
      using no_agree by contradiction
  qed
  show thesis
    by (rule that[OF out_eq fri_openings header partial candidate nonlow
          no_chain])
  qed
qed

lemma trace_fri_header_tied_recorded_sibling_candidate_missing_imp_assignment_obstruction:
  assumes missing:
    "trace_fri_header_tied_recorded_sibling_candidate_missing s out"
  shows
    "trace_fri_header_tied_sampled_layer_assignment_obstruction s out"
proof (rule
    trace_fri_header_tied_recorded_sibling_candidate_missing_no_same_sampled_chain
    [OF missing])
  fix result final_state trace_roots trace_bs trace_final dg
    composition_roots composition_bs composition_final fri_query_idxs
    trace_round_layers composition_round_layers fr as rest trace_openings
    trace_table round_idx xp xp_path xn xn_path
  assume fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs trace_final
      dg composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and cand: "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and no_chain:
      "\<And>doms layers.
        \<not> generic_fri_sampled_layer_chain_evidence trace_table_low_degree
          trace_table (clength - 1) trace_roots trace_bs trace_final
          fri_query_idxs trace_round_layers doms layers"
  have partial_generic:
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
    by (rule accepted_fri_opening_transcript_trace_generic_partial_evidence
        [OF fri_openings])
  have obstruction:
    "generic_fri_sampled_layer_assignment_obstruction
      trace_table_low_degree trace_table (clength - 1) trace_roots
      trace_bs trace_final fri_query_idxs trace_round_layers"
    unfolding generic_fri_sampled_layer_assignment_obstruction_def
    using partial_generic no_chain by blast
  show "trace_fri_header_tied_sampled_layer_assignment_obstruction s out"
    unfolding trace_fri_header_tied_sampled_layer_assignment_obstruction_def
    by (intro exI conjI)
      (rule fri_openings, rule header, rule partial, rule cand,
        rule not_low, rule obstruction)
qed

lemma trace_fri_header_tied_recorded_sibling_candidate_missing_imp_conflict_or_zero:
  assumes missing:
    "trace_fri_header_tied_recorded_sibling_candidate_missing s out"
  shows
    "trace_fri_header_tied_sampled_assignment_conflict s out \<or>
     trace_fri_header_tied_zero_round_final_obstruction s out"
  by (rule trace_fri_header_tied_assignment_obstruction_imp_conflict_or_zero)
    (rule
      trace_fri_header_tied_recorded_sibling_candidate_missing_imp_assignment_obstruction
      [OF missing])

lemma wp_trace_fri_header_tied_recorded_sibling_candidate_missing_bound_from_conflict_and_zero:
  assumes conflict_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_sampled_assignment_conflict s) s \<le> C"
    and zero_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> Z"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_recorded_sibling_candidate_missing s) s
      \<le> C + Z"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_recorded_sibling_candidate_missing s) s \<le>
      wp_event verify_monad
        (\<lambda>out. trace_fri_header_tied_sampled_assignment_conflict s out \<or>
          trace_fri_header_tied_zero_round_final_obstruction s out) s"
    by (rule wp_event_mono)
      (rule
        trace_fri_header_tied_recorded_sibling_candidate_missing_imp_conflict_or_zero)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_header_tied_sampled_assignment_conflict s) s +
      wp_event verify_monad
        (trace_fri_header_tied_zero_round_final_obstruction s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> C + Z"
    by (rule add_mono[OF conflict_bound zero_bound])
  finally show ?thesis .
qed

end

end
