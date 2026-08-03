(*  Title:      Stark/Soundness_FRI_Candidate_Transfer_Support.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Candidate_Transfer_Support
  imports
    Soundness_FRI_Trace_Candidate_Gap
    Soundness_FRI_Composition_Support
begin

text \<open>
  Small destructors for the remaining FRI candidate-transfer branches.  These
  branches are intentionally not closed by complete-table uniqueness: sampled
  partial openings can admit multiple completions.  The lemmas here expose the
  exact low/non-low candidate shape that later proofs must charge to a
  partial-opening inconsistency or a narrower candidate-indexed event.
\<close>

context soundness
begin

definition trace_fri_header_tied_low_candidate_available
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_available s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      trace_table_low_degree trace_table)"

definition trace_fri_header_tied_low_candidate_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table.
      trace_fri_reachable_header_tie_gap s out \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      trace_table_low_degree trace_table)"

definition composition_fri_verifier_tied_misaligned_candidate_classification
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_misaligned_candidate_classification s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      \<not> (trace_table_low_degree trace_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table))"

definition composition_fri_verifier_tied_transcript_consistent_misaligned_classification
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_transcript_consistent_misaligned_classification
      s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings
        composition_openings trace_table composition_table.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest \<and>
      accepted_with_partial_initial_openings_aligned_transcript_consistent s
        out fr trace_roots trace_final as fri_dg composition_roots
        composition_final fri_query_idxs trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      \<not> (trace_table_low_degree trace_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table))"

definition composition_fri_verifier_tied_transcript_consistent_classification_cover
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_transcript_consistent_classification_cover
      s out \<longleftrightarrow>
    composition_bad_with_partial_candidates s out \<or>
    trace_fri_bad_with_header_tied_partial_candidate s out \<or>
    query_bad_with_aligned_transcript_partial_candidates s out"

lemma trace_fri_header_tied_candidate_transfer_gapD:
  assumes "trace_fri_header_tied_candidate_transfer_gap s out"
  shows
    "trace_fri_bad_with_reachable_partial_candidate s out"
    "trace_fri_header_tied_low_candidate_available s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table where
    bad: "trace_fri_bad_with_reachable_partial_candidate s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and low: "trace_table_low_degree trace_table"
    unfolding trace_fri_header_tied_candidate_transfer_gap_def
    by blast
  show "trace_fri_bad_with_reachable_partial_candidate s out"
    by (rule bad)
  show "trace_fri_header_tied_low_candidate_available s out"
    unfolding trace_fri_header_tied_low_candidate_available_def
    by (intro exI conjI)
      (rule fri_openings, rule header, rule partial, rule candidate,
        rule low)
qed

lemma trace_fri_header_tied_candidate_transfer_gap_imp_accepted:
  assumes "trace_fri_header_tied_candidate_transfer_gap s out"
  shows "accepted out"
proof -
  have bad: "trace_fri_bad_with_reachable_partial_candidate s out"
    by (rule trace_fri_header_tied_candidate_transfer_gapD(1)[OF assms])
  from trace_fri_bad_with_reachable_partial_candidateE[OF bad]
  obtain fr query_idxs trace_openings trace_table where evidence:
    "trace_fri_partial_candidate_evidence s out fr query_idxs
      trace_openings trace_table"
    by blast
  have partial:
    "accepted_with_partial_trace_openings s out fr query_idxs
      trace_openings"
    by (rule trace_fri_partial_candidate_evidenceD(1)[OF evidence])
  show ?thesis
    by (rule accepted_with_partial_trace_openings_imp_accepted[OF partial])
qed

lemma wp_trace_fri_header_tied_candidate_transfer_gap_bound_from_low_candidate:
  assumes low_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_available s) s \<le> T"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_candidate_transfer_gap s) s \<le> T"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_candidate_transfer_gap s) s \<le>
    wp_event verify_monad
      (trace_fri_header_tied_low_candidate_available s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_candidate_transfer_gapD(2))
  then show ?thesis
    by (rule order_trans[OF _ low_bound])
qed

lemma trace_fri_header_tied_low_candidate_gap_imp_low_candidate_available:
  assumes "trace_fri_header_tied_low_candidate_gap s out"
  shows "trace_fri_header_tied_low_candidate_available s out"
  using assms
  unfolding trace_fri_header_tied_low_candidate_gap_def
    trace_fri_header_tied_low_candidate_available_def
  by blast

lemma trace_fri_header_tied_low_candidate_gap_imp_transfer_gap:
  assumes "trace_fri_header_tied_low_candidate_gap s out"
  shows "trace_fri_header_tied_candidate_transfer_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table where
    gap: "trace_fri_reachable_header_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and low: "trace_table_low_degree trace_table"
    unfolding trace_fri_header_tied_low_candidate_gap_def by blast
  show ?thesis
    by (rule trace_fri_header_candidate_low_imp_transfer_gap
        [OF gap fri_openings header partial candidate low])
qed

lemma trace_fri_header_tied_candidate_available_gap_imp_low_candidate_gap:
  assumes "trace_fri_header_tied_candidate_available_gap s out"
  shows "trace_fri_header_tied_low_candidate_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table where
    gap: "trace_fri_reachable_header_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    unfolding trace_fri_header_tied_candidate_available_gap_def by blast
  show ?thesis
  proof (cases "trace_table_low_degree trace_table")
    case True
    show ?thesis
      unfolding trace_fri_header_tied_low_candidate_gap_def
      by (intro exI conjI)
        (rule gap, rule fri_openings, rule header, rule partial,
          rule candidate, rule True)
  next
    case False
    have False
      by (rule trace_fri_header_candidate_non_low_contradicts_header_tie_gap
          [OF gap fri_openings header partial candidate False])
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_header_tied_candidate_available_gap_bound_from_low_candidate_gap:
  assumes low_gap_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_gap s) s \<le> T"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_candidate_available_gap s) s \<le> T"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_candidate_available_gap s) s \<le>
    wp_event verify_monad
      (trace_fri_header_tied_low_candidate_gap s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_candidate_available_gap_imp_low_candidate_gap)
  then show ?thesis
    by (rule order_trans[OF _ low_gap_bound])
qed

lemma wp_trace_fri_reachable_header_tie_gap_bound_from_merkle_and_low_candidate_gap:
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and low_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_gap s) s \<le> T"
  shows
    "wp_event verify_monad
      (trace_fri_reachable_header_tie_gap s) s \<le> M + T"
proof -
  have split_bound:
    "wp_event verify_monad
      (trace_fri_reachable_header_tie_gap s) s \<le>
      wp_event verify_monad
        (\<lambda>out. partial_merkle_inconsistency_bad s out \<or>
          trace_fri_header_tied_candidate_available_gap s out) s"
    by (rule wp_event_mono_on_support)
      (rule
        trace_fri_reachable_header_tie_gap_imp_merkle_or_candidate_available_on_support)
  also have "... \<le>
      wp_event verify_monad (partial_merkle_inconsistency_bad s) s +
      wp_event verify_monad
        (trace_fri_header_tied_candidate_available_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> M + T"
    by (rule add_mono[OF merkle_bound])
      (rule
        wp_trace_fri_header_tied_candidate_available_gap_bound_from_low_candidate_gap
        [OF low_gap_bound])
  finally show ?thesis .
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_low_candidate_gap:
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le> Ht"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> Mt"
    and low_gap_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_gap s) s \<le> Tt"
    and total_bound: "Ht + (Mt + Tt) \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have gap_bound:
    "wp_event verify_monad
      (trace_fri_reachable_header_tie_gap s) s \<le> Mt + Tt"
    by (rule
        wp_trace_fri_reachable_header_tie_gap_bound_from_merkle_and_low_candidate_gap
        [OF merkle_bound low_gap_bound])
  have reachable_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le>
      Ht + (Mt + Tt)"
    by (rule wp_trace_fri_reachable_bound_from_header_tied_and_gap
        [OF header_bound gap_bound])
  show ?thesis
    unfolding trace_fri_reachable_partial_candidate_reduction_assumption_def
    by (rule order_trans[OF reachable_bound total_bound])
qed

lemma composition_fri_verifier_tied_candidate_transfer_gapD:
  assumes "composition_fri_verifier_tied_candidate_transfer_gap s out"
  shows
    "composition_fri_bad_with_reachable_partial_candidate s out"
    "composition_fri_verifier_tied_misaligned_candidate_classification s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table where
    bad: "composition_fri_bad_with_reachable_partial_candidate s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and classified:
      "\<not> (trace_table_low_degree trace_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table)"
    unfolding composition_fri_verifier_tied_candidate_transfer_gap_def
    by blast
  show "composition_fri_bad_with_reachable_partial_candidate s out"
    by (rule bad)
  show
    "composition_fri_verifier_tied_misaligned_candidate_classification s out"
    unfolding
      composition_fri_verifier_tied_misaligned_candidate_classification_def
    by (intro exI conjI)
      (rule fri_openings, rule aligned, rule trace_candidate,
        rule composition_candidate, rule classified)
qed

lemma composition_fri_verifier_tied_candidate_transfer_gap_imp_accepted:
  assumes "composition_fri_verifier_tied_candidate_transfer_gap s out"
  shows "accepted out"
  by (rule composition_fri_bad_with_reachable_partial_candidate_imp_accepted)
    (rule composition_fri_verifier_tied_candidate_transfer_gapD(1)[OF assms])

lemma wp_composition_fri_verifier_tied_candidate_transfer_gap_bound_from_misaligned_classification:
  assumes classification_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_misaligned_candidate_classification s)
      s \<le> T"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_candidate_transfer_gap s) s \<le> T"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_candidate_transfer_gap s) s \<le>
    wp_event verify_monad
      (composition_fri_verifier_tied_misaligned_candidate_classification s)
      s"
    by (rule wp_event_mono)
      (rule composition_fri_verifier_tied_candidate_transfer_gapD(2))
  then show ?thesis
    by (rule order_trans[OF _ classification_bound])
qed

lemma composition_fri_verifier_tied_transcript_consistent_misaligned_classification_imp_misaligned_classification:
  assumes
    "composition_fri_verifier_tied_transcript_consistent_misaligned_classification
      s out"
  shows "composition_fri_verifier_tied_misaligned_candidate_classification
      s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      composition_openings trace_table composition_table where
    fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent s
        out fr trace_roots trace_final as fri_dg composition_roots
        composition_final fri_query_idxs trace_openings composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and classified:
      "\<not> (trace_table_low_degree trace_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table)"
    unfolding
      composition_fri_verifier_tied_transcript_consistent_misaligned_classification_def
    by blast
  have aligned:
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final fri_query_idxs
      trace_openings composition_openings"
    using partial
    by (blast dest:
        accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
        accepted_with_partial_initial_openings_aligned_consistent_imp_aligned)
  show ?thesis
    unfolding
      composition_fri_verifier_tied_misaligned_candidate_classification_def
    by (intro exI conjI)
      (rule fri_openings, rule aligned, rule trace_candidate,
        rule composition_candidate, rule classified)
qed

lemma composition_fri_verifier_tied_transcript_consistent_misaligned_classification_imp_aligned_bad_event:
  assumes false_statement: "\<not> exists_valid_trace"
    and classification:
      "composition_fri_verifier_tied_transcript_consistent_misaligned_classification
        s out"
  shows
    "soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate
      s out"
proof -
  from classification obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      composition_openings trace_table composition_table where
    fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent s
        out fr trace_roots trace_final as fri_dg composition_roots
        composition_final fri_query_idxs trace_openings composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    unfolding
      composition_fri_verifier_tied_transcript_consistent_misaligned_classification_def
    by blast
  show ?thesis
    by (rule
        accepted_verifier_tied_aligned_transcript_partial_candidate_partition
        [OF false_statement fri_openings partial header trace_candidate
          composition_candidate])
qed

lemma wp_composition_fri_verifier_tied_transcript_consistent_misaligned_classification_bound_from_aligned_bad_event:
  assumes false_statement: "\<not> exists_valid_trace"
    and aligned_bound:
      "wp_event verify_monad
        (soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate
          s) s \<le> T"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_transcript_consistent_misaligned_classification
        s) s \<le> T"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_transcript_consistent_misaligned_classification
        s) s \<le>
    wp_event verify_monad
      (soundness_bad_event_verifier_tied_aligned_transcript_partial_candidate
        s) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_transcript_consistent_misaligned_classification_imp_aligned_bad_event
        [OF false_statement])
  then show ?thesis
    by (rule order_trans[OF _ aligned_bound])
qed

lemma composition_fri_verifier_tied_transcript_consistent_misaligned_classification_imp_cover:
  assumes false_statement: "\<not> exists_valid_trace"
    and classification:
      "composition_fri_verifier_tied_transcript_consistent_misaligned_classification
        s out"
  shows
    "composition_fri_verifier_tied_transcript_consistent_classification_cover
      s out"
proof -
  from classification obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      composition_openings trace_table composition_table where
    fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and header:
      "verifier_header_transcript s fr trace_roots trace_final as fri_dg
        composition_roots composition_final rest"
    and partial:
      "accepted_with_partial_initial_openings_aligned_transcript_consistent s
        out fr trace_roots trace_final as fri_dg composition_roots
        composition_final fri_query_idxs trace_openings composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and classified:
      "\<not> (trace_table_low_degree trace_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table)"
    unfolding
      composition_fri_verifier_tied_transcript_consistent_misaligned_classification_def
    by blast
  show ?thesis
  proof (cases "trace_table_low_degree trace_table")
    case False
    have aligned:
      "accepted_with_partial_initial_openings_aligned_consistent s out fr
        trace_roots trace_final as fri_dg composition_roots
        composition_final fri_query_idxs trace_openings composition_openings"
      by (rule
          accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
          [OF partial])
    have aligned0:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
      by (rule
          accepted_with_partial_initial_openings_aligned_consistent_imp_aligned
          [OF aligned])
    have trace_partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
      by (rule accepted_with_partial_initial_openings_aligned_shapes(3)
          [OF aligned0])
    have "trace_fri_bad_with_header_tied_partial_candidate s out"
      unfolding trace_fri_bad_with_header_tied_partial_candidate_def
      by (intro exI conjI)
        (rule fri_openings, rule header, rule trace_partial,
          rule trace_candidate, rule False)
    then show ?thesis
      unfolding
        composition_fri_verifier_tied_transcript_consistent_classification_cover_def
      by blast
  next
    case True
    note trace_low = True
    have composition_low:
      "composition_table_low_degree maxDegree composition_table"
      using classified trace_low by blast
    show ?thesis
    proof (cases "all_queries_consistent trace_table composition_table as")
      case False
      have "query_bad_with_aligned_transcript_partial_candidates s out"
        unfolding query_bad_with_aligned_transcript_partial_candidates_def
        using partial trace_candidate composition_candidate trace_low
          composition_low False
        by blast
      then show ?thesis
        unfolding
          composition_fri_verifier_tied_transcript_consistent_classification_cover_def
        by blast
    next
      case True
      note all_queries = True
      from trace_low obtain f where
        deg_f: "degree f < clength"
        and trace_table_eq: "trace_table = map (poly f) eval_domain"
        unfolding trace_table_low_degree_def by blast
      have violated: "violated_constraints f \<noteq> {}"
        by (rule false_statement_violated_constraints
            [OF false_statement deg_f])
      have aligned:
        "accepted_with_partial_initial_openings_aligned_consistent s out fr
          trace_roots trace_final as fri_dg composition_roots
          composition_final fri_query_idxs trace_openings
          composition_openings"
        by (rule
            accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
            [OF partial])
      have "composition_bad_with_partial_candidates s out"
        unfolding composition_bad_with_partial_candidates_def
        using accepted_with_partial_initial_openings_aligned_consistent_imp_unaligned
            [OF aligned]
          trace_candidate composition_candidate deg_f trace_table_eq
          violated composition_low all_queries
        by blast
      then show ?thesis
        unfolding
          composition_fri_verifier_tied_transcript_consistent_classification_cover_def
        by blast
    qed
  qed
qed

lemma wp_composition_fri_verifier_tied_transcript_consistent_classification_cover_union_bound:
  assumes comp_bound:
      "wp_event verify_monad
        (composition_bad_with_partial_candidates s) s \<le> C"
    and trace_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate s) s \<le> Ft"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_aligned_transcript_partial_candidates s) s \<le> Q"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_transcript_consistent_classification_cover
        s) s \<le> C + Ft + Q"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_transcript_consistent_classification_cover
        s) s \<le>
    wp_event verify_monad
      (composition_bad_with_partial_candidates s) s +
    wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s +
    wp_event verify_monad
      (query_bad_with_aligned_transcript_partial_candidates s) s"
  proof -
    have "wp_event verify_monad
        (composition_fri_verifier_tied_transcript_consistent_classification_cover
          s) s \<le>
      wp_event verify_monad
        (composition_bad_with_partial_candidates s) s +
      wp_event verify_monad
        (\<lambda>out.
          trace_fri_bad_with_header_tied_partial_candidate s out \<or>
          query_bad_with_aligned_transcript_partial_candidates s out) s"
      unfolding
        composition_fri_verifier_tied_transcript_consistent_classification_cover_def
      by (rule wp_event_union_bound)
    also have "... \<le>
      wp_event verify_monad
        (composition_bad_with_partial_candidates s) s +
      (wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate s) s +
       wp_event verify_monad
        (query_bad_with_aligned_transcript_partial_candidates s) s)"
      by (rule add_mono[OF order_refl wp_event_union_bound])
    finally show ?thesis by (simp add: algebra_simps)
  qed
  also have "... \<le> C + Ft + Q"
    by (intro add_mono comp_bound trace_bound query_bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_verifier_tied_transcript_consistent_misaligned_classification_bound_from_cover_components:
  assumes false_statement: "\<not> exists_valid_trace"
    and comp_bound:
      "wp_event verify_monad
        (composition_bad_with_partial_candidates s) s \<le> C"
    and trace_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate s) s \<le> Ft"
    and query_bound:
      "wp_event verify_monad
        (query_bad_with_aligned_transcript_partial_candidates s) s \<le> Q"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_transcript_consistent_misaligned_classification
        s) s \<le> C + Ft + Q"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_transcript_consistent_misaligned_classification
        s) s \<le>
    wp_event verify_monad
      (composition_fri_verifier_tied_transcript_consistent_classification_cover
        s) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_transcript_consistent_misaligned_classification_imp_cover
        [OF false_statement])
  also have "... \<le> C + Ft + Q"
    by (rule
        wp_composition_fri_verifier_tied_transcript_consistent_classification_cover_union_bound
        [OF comp_bound trace_bound query_bound])
  finally show ?thesis .
qed

lemma composition_fri_verifier_tied_candidate_available_gap_imp_empty_or_merkle_or_transcript_consistent_classification:
  assumes available:
    "composition_fri_verifier_tied_candidate_available_gap s out"
  shows
    "composition_fri_reachable_verifier_tie_empty_header_gap s out \<or>
     partial_merkle_inconsistency_bad s out \<or>
     composition_fri_verifier_tied_transcript_consistent_misaligned_classification
      s out"
proof -
  from available obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table where
    gap: "composition_fri_reachable_verifier_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
    and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
    unfolding composition_fri_verifier_tied_candidate_available_gap_def
    by blast
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  show ?thesis
  proof (cases "composition_roots = []")
    case True
    have "composition_fri_reachable_verifier_tie_empty_header_gap s out"
      by (rule composition_fri_reachable_verifier_tie_empty_header_gapI
          [OF gap fri_openings True])
    then show ?thesis by simp
  next
    case comp_nonempty: False
    show ?thesis
    proof (cases "partial_merkle_inconsistency_bad s out")
      case True
      then show ?thesis by simp
    next
      case no_merkle: False
      from accepted_fri_opening_transcript_obtains_aligned_partial_openings
          [OF fri_openings[unfolded out_eq] comp_nonempty]
      obtain fr' as' rest' trace_openings' composition_openings'
      where header':
        "verifier_header_transcript s fr' trace_roots trace_final as' fri_dg
          composition_roots composition_final rest'"
        and partial':
        "accepted_with_partial_initial_openings_aligned_transcript_consistent s
          (Some (result, final_state)) fr' trace_roots trace_final as'
          fri_dg composition_roots composition_final fri_query_idxs
          trace_openings' composition_openings'"
        by blast
      have aligned':
        "accepted_with_partial_initial_openings_aligned s out fr'
          trace_roots trace_final as' fri_dg composition_roots
          composition_final fri_query_idxs trace_openings'
          composition_openings'"
        using partial'[folded out_eq]
        by (blast dest:
            accepted_with_partial_initial_openings_aligned_transcript_consistent_imp_aligned
            accepted_with_partial_initial_openings_aligned_consistent_imp_aligned)
      obtain trace_table' composition_table'
      where trace_candidate':
        "partial_trace_table_candidate trace_table' trace_openings'"
        and composition_candidate':
        "partial_composition_table_candidate composition_table'
          composition_openings'"
        using
          accepted_with_partial_initial_openings_aligned_candidates_if_no_partial_merkle_bad
          [OF aligned'[unfolded out_eq] no_merkle[unfolded out_eq]]
        by blast
      have classified:
        "\<not> (trace_table_low_degree trace_table' \<and>
          \<not> composition_table_low_degree maxDegree composition_table')"
      proof
        assume bad_class:
          "trace_table_low_degree trace_table' \<and>
           \<not> composition_table_low_degree maxDegree composition_table'"
        have "composition_fri_bad_with_verifier_tied_partial_candidate s out"
          unfolding composition_fri_bad_with_verifier_tied_partial_candidate_def
          by (intro exI conjI)
            (rule fri_openings, rule aligned', rule trace_candidate',
              rule composition_candidate', rule bad_class[THEN conjunct1],
              rule bad_class[THEN conjunct2])
        then show False
          using gap
          unfolding composition_fri_reachable_verifier_tie_gap_def by simp
      qed
      have
        "composition_fri_verifier_tied_transcript_consistent_misaligned_classification
          s out"
        unfolding
          composition_fri_verifier_tied_transcript_consistent_misaligned_classification_def
        by (intro exI conjI)
          (rule fri_openings, rule header'[folded out_eq],
            rule partial'[folded out_eq], rule trace_candidate',
            rule composition_candidate', rule classified)
      then show ?thesis by simp
    qed
  qed
qed

lemma wp_composition_fri_verifier_tied_candidate_available_gap_bound_from_empty_merkle_and_transcript_consistent_classification:
  assumes empty_bound:
      "wp_event verify_monad
        (composition_fri_reachable_verifier_tie_empty_header_gap s) s \<le> E"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and classification_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_transcript_consistent_misaligned_classification
          s) s \<le> T"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_candidate_available_gap s) s \<le>
      E + (M + T)"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_candidate_available_gap s) s \<le>
    wp_event verify_monad
      (\<lambda>out.
        composition_fri_reachable_verifier_tie_empty_header_gap s out \<or>
        partial_merkle_inconsistency_bad s out \<or>
        composition_fri_verifier_tied_transcript_consistent_misaligned_classification
          s out) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_candidate_available_gap_imp_empty_or_merkle_or_transcript_consistent_classification)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_reachable_verifier_tie_empty_header_gap s) s +
      wp_event verify_monad
        (\<lambda>out.
          partial_merkle_inconsistency_bad s out \<or>
          composition_fri_verifier_tied_transcript_consistent_misaligned_classification
            s out) s"
    by (rule wp_event_union_bound)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_reachable_verifier_tie_empty_header_gap s) s +
      (wp_event verify_monad (partial_merkle_inconsistency_bad s) s +
       wp_event verify_monad
        (composition_fri_verifier_tied_transcript_consistent_misaligned_classification
          s) s)"
    by (rule add_mono[OF order_refl wp_event_union_bound])
  also have "... \<le> E + (M + T)"
    by (intro add_mono empty_bound merkle_bound classification_bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_reachable_verifier_tie_gap_bound_from_empty_merkle_and_candidate_available:
  assumes empty_bound:
      "wp_event verify_monad
        (composition_fri_reachable_verifier_tie_empty_header_gap s) s \<le> E"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and available_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_candidate_available_gap s) s \<le> T"
  shows
    "wp_event verify_monad
      (composition_fri_reachable_verifier_tie_gap s) s \<le> E + (M + T)"
proof -
  have split_bound:
    "wp_event verify_monad
      (composition_fri_reachable_verifier_tie_gap s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          composition_fri_reachable_verifier_tie_empty_header_gap s out \<or>
          partial_merkle_inconsistency_bad s out \<or>
          composition_fri_verifier_tied_candidate_available_gap s out) s"
    by (rule wp_event_mono_on_support)
      (rule
        composition_fri_reachable_verifier_tie_gap_imp_empty_or_merkle_or_candidate_available_on_support)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_reachable_verifier_tie_empty_header_gap s) s +
      wp_event verify_monad
        (\<lambda>out.
          partial_merkle_inconsistency_bad s out \<or>
          composition_fri_verifier_tied_candidate_available_gap s out) s"
    by (rule wp_event_union_bound)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_reachable_verifier_tie_empty_header_gap s) s +
      (wp_event verify_monad (partial_merkle_inconsistency_bad s) s +
       wp_event verify_monad
        (composition_fri_verifier_tied_candidate_available_gap s) s)"
    by (rule add_mono[OF order_refl wp_event_union_bound])
  also have "... \<le> E + (M + T)"
    by (intro add_mono empty_bound merkle_bound available_bound)
  finally show ?thesis .
qed

lemma composition_fri_reachable_partial_candidate_reduction_from_split_residual_bounds_with_candidate_available:
  fixes R A P M N S G E Q T :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and slot_gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          s) s \<le> A"
    and verifier_partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and missing_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s)
        s \<le> M"
    and next_gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap s) s \<le> G"
    and empty_bound:
      "wp_event verify_monad
        (composition_fri_reachable_verifier_tie_empty_header_gap s) s \<le> E"
    and gap_partial_merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> Q"
    and candidate_available_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_candidate_available_gap s) s \<le> T"
    and total_bound:
      "R + (((P + M) + N + S + G + P) + A) + (E + (Q + T))
        \<le> composition_fri_error"
  shows "composition_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have verifier_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s
      \<le> R + (((P + M) + N + S + G + P) + A)"
    by (rule
        wp_composition_fri_verifier_tied_bound_from_sampled_slot_recorded_chunk_gap_and_residuals
        [OF sampled_bound slot_gap_bound verifier_partial_merkle_bound
          missing_bound next_gap_bound successor_gap_bound final_gap_bound])
  have gap_bound:
    "wp_event verify_monad
      (composition_fri_reachable_verifier_tie_gap s) s \<le>
      E + (Q + T)"
    by (rule
        wp_composition_fri_reachable_verifier_tie_gap_bound_from_empty_merkle_and_candidate_available
        [OF empty_bound gap_partial_merkle_bound candidate_available_bound])
  show ?thesis
    by (rule
        composition_fri_reachable_partial_candidate_reduction_from_verifier_tied_and_gap
        [OF verifier_bound gap_bound total_bound])
qed

lemma composition_fri_reachable_partial_candidate_reduction_from_split_residual_bounds_with_candidate_available_and_recorded_missing_zero:
  fixes R A P N S G E Q T :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and slot_gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
        s) s \<le> A"
    and verifier_partial_merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and next_gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_next_value_replay_gap s) s \<le> N"
    and successor_gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_successor_replay_gap s) s \<le> S"
    and final_gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap s) s \<le> G"
    and empty_bound:
    "wp_event verify_monad
      (composition_fri_reachable_verifier_tie_empty_header_gap s) s \<le> E"
    and gap_partial_merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> Q"
    and candidate_available_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_candidate_available_gap s) s \<le> T"
    and total_bound:
    "R + (((P + 0) + N + S + G + P) + A) + (E + (Q + T))
      \<le> composition_fri_error"
  shows "composition_fri_reachable_partial_candidate_reduction_assumption s"
  by (rule
      composition_fri_reachable_partial_candidate_reduction_from_split_residual_bounds_with_candidate_available
      [where M = 0])
    (rule sampled_bound,
     rule slot_gap_bound,
     rule verifier_partial_merkle_bound,
     rule wp_composition_fri_verifier_tied_recorded_base_chunk_auth_missing_zero,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound,
     rule empty_bound,
     rule gap_partial_merkle_bound,
     rule candidate_available_bound,
     rule total_bound)

end

end
