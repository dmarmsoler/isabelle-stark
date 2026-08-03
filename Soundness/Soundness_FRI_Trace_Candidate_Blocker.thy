(*  Title:      Stark/Soundness_FRI_Trace_Candidate_Blocker.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Trace_Candidate_Blocker
  imports Soundness_FRI_Candidate_Transfer_Support
begin

text \<open>
  Diagnostic normalization facts for the remaining trace candidate-transfer
  branch.  These lemmas do not close the branch; they identify the exact
  obstacle: the broad reachable witness may use a different authenticated root,
  query-index list, or opening set than the verifier-consumed/header-tied FRI
  witness.
\<close>

context soundness
begin

definition trace_fri_header_tied_low_candidate_untied_reachable_witness_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as rest trace_openings trace_table
        fr0 query_idxs0 trace_openings0 trace_table0.
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
      trace_table_low_degree trace_table \<and>
      accepted_with_partial_trace_openings s out fr0 query_idxs0
        trace_openings0 \<and>
      partial_trace_table_candidate trace_table0 trace_openings0 \<and>
      \<not> trace_table_low_degree trace_table0 \<and>
      (fr0 \<noteq> fr \<or> query_idxs0 \<noteq> fri_query_idxs \<or>
        trace_openings0 \<noteq> trace_openings))"

lemma trace_fri_header_tied_low_candidate_gap_imp_untied_reachable_witness:
  assumes "trace_fri_header_tied_low_candidate_gap s out"
  shows
    "trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table
  where gap: "trace_fri_reachable_header_tie_gap s out"
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
  have raw: "trace_fri_bad_with_reachable_partial_candidate s out"
    using gap unfolding trace_fri_reachable_header_tie_gap_def by simp
  from trace_fri_bad_with_reachable_partial_candidateE[OF raw]
  obtain fr0 query_idxs0 trace_openings0 trace_table0 where evidence0:
    "trace_fri_partial_candidate_evidence s out fr0 query_idxs0
      trace_openings0 trace_table0"
    by blast
  have partial0:
    "accepted_with_partial_trace_openings s out fr0 query_idxs0
      trace_openings0"
    by (rule trace_fri_partial_candidate_evidenceD(1)[OF evidence0])
  have candidate0:
    "partial_trace_table_candidate trace_table0 trace_openings0"
    by (rule trace_fri_partial_candidate_evidenceD(2)[OF evidence0])
  have not_low0: "\<not> trace_table_low_degree trace_table0"
    by (rule trace_fri_partial_candidate_evidenceD(3)[OF evidence0])
  have untied:
    "fr0 \<noteq> fr \<or> query_idxs0 \<noteq> fri_query_idxs \<or>
      trace_openings0 \<noteq> trace_openings"
  proof (rule ccontr)
    assume "\<not> (fr0 \<noteq> fr \<or> query_idxs0 \<noteq> fri_query_idxs \<or>
      trace_openings0 \<noteq> trace_openings)"
    then have eqs:
      "fr0 = fr"
      "query_idxs0 = fri_query_idxs"
      "trace_openings0 = trace_openings"
      by auto
    have "trace_fri_bad_with_header_tied_partial_candidate s out"
      unfolding trace_fri_bad_with_header_tied_partial_candidate_def
      by (intro exI conjI)
        (rule fri_openings, rule header,
          use partial0 candidate0 not_low0 eqs in auto)
    then show False
      using gap unfolding trace_fri_reachable_header_tie_gap_def by simp
  qed
  show ?thesis
    unfolding
      trace_fri_header_tied_low_candidate_untied_reachable_witness_gap_def
    by (intro exI conjI)
      (rule gap, rule fri_openings, rule header, rule partial,
        rule candidate, rule low, rule partial0, rule candidate0,
        rule not_low0, rule untied)
qed

lemma wp_trace_fri_header_tied_low_candidate_gap_bound_from_untied_witness:
  assumes
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
      s \<le> T"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_low_candidate_gap s) s \<le> T"
  by (rule order_trans[OF _ assms])
    (rule wp_event_mono,
      rule trace_fri_header_tied_low_candidate_gap_imp_untied_reachable_witness)

lemma trace_fri_reachable_header_tie_gap_imp_merkle_or_untied_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and gap: "trace_fri_reachable_header_tie_gap s out"
  shows
    "partial_merkle_inconsistency_bad s out \<or>
     trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
proof -
  have split:
    "partial_merkle_inconsistency_bad s out \<or>
     trace_fri_header_tied_candidate_available_gap s out"
    by (rule
        trace_fri_reachable_header_tie_gap_imp_merkle_or_candidate_available_on_support
        [OF support gap])
  then show ?thesis
  proof
    assume "partial_merkle_inconsistency_bad s out"
    then show ?thesis by simp
  next
    assume available: "trace_fri_header_tied_candidate_available_gap s out"
    have low_gap: "trace_fri_header_tied_low_candidate_gap s out"
      by (rule trace_fri_header_tied_candidate_available_gap_imp_low_candidate_gap
          [OF available])
    have
      "trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
      by (rule
          trace_fri_header_tied_low_candidate_gap_imp_untied_reachable_witness
          [OF low_gap])
    then show ?thesis by simp
  qed
qed

lemma wp_trace_fri_reachable_header_tie_gap_bound_from_merkle_and_untied:
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and untied_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
        s \<le> U"
  shows
    "wp_event verify_monad
      (trace_fri_reachable_header_tie_gap s) s \<le> M + U"
proof -
  have split_bound:
    "wp_event verify_monad
      (trace_fri_reachable_header_tie_gap s) s \<le>
      wp_event verify_monad
        (\<lambda>out. partial_merkle_inconsistency_bad s out \<or>
          trace_fri_header_tied_low_candidate_untied_reachable_witness_gap
            s out) s"
    by (rule wp_event_mono_on_support)
      (rule trace_fri_reachable_header_tie_gap_imp_merkle_or_untied_on_support)
  also have "... \<le>
      wp_event verify_monad (partial_merkle_inconsistency_bad s) s +
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
        s"
    by (rule wp_event_union_bound)
  also have "... \<le> M + U"
    by (rule add_mono[OF merkle_bound untied_bound])
  finally show ?thesis .
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_untied:
  fixes H M U :: prob
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le> H"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and untied_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
        s \<le> U"
    and total_bound: "H + (M + U) \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have gap_bound:
    "wp_event verify_monad
      (trace_fri_reachable_header_tie_gap s) s \<le> M + U"
    by (rule
        wp_trace_fri_reachable_header_tie_gap_bound_from_merkle_and_untied
        [OF merkle_bound untied_bound])
  have reachable_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_reachable_partial_candidate s) s \<le> H + (M + U)"
    by (rule wp_trace_fri_reachable_bound_from_header_tied_and_gap
        [OF header_bound gap_bound])
  show ?thesis
    unfolding trace_fri_reachable_partial_candidate_reduction_assumption_def
    by (rule order_trans[OF reachable_bound total_bound])
qed

end

end
