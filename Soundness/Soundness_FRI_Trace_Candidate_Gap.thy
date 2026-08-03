(*  Title:      Stark/Soundness_FRI_Trace_Candidate_Gap.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Trace_Candidate_Gap
  imports Soundness_FRI_Trace_Head_Value
begin

text \<open>
  Candidate-availability split for the reachable/header-tied trace FRI gap.
  This layer depends on the exact FRI-query opening bridge but keeps the
  exported split separate from the base head-value residual theory.
\<close>

context soundness
begin

lemma trace_fri_reachable_header_tie_gap_imp_merkle_or_candidate_available_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and gap: "trace_fri_reachable_header_tie_gap s out"
  shows
    "partial_merkle_inconsistency_bad s out \<or>
     trace_fri_header_tied_candidate_available_gap s out"
proof (cases "partial_merkle_inconsistency_bad s out")
  case True
  then show ?thesis by simp
next
  case no_merkle: False
  from gap have raw: "trace_fri_bad_with_reachable_partial_candidate s out"
    unfolding trace_fri_reachable_header_tie_gap_def by simp
  from trace_fri_bad_with_reachable_partial_candidateE[OF raw]
  obtain fr0 query_idxs0 trace_openings0 trace_table0 where partial0:
    "accepted_with_partial_trace_openings s out fr0 query_idxs0
      trace_openings0"
    using raw unfolding trace_fri_bad_with_reachable_partial_candidate_def
    by blast
  have acc: "accepted out"
    by (rule accepted_with_partial_trace_openings_imp_accepted[OF partial0])
  from acc obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_def by (cases out) auto
  from verify_monad_trace_fri_bad_extracts_opening_evidence
      [OF support[unfolded out_eq] raw[unfolded out_eq]]
  obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr1 candidate_query_idxs trace_openings1
      trace_table1
  where evidence:
    "trace_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr1 candidate_query_idxs
      trace_openings1 trace_table1"
    by (rule verify_monad_trace_fri_bad_extracts_opening_evidence
        [OF support[unfolded out_eq] raw[unfolded out_eq]])
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    using trace_fri_partial_candidate_opening_evidenceD(1)[OF evidence]
    unfolding out_eq .
  from accepted_fri_opening_transcript_headerE[OF fri_openings]
  obtain fr as rest where header:
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
    by (rule accepted_fri_opening_transcript_headerE[OF fri_openings])
  from accepted_fri_opening_transcript_trace_openings_for_query_indices
      [OF fri_openings header out_eq]
  obtain trace_openings where partial:
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    by (rule accepted_fri_opening_transcript_trace_openings_for_query_indices
        [OF fri_openings header out_eq])
  obtain trace_table where candidate:
    "partial_trace_table_candidate trace_table trace_openings"
    using accepted_with_partial_trace_openings_candidate_if_no_partial_merkle_bad
      [OF partial[unfolded out_eq] no_merkle[unfolded out_eq]]
    by blast
  show ?thesis
    unfolding trace_fri_header_tied_candidate_available_gap_def
    by (intro disjI2 exI conjI)
      (rule gap, rule fri_openings, rule header, rule partial,
        rule candidate)
qed

lemma wp_trace_fri_reachable_header_tie_gap_bound_from_merkle_and_candidate_transfer:
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and transfer_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_candidate_transfer_gap s) s \<le> T"
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
        wp_trace_fri_header_tied_candidate_available_gap_bound_from_transfer_gap
        [OF transfer_bound])
  finally show ?thesis .
qed

lemma trace_fri_reachable_partial_candidate_reduction_from_header_merkle_and_candidate_transfer:
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le> Ht"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> Mt"
    and transfer_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_candidate_transfer_gap s) s \<le> Tt"
    and total_bound: "Ht + (Mt + Tt) \<le> trace_fri_error"
  shows "trace_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have gap_bound:
    "wp_event verify_monad
      (trace_fri_reachable_header_tie_gap s) s \<le> Mt + Tt"
    by (rule
        wp_trace_fri_reachable_header_tie_gap_bound_from_merkle_and_candidate_transfer
        [OF merkle_bound transfer_bound])
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

end

end
