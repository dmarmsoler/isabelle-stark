(*  Title:      Stark/Soundness_FRI_Trace_Empty_Verifier_Tied.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Trace_Empty_Verifier_Tied
  imports
    Soundness_FRI_Trace_Untied_Cases
    Soundness_FRI_Zero_Round_Query_List_Bounds
begin

text \<open>
  Verifier-tied normalization for the empty-composition-header trace FRI branch.

  The broad empty-header branch can carry a non-low candidate built from
  existential partial openings.  This layer separates that branch into the
  verifier-checked zero-round obstruction, Merkle inconsistency, or the existing
  candidate-transfer residual.  It deliberately avoids complete-table
  reconstruction from sampled openings.
\<close>

context soundness
begin

lemma trace_zero_round_candidate_low_degree_if_final_consistent:
  assumes rounds_empty: "length trace_bs = 0"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final dg composition_roots composition_bs composition_final
        fri_query_idxs trace_round_layers composition_round_layers"
    and candidate:
      "partial_trace_table_candidate trace_table trace_openings"
    and final:
      "fri_final_constant_consistent trace_table trace_final"
  shows "trace_table_low_degree trace_table"
proof -
  have len_trace_bs: "length trace_bs = ceil_log clength"
    using accepted_fri_opening_transcript_shapes(1,2)[OF fri_openings]
    by simp
  have ceil_zero: "ceil_log clength = 0"
    using rounds_empty len_trace_bs by simp
  have clength_le_one: "clength \<le> 1"
    using ceil_zero unfolding ceil_log_def
    by (cases "clength \<le> 1") simp_all
  have clength_eq: "clength = 1"
    using clength_le_one clength_pos by simp
  have len_table: "length trace_table = length eval_domain"
    using candidate eval_domain_length
    unfolding partial_trace_table_candidate_def
    by simp
  have table_eq:
    "trace_table = map (poly [:trace_final:]) eval_domain"
  proof (rule nth_equalityI)
    show "length trace_table =
        length (map (poly [:trace_final:]) eval_domain)"
      using len_table by simp
  next
    fix i
    assume i_bound: "i < length trace_table"
    have "trace_table ! i = trace_final"
      by (rule fri_final_constant_consistent_nth[OF final i_bound])
    then show "trace_table ! i =
        map (poly [:trace_final:]) eval_domain ! i"
      using i_bound len_table by simp
  qed
  show ?thesis
    unfolding trace_table_low_degree_def
    by (intro exI[of _ "[:trace_final:]"] conjI)
      (use clength_eq table_eq in simp_all)
qed

lemma trace_fri_zero_round_final_obstruction_imp_checked_merkle_transfer_or_header:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and obstruction: "trace_fri_zero_round_final_obstruction s out"
  shows
    "trace_fri_zero_round_checked_final_obstruction s out \<or>
     partial_merkle_inconsistency_bad s out \<or>
     trace_fri_header_tied_candidate_transfer_gap s out \<or>
     trace_fri_bad_with_header_tied_partial_candidate s out"
proof -
  from trace_fri_zero_round_final_obstructionE[OF obstruction]
  obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr0 candidate_query_idxs trace_openings0
      trace_table0 where evidence:
      "trace_fri_partial_candidate_opening_evidence s out trace_roots
        trace_bs trace_final dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr0 candidate_query_idxs trace_openings0
        trace_table0"
    and rounds_empty: "length trace_bs = 0"
    and not_final0:
      "\<not> fri_final_constant_consistent trace_table0 trace_final"
    by blast
  have fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    using trace_fri_partial_candidate_opening_evidenceD(1)[OF evidence] .
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  from accepted_fri_opening_transcript_headerE[OF fri_openings]
  obtain fr as rest where header:
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
    by blast
  show ?thesis
  proof (cases "partial_merkle_inconsistency_bad s out")
    case True
    then show ?thesis by simp
  next
    case no_merkle: False
    from accepted_fri_opening_transcript_trace_openings_for_query_indices
        [OF fri_openings header out_eq]
    obtain trace_openings where partial:
      "accepted_with_partial_trace_openings s out fr fri_query_idxs
        trace_openings"
      by blast
    obtain trace_table where candidate:
      "partial_trace_table_candidate trace_table trace_openings"
      using accepted_with_partial_trace_openings_candidate_if_no_partial_merkle_bad
        [OF partial[unfolded out_eq] no_merkle[unfolded out_eq]]
      by blast
    show ?thesis
    proof (cases "trace_table_low_degree trace_table")
      case True
      then show ?thesis
      proof (cases "trace_fri_bad_with_header_tied_partial_candidate s out")
        case True
        then show ?thesis by simp
      next
        case no_header: False
        have reachable:
          "trace_fri_bad_with_reachable_partial_candidate s out"
          using trace_fri_zero_round_final_obstruction_imp_header_tied_or_gap
            [OF obstruction] no_header
          unfolding trace_fri_reachable_header_tie_gap_def by simp
        have gap: "trace_fri_reachable_header_tie_gap s out"
          unfolding trace_fri_reachable_header_tie_gap_def
          using reachable no_header by simp
        have transfer:
          "trace_fri_header_tied_candidate_transfer_gap s out"
          by (rule trace_fri_header_candidate_low_imp_transfer_gap
              [OF gap fri_openings header partial candidate True])
        then show ?thesis by simp
      qed
    next
      case not_low: False
      have not_final:
        "\<not> fri_final_constant_consistent trace_table trace_final"
      proof
        assume final:
          "fri_final_constant_consistent trace_table trace_final"
        have low:
          "trace_table_low_degree trace_table"
          by (rule
              trace_zero_round_candidate_low_degree_if_final_consistent
              [OF rounds_empty fri_openings candidate final])
        then show False
          using not_low by contradiction
      qed
      have header_zero:
        "trace_fri_header_tied_zero_round_final_obstruction s out"
        unfolding trace_fri_header_tied_zero_round_final_obstruction_def
        by (intro exI conjI)
          (rule fri_openings, rule header, rule partial, rule candidate,
            rule not_low, rule rounds_empty, rule not_final)
      then show ?thesis
        using
          trace_fri_header_tied_zero_round_final_obstruction_imp_checked_or_merkle
        by blast
    qed
  qed
qed

lemma wp_trace_fri_zero_round_checked_final_obstruction_bound_from_query_list_target:
  assumes target_bound:
    "wp_event verify_monad
      (trace_fri_zero_round_query_list_target_hit s) s \<le> Q"
  shows
    "wp_event verify_monad
      (trace_fri_zero_round_checked_final_obstruction s) s \<le> Q"
proof -
  have "wp_event verify_monad
      (trace_fri_zero_round_checked_final_obstruction s) s \<le>
    wp_event verify_monad
      (trace_fri_zero_round_checked_first_query_target_hit s) s"
    by (rule wp_event_mono)
      (rule trace_fri_zero_round_checked_final_obstruction_imp_first_query_target_hit)
  also have "... \<le>
    wp_event verify_monad
      (trace_fri_zero_round_query_list_target_hit s) s"
    by (rule wp_event_mono)
      (rule trace_fri_zero_round_checked_first_query_target_hit_imp_query_list_target)
  also have "... \<le> Q"
    by (rule target_bound)
  finally show ?thesis .
qed

lemma wp_trace_fri_zero_round_final_obstruction_bound_from_checked_merkle_transfer_header:
  fixes H M Q T :: prob
  assumes checked_bound:
    "wp_event verify_monad
      (trace_fri_zero_round_checked_final_obstruction s) s \<le> Q"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and transfer_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_candidate_transfer_gap s) s \<le> T"
    and header_bound:
      "wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate s) s \<le> H"
  shows
    "wp_event verify_monad
      (trace_fri_zero_round_final_obstruction s) s \<le> Q + M + T + H"
proof -
  have "wp_event verify_monad
      (trace_fri_zero_round_final_obstruction s) s \<le>
    wp_event verify_monad
      (\<lambda>out.
        trace_fri_zero_round_checked_final_obstruction s out \<or>
        partial_merkle_inconsistency_bad s out \<or>
        trace_fri_header_tied_candidate_transfer_gap s out \<or>
        trace_fri_bad_with_header_tied_partial_candidate s out) s"
    by (rule wp_event_mono_on_support)
      (rule trace_fri_zero_round_final_obstruction_imp_checked_merkle_transfer_or_header)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_zero_round_checked_final_obstruction s) s +
      wp_event verify_monad (partial_merkle_inconsistency_bad s) s +
      wp_event verify_monad
        (trace_fri_header_tied_candidate_transfer_gap s) s +
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate s) s"
    by (rule wp_event_union_bound4)
  also have "... \<le> Q + M + T + H"
    by (intro add_mono checked_bound merkle_bound transfer_bound
        header_bound)
  finally show ?thesis .
qed

lemma trace_fri_header_tied_candidate_transfer_gap_imp_header_or_untied:
  assumes transfer: "trace_fri_header_tied_candidate_transfer_gap s out"
  shows
    "trace_fri_bad_with_header_tied_partial_candidate s out \<or>
     trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
proof (cases "trace_fri_bad_with_header_tied_partial_candidate s out")
  case True
  then show ?thesis by simp
next
  case no_header: False
  from transfer obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as rest trace_openings
      trace_table where
    raw: "trace_fri_bad_with_reachable_partial_candidate s out"
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
    unfolding trace_fri_header_tied_candidate_transfer_gap_def by blast
  have gap: "trace_fri_reachable_header_tie_gap s out"
    unfolding trace_fri_reachable_header_tie_gap_def
    using raw no_header by simp
  have low_gap: "trace_fri_header_tied_low_candidate_gap s out"
    unfolding trace_fri_header_tied_low_candidate_gap_def
    by (intro exI conjI)
      (rule gap, rule fri_openings, rule header, rule partial, rule candidate,
        rule low)
  have untied:
    "trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s out"
    by (rule trace_fri_header_tied_low_candidate_gap_imp_untied_reachable_witness
        [OF low_gap])
  then show ?thesis by simp
qed

lemma wp_trace_fri_header_tied_candidate_transfer_gap_bound_from_header_and_untied:
  fixes H U :: prob
  assumes header_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_partial_candidate s) s \<le> H"
    and untied_bound:
      "wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
        s \<le> U"
  shows
    "wp_event verify_monad
      (trace_fri_header_tied_candidate_transfer_gap s) s \<le> H + U"
proof -
  have "wp_event verify_monad
      (trace_fri_header_tied_candidate_transfer_gap s) s \<le>
    wp_event verify_monad
      (\<lambda>out.
        trace_fri_bad_with_header_tied_partial_candidate s out \<or>
        trace_fri_header_tied_low_candidate_untied_reachable_witness_gap
          s out) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_candidate_transfer_gap_imp_header_or_untied)
  also have "... \<le>
      wp_event verify_monad
        (trace_fri_bad_with_header_tied_partial_candidate s) s +
      wp_event verify_monad
        (trace_fri_header_tied_low_candidate_untied_reachable_witness_gap s)
        s"
    by (rule wp_event_union_bound)
  also have "... \<le> H + U"
    by (rule add_mono[OF header_bound untied_bound])
  finally show ?thesis .
qed

end

end
