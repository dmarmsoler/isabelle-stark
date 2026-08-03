(*  Title:      Stark/Soundness_FRI_Obligation_Normalization.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Obligation_Normalization
  imports Soundness_FRI_Active_Reductions
begin

text \<open>
  Normal form for the three FRI obligations that remain internal to locale
  \<^locale>\<open>soundness_fri\<close>.

  This theory does not change the protocol or the public soundness route.  It
  only records the exact verifier-local events behind the internal FRI
  assumptions and exposes the generic partial FRI evidence already available
  from accepted verifier transcripts.
\<close>

context soundness
begin

lemma trace_fri_header_tied_reduction_event:
  "trace_fri_header_tied_reduction s \<longleftrightarrow>
    wp_event verify_monad
      (\<lambda>out. \<exists>trace_roots trace_bs trace_final dg composition_roots
          composition_bs composition_final fri_query_idxs trace_round_layers
          composition_round_layers fr as rest trace_openings trace_table.
        accepted_fri_opening_transcript s out trace_roots trace_bs
          trace_final dg composition_roots composition_bs composition_final
          fri_query_idxs trace_round_layers composition_round_layers \<and>
        verifier_header_transcript s fr trace_roots trace_final as dg
          composition_roots composition_final rest \<and>
        accepted_with_partial_trace_openings s out fr fri_query_idxs
          trace_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        \<not> trace_table_low_degree trace_table) s \<le>
      trace_fri_error"
  unfolding trace_fri_header_tied_reduction_def
    trace_fri_bad_with_header_tied_partial_candidate_def
  by simp

lemma trace_fri_empty_header_reduction_event:
  "trace_fri_empty_header_reduction s \<longleftrightarrow>
    wp_event verify_monad
      (\<lambda>out. \<exists>fr f_fri_roots f_final as dg final trace_query_idxs
          trace_openings trace_table composition_table.
        accepted_with_empty_composition_header_candidates s out fr
          f_fri_roots f_final as dg final trace_query_idxs trace_openings
          trace_table composition_table \<and>
        \<not> trace_table_low_degree trace_table) s \<le>
      trace_fri_error"
  unfolding trace_fri_empty_header_reduction_def
    trace_fri_bad_with_empty_composition_header_candidates_def
  by simp

lemma composition_fri_verifier_tied_reduction_event:
  "composition_fri_verifier_tied_reduction s \<longleftrightarrow>
    wp_event verify_monad
      (\<lambda>out. \<exists>trace_roots trace_bs trace_final fri_dg composition_roots
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
        trace_table_low_degree trace_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table) s \<le>
      composition_fri_error"
  unfolding composition_fri_verifier_tied_reduction_def
    composition_fri_bad_with_verifier_tied_partial_candidate_def
  by simp

lemma trace_fri_header_tied_badE:
  assumes "trace_fri_bad_with_header_tied_partial_candidate s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "\<not> trace_table_low_degree trace_table"
  using assms
  unfolding trace_fri_bad_with_header_tied_partial_candidate_def
  by blast

lemma trace_fri_empty_header_badE:
  assumes "trace_fri_bad_with_empty_composition_header_candidates s out"
  obtains fr f_fri_roots f_final as dg final trace_query_idxs
      trace_openings trace_table composition_table where
    "accepted_with_empty_composition_header_candidates s out fr
      f_fri_roots f_final as dg final trace_query_idxs trace_openings
      trace_table composition_table"
    "\<not> trace_table_low_degree trace_table"
  using assms
  unfolding trace_fri_bad_with_empty_composition_header_candidates_def
  by blast

lemma trace_fri_empty_header_bad_extracts_generic_partial_evidence:
  assumes outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    and bad:
    "trace_fri_bad_with_empty_composition_header_candidates s
      (Some (result, final_state))"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table where
    "trace_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr candidate_query_idxs
      trace_openings trace_table"
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
proof -
  have reachable:
    "trace_fri_bad_with_reachable_partial_candidate s
      (Some (result, final_state))"
    by (rule
        trace_fri_bad_with_empty_composition_header_candidates_imp_reachable_partial_candidate
        [OF bad])
  from verify_monad_trace_fri_bad_extracts_opening_evidence
      [OF outcome reachable]
  obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr candidate_query_idxs trace_openings
      trace_table
  where evidence:
    "trace_fri_partial_candidate_opening_evidence s
      (Some (result, final_state)) trace_roots trace_bs trace_final dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr candidate_query_idxs
      trace_openings trace_table"
    by blast
  have generic:
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
    by (rule trace_fri_partial_candidate_opening_evidence_generic_partial
        [OF evidence])
  show ?thesis
    by (rule that[OF evidence generic])
qed

lemma trace_fri_header_tied_sampled_layer_chain_imp_sampled_layer_chain:
  assumes "trace_fri_bad_with_header_tied_sampled_layer_chain s out"
  shows "trace_fri_bad_with_sampled_layer_chain s out"
proof -
  from assms obtain trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table doms
      layers
  where fri:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    and partial:
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    and candidate:
    "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    and chain:
    "generic_fri_sampled_layer_chain_evidence trace_table_low_degree
      trace_table (clength - 1) trace_roots trace_bs trace_final
      fri_query_idxs trace_round_layers doms layers"
    unfolding trace_fri_bad_with_header_tied_sampled_layer_chain_def
    by blast
  have evidence:
    "trace_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr fri_query_idxs trace_openings
      trace_table"
    unfolding trace_fri_partial_candidate_opening_evidence_def
      trace_fri_partial_candidate_evidence_def
    by (intro conjI fri partial candidate not_low)
  show ?thesis
    unfolding trace_fri_bad_with_sampled_layer_chain_def
    by (intro exI conjI)
      (rule evidence, rule chain)
qed

lemma wp_trace_fri_header_tied_sampled_layer_chain_bound_from_sampled:
  assumes sampled_bound:
    "wp_event verify_monad (trace_fri_bad_with_sampled_layer_chain s) s \<le> R"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R"
proof -
  have "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le>
      wp_event verify_monad (trace_fri_bad_with_sampled_layer_chain s) s"
    by (rule wp_event_mono)
      (rule trace_fri_header_tied_sampled_layer_chain_imp_sampled_layer_chain)
  then show ?thesis
    by (rule order_trans[OF _ sampled_bound])
qed

lemma wp_trace_fri_header_tied_sampled_layer_chain_bound_from_full_cover_and_missing:
  assumes full_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_full_cover_layer_chain s bad) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s \<le> M"
  shows
    "wp_event verify_monad
      (trace_fri_bad_with_header_tied_sampled_layer_chain s) s \<le> R + M"
  by (rule wp_trace_fri_header_tied_sampled_layer_chain_bound_from_sampled)
    (rule wp_trace_fri_sampled_bound_from_full_cover_and_missing
      [OF full_bound missing_bound])

lemma composition_fri_verifier_tied_sampled_layer_chain_imp_sampled_layer_chain:
  assumes "composition_fri_bad_with_verifier_tied_sampled_layer_chain s out"
  shows "composition_fri_bad_with_sampled_layer_chain s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table doms layers
  where fri:
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
    and trace_low: "trace_table_low_degree trace_table"
    and composition_not_low:
    "\<not> composition_table_low_degree maxDegree composition_table"
    and chain:
    "generic_fri_sampled_layer_chain_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) composition_roots composition_bs composition_final
      fri_query_idxs composition_round_layers doms layers"
    unfolding composition_fri_bad_with_verifier_tied_sampled_layer_chain_def
    by blast
  have unaligned:
    "accepted_with_partial_initial_openings s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final
      fri_query_idxs trace_openings fri_query_idxs composition_openings"
    by (rule accepted_with_partial_initial_openings_aligned_imp_unaligned
        [OF aligned])
  have evidence:
    "composition_fri_partial_candidate_opening_evidence s out trace_roots
      trace_bs trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr trace_roots trace_final as fri_dg
      composition_roots composition_final fri_query_idxs trace_openings
      fri_query_idxs composition_openings trace_table composition_table"
    unfolding composition_fri_partial_candidate_opening_evidence_def
      composition_fri_partial_candidate_evidence_def
    by (intro conjI fri unaligned trace_candidate composition_candidate
        trace_low composition_not_low)
  show ?thesis
    unfolding composition_fri_bad_with_sampled_layer_chain_def
    by (intro exI conjI)
      (rule evidence, rule chain)
qed

lemma wp_composition_fri_verifier_tied_sampled_layer_chain_bound_from_sampled:
  assumes sampled_bound:
    "wp_event verify_monad (composition_fri_bad_with_sampled_layer_chain s) s
      \<le> R"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s
      \<le> R"
proof -
  have "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le>
      wp_event verify_monad (composition_fri_bad_with_sampled_layer_chain s) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_sampled_layer_chain_imp_sampled_layer_chain)
  then show ?thesis
    by (rule order_trans[OF _ sampled_bound])
qed

lemma wp_composition_fri_verifier_tied_sampled_layer_chain_bound_from_full_cover_and_missing:
  assumes full_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_full_cover_layer_chain s bad) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s
      \<le> R + M"
  by (rule
      wp_composition_fri_verifier_tied_sampled_layer_chain_bound_from_sampled)
    (rule wp_composition_fri_sampled_bound_from_full_cover_and_missing
      [OF full_bound missing_bound])

lemma trace_fri_header_tied_residual_obligations_from_full_cover_missing_without_head_slot_and_selected_zero:
  assumes full_bound:
    "wp_event verify_monad
      (trace_fri_bad_with_full_cover_layer_chain s bad) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (trace_fri_sampled_missing_full_cover s bad) s \<le> M"
    and zero:
    "wp_event verify_monad
      (trace_fri_header_tied_zero_round_final_obstruction s) s \<le> z_b"
    and merkle:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    and structural:
    "wp_event verify_monad
      (trace_fri_header_tied_sibling_mismatch_structural_gap s) s \<le> h_b"
    and next_bound:
    "wp_event verify_monad
      (trace_fri_header_tied_next_value_replay_gap s) s \<le> n_b"
    and successor:
    "wp_event verify_monad
      (trace_fri_header_tied_successor_replay_gap s) s \<le> s_b"
    and total:
    "(R + M) + (((((p_b + h_b) + p_b) + n_b + s_b +
      (p_b + 0 + 0)) + p_b) + 0 + z_b)
      \<le> trace_fri_error"
  shows
    "trace_fri_header_tied_residual_obligations s
      (R + M) z_b 0 p_b h_b p_b n_b s_b 0"
  by (rule
      trace_fri_header_tied_residual_obligations_from_bounds_without_head_slot_and_selected_zero)
    (rule
      wp_trace_fri_header_tied_sampled_layer_chain_bound_from_full_cover_and_missing
      [OF full_bound missing_bound],
     rule zero, rule merkle, rule structural, rule next_bound,
     rule successor, rule total)

lemma composition_fri_verifier_tied_residual_obligations_from_full_cover_missing_slot_zero:
  assumes full_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_full_cover_layer_chain s bad) s \<le> R"
    and missing_bound:
    "wp_event verify_monad
      (composition_fri_sampled_missing_full_cover s bad) s \<le> M"
    and merkle:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> p_b"
    and next_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_next_value_replay_gap s) s \<le> n_b"
    and successor:
    "wp_event verify_monad
      (composition_fri_verifier_tied_successor_replay_gap s) s \<le> s_b"
    and final_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap s) s \<le> g_b"
    and total:
    "(R + M) + (((p_b + 0) + n_b + s_b + g_b + p_b) + 0)
      \<le> composition_fri_error"
  shows
    "composition_fri_verifier_tied_residual_obligations s
      (R + M) 0 p_b n_b s_b g_b"
  by (rule composition_fri_verifier_tied_residual_obligations_from_bounds_slot_zero)
    (rule
      wp_composition_fri_verifier_tied_sampled_layer_chain_bound_from_full_cover_and_missing
      [OF full_bound missing_bound],
     rule merkle, rule next_bound, rule successor, rule final_bound,
     rule total)

lemma composition_fri_verifier_tied_badE:
  assumes "composition_fri_bad_with_verifier_tied_partial_candidate s out"
  obtains trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final
      fri_query_idxs trace_openings composition_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    "trace_table_low_degree trace_table"
    "\<not> composition_table_low_degree maxDegree composition_table"
  using assms
  unfolding composition_fri_bad_with_verifier_tied_partial_candidate_def
  by blast

lemma trace_fri_header_tied_bad_generic_partial_evidence:
  assumes "trace_fri_bad_with_header_tied_partial_candidate s out"
  obtains trace_roots trace_bs trace_final dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as rest trace_openings trace_table where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "verifier_header_transcript s fr trace_roots trace_final as dg
      composition_roots composition_final rest"
    "accepted_with_partial_trace_openings s out fr fri_query_idxs
      trace_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "\<not> trace_table_low_degree trace_table"
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
proof -
  from trace_fri_header_tied_badE[OF assms] obtain trace_roots trace_bs
      trace_final dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers fr as rest
      trace_openings trace_table
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
    and candidate:
    "partial_trace_table_candidate trace_table trace_openings"
    and not_low: "\<not> trace_table_low_degree trace_table"
    by blast
  have generic:
    "generic_fri_partial_evidence trace_table_low_degree trace_table
      (clength - 1) trace_roots trace_bs trace_final fri_query_idxs
      trace_round_layers"
    by (rule accepted_fri_opening_transcript_trace_generic_partial_evidence
        [OF fri])
  show ?thesis
    by (rule that[OF fri header partial candidate not_low generic])
qed

lemma composition_fri_verifier_tied_bad_generic_partial_evidence:
  assumes "composition_fri_bad_with_verifier_tied_partial_candidate s out"
  obtains trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final
      fri_query_idxs trace_openings composition_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    "trace_table_low_degree trace_table"
    "\<not> composition_table_low_degree maxDegree composition_table"
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) composition_roots composition_bs composition_final
      fri_query_idxs composition_round_layers"
proof -
  from composition_fri_verifier_tied_badE[OF assms] obtain trace_roots
      trace_bs trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table
  where fri:
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
    and trace_low: "trace_table_low_degree trace_table"
    and composition_not_low:
    "\<not> composition_table_low_degree maxDegree composition_table"
    by blast
  have generic:
    "generic_fri_partial_evidence
      (composition_table_low_degree (to_nat fri_dg)) composition_table
      (to_nat fri_dg) composition_roots composition_bs composition_final
      fri_query_idxs composition_round_layers"
    by (rule
        accepted_fri_opening_transcript_composition_generic_partial_evidence
        [OF fri])
  show ?thesis
    by (rule that[OF fri aligned trace_candidate composition_candidate
          trace_low composition_not_low generic])
qed

end

end
