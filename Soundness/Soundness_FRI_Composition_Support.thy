(*  Title:      Stark/Soundness_FRI_Composition_Support.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Composition_Support
  imports Soundness_FRI_Composition_Residuals
begin

text \<open>
  Small support/extraction facts for the composition FRI reachable gap.  These
  are factored out to avoid large direct proofs that stall theory finalization.
\<close>

context soundness
begin

definition composition_fri_reachable_verifier_tie_empty_header_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_reachable_verifier_tie_empty_header_gap s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers.
      composition_fri_reachable_verifier_tie_gap s out \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      composition_roots = [])"

lemma composition_fri_bad_with_reachable_partial_candidate_imp_accepted:
  assumes "composition_fri_bad_with_reachable_partial_candidate s out"
  shows "accepted out"
proof (rule composition_fri_bad_with_reachable_partial_candidateE[OF assms])
  fix fr f_roots f_final as dg composition_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table
  assume evidence:
    "composition_fri_partial_candidate_evidence s out fr f_roots
      f_final as dg composition_roots final trace_query_idxs
      trace_openings composition_query_idxs composition_openings
      trace_table composition_table"
  have partial:
    "accepted_with_partial_initial_openings s out fr f_roots f_final
      as dg composition_roots final trace_query_idxs trace_openings
      composition_query_idxs composition_openings"
    by (rule composition_fri_partial_candidate_evidenceD(1)[OF evidence])
  then show "accepted out"
    by (rule accepted_with_partial_initial_openings_imp_accepted)
qed

lemma composition_fri_reachable_verifier_tie_gap_imp_reachable_bad:
  assumes "composition_fri_reachable_verifier_tie_gap s out"
  shows "composition_fri_bad_with_reachable_partial_candidate s out"
  using assms unfolding composition_fri_reachable_verifier_tie_gap_def by simp

lemma composition_fri_reachable_verifier_tie_gap_imp_accepted:
  assumes "composition_fri_reachable_verifier_tie_gap s out"
  shows "accepted out"
  by (rule composition_fri_bad_with_reachable_partial_candidate_imp_accepted)
    (rule composition_fri_reachable_verifier_tie_gap_imp_reachable_bad[OF assms])

lemma composition_fri_reachable_verifier_tie_empty_header_gapI:
  assumes gap: "composition_fri_reachable_verifier_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and empty: "composition_roots = []"
  shows "composition_fri_reachable_verifier_tie_empty_header_gap s out"
  unfolding composition_fri_reachable_verifier_tie_empty_header_gap_def
  by (intro exI conjI)
    (rule gap, rule fri_openings, rule empty)

lemma composition_fri_reachable_verifier_tie_empty_header_gap_false:
  "\<not> composition_fri_reachable_verifier_tie_empty_header_gap s out"
proof
  assume empty_gap:
    "composition_fri_reachable_verifier_tie_empty_header_gap s out"
  then obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers
  where gap: "composition_fri_reachable_verifier_tie_gap s out"
    and fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    and empty: "composition_roots = []"
    unfolding composition_fri_reachable_verifier_tie_empty_header_gap_def
    by blast
  obtain fr as rest where verifier_header:
    "verifier_header_transcript s fr trace_roots trace_final as fri_dg
      composition_roots composition_final rest"
    by (rule accepted_fri_opening_transcript_headerE[OF fri_openings])
  have raw: "composition_fri_bad_with_reachable_partial_candidate s out"
    using gap unfolding composition_fri_reachable_verifier_tie_gap_def
    by simp
  from composition_fri_bad_with_reachable_partial_candidateE[OF raw]
  obtain fr' f_fri_roots f_final as' dg' composition_fri_roots final
      trace_query_idxs trace_openings composition_query_idxs
      composition_openings trace_table composition_table
  where evidence:
    "composition_fri_partial_candidate_evidence s out fr' f_fri_roots
      f_final as' dg' composition_fri_roots final trace_query_idxs
      trace_openings composition_query_idxs composition_openings
      trace_table composition_table"
    by blast
  have partial:
    "accepted_with_partial_initial_openings s out fr' f_fri_roots
      f_final as' dg' composition_fri_roots final trace_query_idxs
      trace_openings composition_query_idxs composition_openings"
    by (rule composition_fri_partial_candidate_evidenceD(1)[OF evidence])
  have nonempty: "composition_fri_roots \<noteq> []"
    by (rule accepted_with_partial_initial_openings_shapes(1)[OF partial])
  obtain rest' where candidate_header:
    "verifier_header_transcript s fr' f_fri_roots f_final as' dg'
      composition_fri_roots final rest'"
    using accepted_with_partial_initial_openings_shapes(2)[OF partial]
    by blast
  have "composition_fri_roots = composition_roots"
    using verifier_header_transcript_unique
      [OF verifier_header candidate_header]
    by simp
  then show False
    using empty nonempty by simp
qed

lemma wp_composition_fri_reachable_verifier_tie_empty_header_gap_zero:
  "wp_event verify_monad
    (composition_fri_reachable_verifier_tie_empty_header_gap s) s = 0"
  unfolding wp_event_def wp_def dist_expect_def
  by (simp add:
      composition_fri_reachable_verifier_tie_empty_header_gap_false)

lemma composition_fri_reachable_verifier_tie_gap_with_fri_openings_empty_or_nonempty:
  assumes gap: "composition_fri_reachable_verifier_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
  shows
    "composition_fri_reachable_verifier_tie_empty_header_gap s out \<or>
     composition_roots \<noteq> []"
proof (cases "composition_roots = []")
  case True
  have "composition_fri_reachable_verifier_tie_empty_header_gap s out"
    by (rule composition_fri_reachable_verifier_tie_empty_header_gapI
        [OF gap fri_openings True])
  then show ?thesis by simp
next
  case False
  then show ?thesis by simp
qed

lemma composition_fri_verifier_tied_candidate_available_gapI:
  assumes gap: "composition_fri_reachable_verifier_tie_gap s out"
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
  shows "composition_fri_verifier_tied_candidate_available_gap s out"
  unfolding composition_fri_verifier_tied_candidate_available_gap_def
  by (intro exI conjI)
    (rule gap, rule fri_openings, rule aligned, rule trace_candidate,
      rule composition_candidate)

lemma composition_fri_reachable_verifier_tie_gap_with_aligned_openings_imp_merkle_or_candidate_available:
  assumes out_eq: "out = Some (result, final_state)"
    and gap: "composition_fri_reachable_verifier_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
  shows
    "partial_merkle_inconsistency_bad s out \<or>
     composition_fri_verifier_tied_candidate_available_gap s out"
proof (cases "partial_merkle_inconsistency_bad s out")
  case True
  then show ?thesis by simp
next
  case no_merkle: False
  obtain trace_table composition_table where trace_candidate:
    "partial_trace_table_candidate trace_table trace_openings"
    and composition_candidate:
    "partial_composition_table_candidate composition_table
      composition_openings"
    using
      accepted_with_partial_initial_openings_aligned_candidates_if_no_partial_merkle_bad
      [OF aligned[unfolded out_eq] no_merkle[unfolded out_eq]]
    by blast
  have available:
    "composition_fri_verifier_tied_candidate_available_gap s out"
    by (rule composition_fri_verifier_tied_candidate_available_gapI
        [OF gap fri_openings aligned trace_candidate composition_candidate])
  then show ?thesis by simp
qed

lemma composition_fri_reachable_verifier_tie_gap_with_fri_openings_headerE:
  assumes
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
  obtains fr as rest where
    "verifier_header_transcript s fr trace_roots trace_final as fri_dg
      composition_roots composition_final rest"
  by (rule accepted_fri_opening_transcript_headerE[OF assms])

lemma composition_fri_reachable_verifier_tie_gap_with_fri_openings_header_and_branchE:
  assumes gap: "composition_fri_reachable_verifier_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
  obtains fr as rest where
    "verifier_header_transcript s fr trace_roots trace_final as fri_dg
      composition_roots composition_final rest"
    "composition_fri_reachable_verifier_tie_empty_header_gap s out \<or>
     composition_roots \<noteq> []"
proof -
  obtain fr as rest where header:
    "verifier_header_transcript s fr trace_roots trace_final as fri_dg
      composition_roots composition_final rest"
    by (rule composition_fri_reachable_verifier_tie_gap_with_fri_openings_headerE
        [OF fri_openings])
  have branch:
    "composition_fri_reachable_verifier_tie_empty_header_gap s out \<or>
     composition_roots \<noteq> []"
    by (rule
        composition_fri_reachable_verifier_tie_gap_with_fri_openings_empty_or_nonempty
        [OF gap fri_openings])
  show ?thesis
    by (rule that[OF header branch])
qed

lemma composition_fri_reachable_verifier_tie_gap_nonempty_imp_merkle_or_candidate_available:
  assumes out_eq: "out = Some (result, final_state)"
    and gap: "composition_fri_reachable_verifier_tie_gap s out"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and nonempty: "composition_roots \<noteq> []"
  shows
    "partial_merkle_inconsistency_bad s out \<or>
     composition_fri_verifier_tied_candidate_available_gap s out"
proof -
  have split:
    "partial_merkle_inconsistency_bad s (Some (result, final_state)) \<or>
     (\<exists>fr as rest trace_openings composition_openings trace_table
        composition_table.
        verifier_header_transcript s fr trace_roots trace_final as fri_dg
          composition_roots composition_final rest \<and>
        accepted_with_partial_initial_openings_aligned s
          (Some (result, final_state)) fr trace_roots trace_final as fri_dg
          composition_roots composition_final fri_query_idxs trace_openings
          composition_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings)"
    by (rule
        accepted_fri_opening_transcript_obtains_aligned_partial_candidates_or_partial_merkle
        [OF fri_openings[unfolded out_eq] nonempty])
  show ?thesis
  proof (rule disjE[OF split])
    assume "partial_merkle_inconsistency_bad s (Some (result, final_state))"
    then show ?thesis
      by (simp add: out_eq)
  next
    assume
      "\<exists>fr as rest trace_openings composition_openings trace_table
        composition_table.
        verifier_header_transcript s fr trace_roots trace_final as fri_dg
          composition_roots composition_final rest \<and>
        accepted_with_partial_initial_openings_aligned s
          (Some (result, final_state)) fr trace_roots trace_final as fri_dg
          composition_roots composition_final fri_query_idxs trace_openings
          composition_openings \<and>
        partial_trace_table_candidate trace_table trace_openings \<and>
        partial_composition_table_candidate composition_table
          composition_openings"
    then obtain fr as rest trace_openings composition_openings trace_table
        composition_table where aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
      and trace_candidate:
      "partial_trace_table_candidate trace_table trace_openings"
      and composition_candidate:
      "partial_composition_table_candidate composition_table
        composition_openings"
      by (auto simp: out_eq)
    have available:
      "composition_fri_verifier_tied_candidate_available_gap s out"
      by (rule composition_fri_verifier_tied_candidate_available_gapI
          [OF gap fri_openings aligned trace_candidate composition_candidate])
    then show ?thesis by simp
  qed
qed

lemma composition_fri_reachable_verifier_tie_gap_imp_empty_or_merkle_or_candidate_available_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and gap: "composition_fri_reachable_verifier_tie_gap s out"
  shows
    "composition_fri_reachable_verifier_tie_empty_header_gap s out \<or>
     partial_merkle_inconsistency_bad s out \<or>
     composition_fri_verifier_tied_candidate_available_gap s out"
proof -
  have raw: "composition_fri_bad_with_reachable_partial_candidate s out"
    using gap
    unfolding composition_fri_reachable_verifier_tie_gap_def by simp
  have acc: "accepted out"
    by (rule composition_fri_bad_with_reachable_partial_candidate_imp_accepted
        [OF raw])
  obtain result final_state where out_eq: "out = Some (result, final_state)"
    using acc unfolding accepted_def by (cases out) auto
  from verify_monad_accepted_fri_opening_transcript[OF support[unfolded out_eq]]
  obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers
  where fri_openings:
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs
      composition_final fri_query_idxs trace_round_layers
      composition_round_layers"
    unfolding out_eq by blast
  show ?thesis
  proof (cases "composition_roots = []")
    case True
    have "composition_fri_reachable_verifier_tie_empty_header_gap s out"
      by (rule composition_fri_reachable_verifier_tie_empty_header_gapI
          [OF gap fri_openings True])
    then show ?thesis by simp
  next
    case False
    have
      "partial_merkle_inconsistency_bad s out \<or>
       composition_fri_verifier_tied_candidate_available_gap s out"
      by (rule
          composition_fri_reachable_verifier_tie_gap_nonempty_imp_merkle_or_candidate_available
          [OF out_eq gap fri_openings False])
    then show ?thesis by simp
  qed
qed

lemma wp_composition_fri_reachable_verifier_tie_gap_bound_from_empty_merkle_and_candidate_transfer:
  assumes empty_bound:
    "wp_event verify_monad
      (composition_fri_reachable_verifier_tie_empty_header_gap s) s \<le> E"
    and merkle_bound:
      "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and transfer_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_candidate_transfer_gap s) s \<le> T"
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
    by (intro add_mono empty_bound merkle_bound
        wp_composition_fri_verifier_tied_candidate_available_gap_bound_from_transfer_gap
        transfer_bound)
  finally show ?thesis .
qed

lemma composition_fri_reachable_partial_candidate_reduction_from_split_residual_bounds:
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
    and candidate_transfer_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_candidate_transfer_gap s) s \<le> T"
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
        wp_composition_fri_reachable_verifier_tie_gap_bound_from_empty_merkle_and_candidate_transfer
        [OF empty_bound gap_partial_merkle_bound candidate_transfer_bound])
  show ?thesis
    by (rule
        composition_fri_reachable_partial_candidate_reduction_from_verifier_tied_and_gap
        [OF verifier_bound gap_bound total_bound])
qed

lemma composition_fri_reachable_partial_candidate_reduction_from_split_residual_bounds_with_recorded_missing_zero:
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
    and candidate_transfer_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_candidate_transfer_gap s) s \<le> T"
    and total_bound:
    "R + (((P + 0) + N + S + G + P) + A) + (E + (Q + T))
      \<le> composition_fri_error"
  shows "composition_fri_reachable_partial_candidate_reduction_assumption s"
  by (rule
      composition_fri_reachable_partial_candidate_reduction_from_split_residual_bounds
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
     rule candidate_transfer_bound,
     rule total_bound)

end

end
