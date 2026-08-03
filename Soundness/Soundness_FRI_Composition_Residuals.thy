(*  Title:      Stark/Soundness_FRI_Composition_Residuals.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Soundness_FRI_Composition_Residuals
  imports
    Soundness_FRI_Authenticated_Route
    Soundness_FRI_Base_Recorded_Chunk
    Soundness_FRI_Final_Step_Replay
    Soundness_FRI_Raw_Layer_Bounds
    Soundness_FRI_Recorded_Chunk_Replay
begin

text \<open>
  Narrow residual refinements for the verifier-tied composition FRI route.
  This layer keeps the larger authenticated route theory stable while naming
  the exact remaining base-opening gap: the recorded first-layer composition
  FRI chunk is not known to be authenticated.
\<close>

context soundness
begin

definition composition_fri_reachable_verifier_tie_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_reachable_verifier_tie_gap s out \<longleftrightarrow>
    composition_fri_bad_with_reachable_partial_candidate s out \<and>
    \<not> composition_fri_bad_with_verifier_tied_partial_candidate s out"

definition composition_fri_verifier_tied_candidate_transfer_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_candidate_transfer_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table.
      composition_fri_bad_with_reachable_partial_candidate s out \<and>
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

definition composition_fri_verifier_tied_candidate_available_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_candidate_available_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table.
      composition_fri_reachable_verifier_tie_gap s out \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings)"

lemma composition_fri_aligned_candidate_bad_contradicts_verifier_tie_gap:
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
    and trace_low: "trace_table_low_degree trace_table"
    and composition_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
  shows False
proof -
  have "composition_fri_bad_with_verifier_tied_partial_candidate s out"
    unfolding composition_fri_bad_with_verifier_tied_partial_candidate_def
    by (intro exI conjI)
      (rule fri_openings, rule aligned, rule trace_candidate,
        rule composition_candidate, rule trace_low, rule composition_not_low)
  then show False
    using gap unfolding composition_fri_reachable_verifier_tie_gap_def by simp
qed

lemma composition_fri_aligned_candidate_transfer_imp_transfer_gap:
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
    and transfer:
      "\<not> (trace_table_low_degree trace_table \<and>
        \<not> composition_table_low_degree maxDegree composition_table)"
  shows "composition_fri_verifier_tied_candidate_transfer_gap s out"
proof -
  have raw: "composition_fri_bad_with_reachable_partial_candidate s out"
    using gap unfolding composition_fri_reachable_verifier_tie_gap_def
    by simp
  show ?thesis
    unfolding composition_fri_verifier_tied_candidate_transfer_gap_def
    by (intro exI conjI)
      (rule raw, rule fri_openings, rule aligned, rule trace_candidate,
        rule composition_candidate, rule transfer)
qed

lemma composition_fri_verifier_tied_candidate_available_gap_imp_transfer_gap:
  assumes "composition_fri_verifier_tied_candidate_available_gap s out"
  shows "composition_fri_verifier_tied_candidate_transfer_gap s out"
proof -
  obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table
  where gap: "composition_fri_reachable_verifier_tie_gap s out"
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
    using assms
    unfolding composition_fri_verifier_tied_candidate_available_gap_def
    by blast
  show ?thesis
  proof (cases
      "trace_table_low_degree trace_table \<and>
       \<not> composition_table_low_degree maxDegree composition_table")
    case True
    have False
      by (rule composition_fri_aligned_candidate_bad_contradicts_verifier_tie_gap
          [OF gap fri_openings aligned trace_candidate composition_candidate
            True[THEN conjunct1] True[THEN conjunct2]])
    then show ?thesis by simp
  next
    case False
    show ?thesis
      by (rule composition_fri_aligned_candidate_transfer_imp_transfer_gap
          [OF gap fri_openings aligned trace_candidate composition_candidate
            False])
  qed
qed

lemma wp_composition_fri_verifier_tied_candidate_available_gap_bound_from_transfer_gap:
  assumes transfer_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_candidate_transfer_gap s) s \<le> T"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_candidate_available_gap s) s \<le> T"
  by (rule order_trans[OF _ transfer_bound])
    (rule wp_event_mono,
      rule composition_fri_verifier_tied_candidate_available_gap_imp_transfer_gap)

lemma composition_fri_verifier_tied_reduction_staged_bound:
  assumes reductions:
    "\<And>data attacker_state.
      Some (data, attacker_state) \<in>
        set_dist (execute (checked_staged_transcript_program A)
          adversary_initial_state) \<Longrightarrow>
      composition_fri_verifier_tied_reduction
        (verifier_state_from_adversary attacker_state
          (staged_proof_transcript data))"
  shows
    "wp_event (checked_staged_security_experiment_with_data_state A)
      (staged_security_with_data_state_verifier_event
        composition_fri_bad_with_verifier_tied_partial_candidate)
      adversary_initial_state \<le> composition_fri_error"
  by (rule composition_fri_bad_with_verifier_tied_partial_candidates_staged_bound)
    (rule composition_fri_verifier_tied_reductionD[OF reductions])

lemma composition_fri_verifier_tied_reduction_from_reachable_reduction:
  assumes "composition_fri_reachable_partial_candidate_reduction_assumption s"
  shows "composition_fri_verifier_tied_reduction s"
proof -
  have reachable:
    "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate s) s \<le>
      composition_fri_error"
    using assms
    unfolding
      composition_fri_reachable_partial_candidate_reduction_assumption_def
    by simp
  show ?thesis
    unfolding composition_fri_verifier_tied_reduction_def
    by (rule order_trans[OF _ reachable])
      (rule wp_event_mono,
        rule composition_fri_bad_with_verifier_tied_imp_reachable_partial_candidate)
qed

lemma composition_fri_reachable_imp_verifier_tied_or_gap:
  assumes "composition_fri_bad_with_reachable_partial_candidate s out"
  shows
    "composition_fri_bad_with_verifier_tied_partial_candidate s out \<or>
     composition_fri_reachable_verifier_tie_gap s out"
  using assms
  unfolding composition_fri_reachable_verifier_tie_gap_def
  by blast

lemma wp_composition_fri_reachable_bound_from_verifier_tied_and_gap:
  fixes V G :: prob
  assumes verifier_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s \<le> V"
    and gap_bound:
      "wp_event verify_monad
        (composition_fri_reachable_verifier_tie_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate s) s \<le> V + G"
proof -
  have "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          composition_fri_bad_with_verifier_tied_partial_candidate s out \<or>
          composition_fri_reachable_verifier_tie_gap s out) s"
    by (rule wp_event_mono)
      (rule composition_fri_reachable_imp_verifier_tied_or_gap)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_bad_with_verifier_tied_partial_candidate s) s +
      wp_event verify_monad
        (composition_fri_reachable_verifier_tie_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> V + G"
    by (rule add_mono[OF verifier_bound gap_bound])
  finally show ?thesis .
qed

lemma composition_fri_reachable_partial_candidate_reduction_from_verifier_tied_and_gap:
  fixes V G :: prob
  assumes verifier_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s \<le> V"
    and gap_bound:
      "wp_event verify_monad
        (composition_fri_reachable_verifier_tie_gap s) s \<le> G"
    and total_bound: "V + G \<le> composition_fri_error"
  shows "composition_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have old_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_reachable_partial_candidate s) s \<le> V + G"
    by (rule wp_composition_fri_reachable_bound_from_verifier_tied_and_gap
        [OF verifier_bound gap_bound])
  show ?thesis
    unfolding
      composition_fri_reachable_partial_candidate_reduction_assumption_def
    by (rule order_trans[OF old_bound total_bound])
qed

definition composition_fri_verifier_tied_recorded_base_chunk_auth_missing
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_recorded_base_chunk_auth_missing s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table round_idx xp xp_path xn xn_path
        result final_state.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      round_idx < length fri_query_idxs \<and>
      0 < length composition_bs \<and>
      fri_layer_step_evidence
        (composition_roots ! 0)
        (composition_bs ! 0)
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len composition_roots 0)
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx composition_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value composition_roots composition_bs
          fri_query_idxs round_idx 0 xp xn)
        (composition_round_layers ! round_idx ! 0) \<and>
      \<not> fri_opening_matches_table
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        composition_table xp xn \<and>
      \<not> fri_layer_chunk_authenticated (composition_roots ! 0)
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        (composition_round_layers ! round_idx ! 0) final_state)"

lemma composition_fri_verifier_tied_recorded_base_chunk_auth_missing_false:
  assumes
    "composition_fri_verifier_tied_recorded_base_chunk_auth_missing s out"
  shows False
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table round_idx xp xp_path
      xn xn_path result final_state
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and round_bound: "round_idx < length fri_query_idxs"
    and composition_bs_nonempty: "0 < length composition_bs"
    and missing:
      "\<not> fri_layer_chunk_authenticated (composition_roots ! 0)
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        (composition_round_layers ! round_idx ! 0) final_state"
    unfolding
      composition_fri_verifier_tied_recorded_base_chunk_auth_missing_def
    by blast
  have len_composition_bs:
    "length composition_bs = length composition_roots"
    using accepted_fri_opening_transcript_shapes(4)[OF fri_openings] .
  have composition_nonempty: "0 < length composition_roots"
    using composition_bs_nonempty len_composition_bs by simp
  have len_query: "length fri_query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes(7)[OF fri_openings] .
  have round_bound_rounds: "round_idx < rounds"
    using round_bound len_query by simp
  have auth:
    "fri_layer_chunk_authenticated (composition_roots ! 0) (clength * scale)
      (fri_query_idxs ! round_idx)
      (composition_round_layers ! round_idx ! 0) final_state"
    by (rule
        accepted_fri_opening_transcript_composition_base_recorded_chunk_authenticated_at
          [OF fri_openings out_eq round_bound_rounds composition_nonempty])
  have len0:
    "fri_evidence_layer_len composition_roots 0 = clength * scale"
    using composition_nonempty
    unfolding fri_evidence_layer_len_def
    by (cases composition_roots) simp_all
  have idx0:
    "fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0 =
      fri_query_idxs ! round_idx"
    using composition_nonempty
    unfolding fri_evidence_layer_idx_def
    by (cases composition_roots) simp_all
  show False
    using missing auth unfolding len0 idx0 by contradiction
qed

lemma wp_composition_fri_verifier_tied_recorded_base_chunk_auth_missing_zero:
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s)
      s \<le> 0"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s) s
    \<le> wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono)
      (rule composition_fri_verifier_tied_recorded_base_chunk_auth_missing_false)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis .
qed

lemma composition_fri_verifier_tied_base_chunk_auth_gap_imp_recorded_missing:
  assumes "composition_fri_verifier_tied_base_chunk_auth_gap s out"
  shows
    "composition_fri_verifier_tied_recorded_base_chunk_auth_missing s out"
proof -
  from assms have base:
    "composition_fri_verifier_tied_sampled_base_opening_conflict s out"
    and no_auth:
      "\<not> composition_fri_verifier_tied_authenticated_base_opening_conflict
        s out"
    unfolding composition_fri_verifier_tied_base_chunk_auth_gap_def
    by simp_all
  from base obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and generic:
      "generic_fri_sampled_base_opening_conflict composition_table
        composition_roots composition_bs fri_query_idxs
        composition_round_layers"
    unfolding composition_fri_verifier_tied_sampled_base_opening_conflict_def
    by blast
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  from generic obtain round_idx xp xp_path xn xn_path where
    round_bound: "round_idx < length fri_query_idxs"
    and composition_bs_nonempty: "0 < length composition_bs"
    and step:
      "fri_layer_step_evidence
        (composition_roots ! 0)
        (composition_bs ! 0)
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        1
        (fri_sibling_index (fri_evidence_layer_len composition_roots 0)
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0))
        xp xp_path xn xn_path
        (fri_evidence_next_idx composition_roots fri_query_idxs round_idx 0)
        (fri_evidence_next_value composition_roots composition_bs
          fri_query_idxs round_idx 0 xp xn)
        (composition_round_layers ! round_idx ! 0)"
    and no_match:
      "\<not> fri_opening_matches_table
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        composition_table xp xn"
    unfolding generic_fri_sampled_base_opening_conflict_def
    by blast
  have missing:
    "\<not> fri_layer_chunk_authenticated (composition_roots ! 0)
      (fri_evidence_layer_len composition_roots 0)
      (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
      (composition_round_layers ! round_idx ! 0) final_state"
  proof
    assume auth:
      "fri_layer_chunk_authenticated (composition_roots ! 0)
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        (composition_round_layers ! round_idx ! 0) final_state"
    have
      "composition_fri_verifier_tied_authenticated_base_opening_conflict
        s out"
      unfolding composition_fri_verifier_tied_authenticated_base_opening_conflict_def
      by (intro exI conjI)
        (rule out_eq, rule fri_openings, rule aligned, rule trace_cand,
          rule comp_cand, rule trace_low, rule comp_not_low, rule round_bound,
          rule composition_bs_nonempty, rule step, rule no_match, rule auth)
    then show False
      using no_auth by contradiction
  qed
  show ?thesis
    unfolding composition_fri_verifier_tied_recorded_base_chunk_auth_missing_def
    by (intro exI conjI)
      (rule out_eq, rule fri_openings, rule aligned, rule trace_cand,
        rule comp_cand, rule trace_low, rule comp_not_low, rule round_bound,
        rule composition_bs_nonempty, rule step, rule no_match, rule missing)
qed

lemma wp_composition_fri_verifier_tied_base_chunk_auth_gap_bound_from_recorded_missing:
  fixes M :: prob
  assumes missing_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s)
      s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_base_chunk_auth_gap s) s \<le> M"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_base_chunk_auth_gap s) s \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s) s"
    by (rule wp_event_mono)
      (rule composition_fri_verifier_tied_base_chunk_auth_gap_imp_recorded_missing)
  then show ?thesis
    by (rule order_trans[OF _ missing_bound])
qed

lemma wp_composition_fri_verifier_tied_sampled_base_bound_from_partial_merkle_and_recorded_missing:
  fixes M :: prob
  assumes missing_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s)
      s \<le> M"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_base_opening_conflict s) s
      \<le> wp_event verify_monad (partial_merkle_inconsistency_bad s) s + M"
  by (rule wp_composition_fri_verifier_tied_sampled_base_bound_from_partial_merkle_and_auth_gap)
    (rule
      wp_composition_fri_verifier_tied_base_chunk_auth_gap_bound_from_recorded_missing
        [OF missing_bound])

lemma wp_composition_fri_verifier_tied_without_same_bound_from_partial_merkle_recorded_missing_and_branches:
  fixes M N S F :: prob
  assumes missing_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s)
      s \<le> M"
    and next_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_next_value_conflict s) s \<le> N"
    and successor_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_successor_opening_conflict s)
        s \<le> S"
    and final_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_final_value_conflict s) s \<le> F"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le> (wp_event verify_monad (partial_merkle_inconsistency_bad s) s + M) + N + S + F"
  by (rule wp_composition_fri_verifier_tied_without_same_bound_from_branches)
    (rule wp_composition_fri_verifier_tied_sampled_base_bound_from_partial_merkle_and_recorded_missing
      [OF missing_bound],
     rule next_bound,
     rule successor_bound,
     rule final_bound)

lemma wp_composition_fri_verifier_tied_authenticated_conflict_bound_from_recorded_missing_and_branches:
  fixes P M N S F :: prob
  assumes partial_merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and missing_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s)
        s \<le> M"
    and next_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_next_value_conflict s) s \<le> N"
    and successor_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_successor_opening_conflict s)
        s \<le> S"
    and final_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_final_value_conflict s) s \<le> F"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> (P + M) + N + S + F + P"
proof -
  have without_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer s)
      s \<le> (P + M) + N + S + F"
  proof -
    have "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict_without_same_layer s)
        s \<le>
        (wp_event verify_monad (partial_merkle_inconsistency_bad s) s + M)
        + N + S + F"
      by (rule
          wp_composition_fri_verifier_tied_without_same_bound_from_partial_merkle_recorded_missing_and_branches
            [OF missing_bound next_bound successor_bound final_bound])
    also have "... \<le> (P + M) + N + S + F"
      by (intro add_mono partial_merkle_bound order_refl)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule
        wp_composition_fri_verifier_tied_authenticated_conflict_bound_from_without_same_and_merkle
          [OF without_bound partial_merkle_bound])
qed

definition composition_fri_verifier_tied_next_value_replay_checked_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_next_value_replay_checked_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table round_idx round_idx' layer_idx v v'.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      round_idx < length fri_query_idxs \<and>
      round_idx' < length fri_query_idxs \<and>
      layer_idx < length composition_bs \<and>
      fri_evidence_next_idx composition_roots fri_query_idxs round_idx
        layer_idx =
      fri_evidence_next_idx composition_roots fri_query_idxs round_idx'
        layer_idx \<and>
      generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx layer_idx v \<and>
      generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx' layer_idx v' \<and>
      v \<noteq> v' \<and>
      v = v')"

definition composition_fri_verifier_tied_next_value_replay_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_next_value_replay_gap s out \<longleftrightarrow>
    composition_fri_verifier_tied_sampled_next_value_conflict s out \<and>
    \<not> composition_fri_verifier_tied_next_value_replay_checked_conflict
      s out"

lemma composition_fri_verifier_tied_next_value_replay_checked_conflict_false:
  "\<not> composition_fri_verifier_tied_next_value_replay_checked_conflict s out"
  unfolding composition_fri_verifier_tied_next_value_replay_checked_conflict_def
  by blast

lemma composition_fri_verifier_tied_sampled_next_value_imp_replay_gap:
  assumes "composition_fri_verifier_tied_sampled_next_value_conflict s out"
  shows "composition_fri_verifier_tied_next_value_replay_gap s out"
  using assms composition_fri_verifier_tied_next_value_replay_checked_conflict_false
  unfolding composition_fri_verifier_tied_next_value_replay_gap_def
  by simp

lemma composition_fri_verifier_tied_sampled_next_value_conflictE:
  assumes "composition_fri_verifier_tied_sampled_next_value_conflict s out"
  obtains trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table round_idx round_idx' layer_idx v v'
  where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final fri_query_idxs
      trace_openings composition_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    "trace_table_low_degree trace_table"
    "\<not> composition_table_low_degree maxDegree composition_table"
    "round_idx < length fri_query_idxs"
    "round_idx' < length fri_query_idxs"
    "layer_idx < length composition_bs"
    "fri_evidence_next_idx composition_roots fri_query_idxs round_idx
      layer_idx =
     fri_evidence_next_idx composition_roots fri_query_idxs round_idx'
      layer_idx"
    "generic_fri_round_forced_next_value composition_roots composition_bs
      fri_query_idxs composition_round_layers round_idx layer_idx v"
    "generic_fri_round_forced_next_value composition_roots composition_bs
      fri_query_idxs composition_round_layers round_idx' layer_idx v'"
    "v \<noteq> v'"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and conflict:
      "generic_fri_sampled_next_value_conflict composition_roots
        composition_bs fri_query_idxs composition_round_layers"
    unfolding composition_fri_verifier_tied_sampled_next_value_conflict_def
    by blast
  from generic_fri_sampled_next_value_conflictE[OF conflict]
  obtain round_idx round_idx' layer_idx v v'
    where round_bound: "round_idx < length fri_query_idxs"
    and round_bound': "round_idx' < length fri_query_idxs"
    and layer_bound: "layer_idx < length composition_bs"
    and same_idx:
      "fri_evidence_next_idx composition_roots fri_query_idxs round_idx
        layer_idx =
       fri_evidence_next_idx composition_roots fri_query_idxs round_idx'
        layer_idx"
    and forced:
      "generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx layer_idx v"
    and forced':
      "generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx' layer_idx v'"
    and neq: "v \<noteq> v'"
    by blast
  show ?thesis
    by (rule that[OF fri_openings aligned trace_cand comp_cand trace_low
          comp_not_low round_bound round_bound' layer_bound same_idx forced
          forced' neq])
qed

lemma wp_composition_fri_verifier_tied_sampled_next_value_bound_from_replay_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_next_value_replay_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_next_value_conflict s) s \<le> G"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_next_value_conflict s) s \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_next_value_replay_gap s) s"
    by (rule wp_event_mono)
      (rule composition_fri_verifier_tied_sampled_next_value_imp_replay_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

definition composition_fri_verifier_tied_successor_replay_checked_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_successor_replay_checked_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table source_round target_round layer_idx
        v xp xp_path xn xn_path.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      source_round < length fri_query_idxs \<and>
      target_round < length fri_query_idxs \<and>
      Suc layer_idx < length composition_bs \<and>
      generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers source_round layer_idx v \<and>
      fri_layer_step_evidence
        (composition_roots ! Suc layer_idx)
        (composition_bs ! Suc layer_idx)
        (fri_evidence_layer_len composition_roots (Suc layer_idx))
        (fri_evidence_layer_idx composition_roots fri_query_idxs target_round
          (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len composition_roots (Suc layer_idx))
          (fri_evidence_layer_idx composition_roots fri_query_idxs
            target_round (Suc layer_idx)))
        xp xp_path xn xn_path
        (fri_evidence_next_idx composition_roots fri_query_idxs target_round
          (Suc layer_idx))
        (fri_evidence_next_value composition_roots composition_bs
          fri_query_idxs target_round (Suc layer_idx) xp xn)
        (composition_round_layers ! target_round ! Suc layer_idx) \<and>
      ((fri_evidence_next_idx composition_roots fri_query_idxs source_round
          layer_idx =
        fri_evidence_layer_idx composition_roots fri_query_idxs target_round
          (Suc layer_idx) \<and>
        v \<noteq> xp \<and> v = xp) \<or>
       (fri_evidence_next_idx composition_roots fri_query_idxs source_round
          layer_idx =
        fri_sibling_index
          (fri_evidence_layer_len composition_roots (Suc layer_idx))
          (fri_evidence_layer_idx composition_roots fri_query_idxs
            target_round (Suc layer_idx)) \<and>
        v \<noteq> xn \<and> v = xn)))"

definition composition_fri_verifier_tied_successor_replay_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_successor_replay_gap s out \<longleftrightarrow>
    composition_fri_verifier_tied_sampled_successor_opening_conflict s out \<and>
    \<not> composition_fri_verifier_tied_successor_replay_checked_conflict
      s out"

lemma composition_fri_verifier_tied_successor_replay_checked_conflict_false:
  "\<not> composition_fri_verifier_tied_successor_replay_checked_conflict s out"
  unfolding
    composition_fri_verifier_tied_successor_replay_checked_conflict_def
  by blast

lemma composition_fri_verifier_tied_sampled_successor_imp_replay_gap:
  assumes
    "composition_fri_verifier_tied_sampled_successor_opening_conflict s out"
  shows "composition_fri_verifier_tied_successor_replay_gap s out"
  using assms
    composition_fri_verifier_tied_successor_replay_checked_conflict_false
  unfolding composition_fri_verifier_tied_successor_replay_gap_def
  by simp

lemma composition_fri_verifier_tied_sampled_successor_opening_conflictE:
  assumes
    "composition_fri_verifier_tied_sampled_successor_opening_conflict s out"
  obtains trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table source_round target_round layer_idx v
      xp xp_path xn xn_path
  where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final fri_query_idxs
      trace_openings composition_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    "trace_table_low_degree trace_table"
    "\<not> composition_table_low_degree maxDegree composition_table"
    "source_round < length fri_query_idxs"
    "target_round < length fri_query_idxs"
    "Suc layer_idx < length composition_bs"
    "generic_fri_round_forced_next_value composition_roots composition_bs
      fri_query_idxs composition_round_layers source_round layer_idx v"
    "fri_layer_step_evidence
      (composition_roots ! Suc layer_idx)
      (composition_bs ! Suc layer_idx)
      (fri_evidence_layer_len composition_roots (Suc layer_idx))
      (fri_evidence_layer_idx composition_roots fri_query_idxs target_round
        (Suc layer_idx))
      (2 ^ Suc layer_idx)
      (fri_sibling_index
        (fri_evidence_layer_len composition_roots (Suc layer_idx))
        (fri_evidence_layer_idx composition_roots fri_query_idxs
          target_round (Suc layer_idx)))
      xp xp_path xn xn_path
      (fri_evidence_next_idx composition_roots fri_query_idxs target_round
        (Suc layer_idx))
      (fri_evidence_next_value composition_roots composition_bs
        fri_query_idxs target_round (Suc layer_idx) xp xn)
      (composition_round_layers ! target_round ! Suc layer_idx)"
    "(fri_evidence_next_idx composition_roots fri_query_idxs source_round
        layer_idx =
      fri_evidence_layer_idx composition_roots fri_query_idxs target_round
        (Suc layer_idx) \<and>
      v \<noteq> xp) \<or>
     (fri_evidence_next_idx composition_roots fri_query_idxs source_round
        layer_idx =
      fri_sibling_index
        (fri_evidence_layer_len composition_roots (Suc layer_idx))
        (fri_evidence_layer_idx composition_roots fri_query_idxs
          target_round (Suc layer_idx)) \<and>
      v \<noteq> xn)"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and conflict:
      "generic_fri_sampled_successor_opening_conflict composition_roots
        composition_bs fri_query_idxs composition_round_layers"
    unfolding
      composition_fri_verifier_tied_sampled_successor_opening_conflict_def
    by blast
  from generic_fri_sampled_successor_opening_conflictE[OF conflict]
  obtain source_round target_round layer_idx v xp xp_path xn xn_path
    where source_bound: "source_round < length fri_query_idxs"
    and target_bound: "target_round < length fri_query_idxs"
    and layer_bound: "Suc layer_idx < length composition_bs"
    and forced:
      "generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers source_round layer_idx v"
    and step:
      "fri_layer_step_evidence
        (composition_roots ! Suc layer_idx)
        (composition_bs ! Suc layer_idx)
        (fri_evidence_layer_len composition_roots (Suc layer_idx))
        (fri_evidence_layer_idx composition_roots fri_query_idxs
          target_round (Suc layer_idx))
        (2 ^ Suc layer_idx)
        (fri_sibling_index
          (fri_evidence_layer_len composition_roots (Suc layer_idx))
          (fri_evidence_layer_idx composition_roots fri_query_idxs
            target_round (Suc layer_idx)))
        xp xp_path xn xn_path
        (fri_evidence_next_idx composition_roots fri_query_idxs
          target_round (Suc layer_idx))
        (fri_evidence_next_value composition_roots composition_bs
          fri_query_idxs target_round (Suc layer_idx) xp xn)
        (composition_round_layers ! target_round ! Suc layer_idx)"
    and cases:
      "(fri_evidence_next_idx composition_roots fri_query_idxs source_round
          layer_idx =
        fri_evidence_layer_idx composition_roots fri_query_idxs target_round
          (Suc layer_idx) \<and>
        v \<noteq> xp) \<or>
       (fri_evidence_next_idx composition_roots fri_query_idxs source_round
          layer_idx =
        fri_sibling_index
          (fri_evidence_layer_len composition_roots (Suc layer_idx))
          (fri_evidence_layer_idx composition_roots fri_query_idxs
            target_round (Suc layer_idx)) \<and>
        v \<noteq> xn)"
    by blast
  show ?thesis
    by (rule that[OF fri_openings aligned trace_cand comp_cand trace_low
          comp_not_low source_bound target_bound layer_bound forced step
          cases])
qed

lemma wp_composition_fri_verifier_tied_sampled_successor_bound_from_replay_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_successor_replay_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_successor_opening_conflict s)
      s \<le> G"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_successor_opening_conflict s)
      s \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_successor_replay_gap s) s"
    by (rule wp_event_mono)
      (rule composition_fri_verifier_tied_sampled_successor_imp_replay_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

definition composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
      s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table result final_state.
      out = Some (result, final_state) \<and>
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
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_authenticated_slot_recorded_chunk_gap composition_roots
        fri_query_idxs composition_round_layers final_state)"

definition composition_fri_verifier_tied_final_value_replay_checked_conflict
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_final_value_replay_checked_conflict s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table round_idx v.
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      0 < length composition_bs \<and>
      round_idx < length fri_query_idxs \<and>
      generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx
        (length composition_bs - 1) v \<and>
      v \<noteq> composition_final \<and>
      v = composition_final)"

definition composition_fri_verifier_tied_final_value_replay_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_final_value_replay_gap s out \<longleftrightarrow>
    composition_fri_verifier_tied_sampled_final_value_conflict s out \<and>
    \<not> composition_fri_verifier_tied_final_value_replay_checked_conflict
      s out"

lemma composition_fri_verifier_tied_sampled_final_value_conflictE:
  assumes
    "composition_fri_verifier_tied_sampled_final_value_conflict s out"
  obtains trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table round_idx v
  where
    "accepted_fri_opening_transcript s out trace_roots trace_bs
      trace_final fri_dg composition_roots composition_bs composition_final
      fri_query_idxs trace_round_layers composition_round_layers"
    "accepted_with_partial_initial_openings_aligned s out fr trace_roots
      trace_final as fri_dg composition_roots composition_final fri_query_idxs
      trace_openings composition_openings"
    "partial_trace_table_candidate trace_table trace_openings"
    "partial_composition_table_candidate composition_table
      composition_openings"
    "trace_table_low_degree trace_table"
    "\<not> composition_table_low_degree maxDegree composition_table"
    "0 < length composition_bs"
    "round_idx < length fri_query_idxs"
    "generic_fri_round_forced_next_value composition_roots composition_bs
      fri_query_idxs composition_round_layers round_idx
      (length composition_bs - 1) v"
    "v \<noteq> composition_final"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table where
    fri_openings:
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
    and composition_nonlow:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and final_conflict:
      "generic_fri_sampled_final_value_conflict composition_roots
        composition_bs composition_final fri_query_idxs
        composition_round_layers"
    unfolding composition_fri_verifier_tied_sampled_final_value_conflict_def
    by blast
  from generic_fri_sampled_final_value_conflictE[OF final_conflict]
  obtain round_idx v where
    nonempty: "0 < length composition_bs"
    and round_bound: "round_idx < length fri_query_idxs"
    and forced:
      "generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx
        (length composition_bs - 1) v"
    and neq: "v \<noteq> composition_final"
    by blast
  show ?thesis
    by (rule that[OF fri_openings aligned trace_candidate
          composition_candidate trace_low composition_nonlow nonempty
          round_bound forced neq])
qed

lemma composition_fri_verifier_tied_final_value_replay_checked_conflict_false:
  "\<not> composition_fri_verifier_tied_final_value_replay_checked_conflict s out"
  unfolding composition_fri_verifier_tied_final_value_replay_checked_conflict_def
  by blast

lemma composition_fri_verifier_tied_sampled_final_value_imp_replay_gap:
  assumes "composition_fri_verifier_tied_sampled_final_value_conflict s out"
  shows "composition_fri_verifier_tied_final_value_replay_gap s out"
  using assms composition_fri_verifier_tied_final_value_replay_checked_conflict_false
  unfolding composition_fri_verifier_tied_final_value_replay_gap_def
  by simp

lemma wp_composition_fri_verifier_tied_sampled_final_value_bound_from_replay_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_final_value_conflict s) s \<le> G"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_final_value_conflict s) s \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap s) s"
    by (rule wp_event_mono)
      (rule composition_fri_verifier_tied_sampled_final_value_imp_replay_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

definition composition_fri_verifier_tied_final_value_authenticated_replay_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_final_value_authenticated_replay_gap s out
    \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table result final_state round_idx v.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final fri_query_idxs
        trace_openings composition_openings \<and>
      partial_trace_table_candidate trace_table trace_openings \<and>
      partial_composition_table_candidate composition_table
        composition_openings \<and>
      trace_table_low_degree trace_table \<and>
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      0 < length composition_bs \<and>
      round_idx < length fri_query_idxs \<and>
      generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx
        (length composition_bs - 1) v \<and>
      v \<noteq> composition_final \<and>
      \<not> partial_merkle_inconsistency_bad s out \<and>
      generic_fri_recorded_layer_chunk_authenticated composition_roots
        fri_query_idxs composition_round_layers final_state round_idx
        (length composition_bs - 1))"

definition composition_fri_verifier_tied_final_value_selected_step_missing_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_final_value_selected_step_missing_gap s out
    \<longleftrightarrow>
    composition_fri_verifier_tied_final_value_authenticated_replay_gap s out \<and>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers result final_state round_idx v.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      0 < length composition_bs \<and>
      round_idx < length fri_query_idxs \<and>
      generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx
        (length composition_bs - 1) v \<and>
      v \<noteq> composition_final \<and>
      \<not> partial_merkle_inconsistency_bad s out \<and>
      generic_fri_recorded_layer_chunk_authenticated composition_roots
        fri_query_idxs composition_round_layers final_state round_idx
        (length composition_bs - 1) \<and>
      (\<forall>actual_chunk axp axp_path axn axn_path.
        \<not> (fri_layer_chunk_authenticated
          (composition_roots ! (length composition_bs - 1))
          (fri_evidence_layer_len composition_roots (length composition_bs - 1))
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          actual_chunk final_state \<and>
        fri_layer_step_evidence
          (composition_roots ! (length composition_bs - 1))
          (composition_bs ! (length composition_bs - 1))
          (fri_evidence_layer_len composition_roots (length composition_bs - 1))
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          (2 ^ (length composition_bs - 1))
          (fri_sibling_index
            (fri_evidence_layer_len composition_roots (length composition_bs - 1))
            (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
              (length composition_bs - 1)))
          axp axp_path axn axn_path
          (fri_evidence_next_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          composition_final actual_chunk)))"

lemma composition_fri_verifier_tied_final_value_selected_step_missing_gap_false_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and gap:
      "composition_fri_verifier_tied_final_value_selected_step_missing_gap
        s out"
  shows False
proof -
  from gap obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers result final_state round_idx v
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and nonempty_bs: "0 < length composition_bs"
    and round_bound: "round_idx < length fri_query_idxs"
    and missing:
      "\<And>actual_chunk axp axp_path axn axn_path.
        \<not> (fri_layer_chunk_authenticated
          (composition_roots ! (length composition_bs - 1))
          (fri_evidence_layer_len composition_roots (length composition_bs - 1))
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          actual_chunk final_state \<and>
        fri_layer_step_evidence
          (composition_roots ! (length composition_bs - 1))
          (composition_bs ! (length composition_bs - 1))
          (fri_evidence_layer_len composition_roots (length composition_bs - 1))
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          (2 ^ (length composition_bs - 1))
          (fri_sibling_index
            (fri_evidence_layer_len composition_roots (length composition_bs - 1))
            (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
              (length composition_bs - 1)))
          axp axp_path axn axn_path
          (fri_evidence_next_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          composition_final actual_chunk)"
    unfolding
      composition_fri_verifier_tied_final_value_selected_step_missing_gap_def
    by blast
  have outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using support out_eq by simp
  have challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs fri_dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF fri_openings]
      out_eq by simp
  have degree_bound: "to_nat fri_dg \<le> maxDegree"
    by (rule verify_monad_accepted_fri_challenges_degree_bound
        [OF outcome challenges])
  have len_bs_roots: "length composition_bs = length composition_roots"
    using accepted_fri_opening_transcript_shapes(4)[OF fri_openings] .
  have nonempty_roots: "0 < length composition_roots"
    using nonempty_bs len_bs_roots by simp
  have round_bound_rounds: "round_idx < rounds"
    using round_bound
      accepted_fri_opening_transcript_shapes(7)[OF fri_openings]
    by simp
  have raw_layer:
    "\<And>raw.
      0 < fri_layer_lengths (length composition_roots) (clength * scale) !
        (length composition_roots - 1) \<and>
      fri_layer_indices (length composition_roots) (index (to_nat raw))
        (clength * scale) ! (length composition_roots - 1) <
      fri_layer_lengths (length composition_roots) (clength * scale) !
        (length composition_roots - 1)"
    by (rule accepted_fri_opening_transcript_composition_raw_layer_bound
        [OF fri_openings degree_bound])
      (use nonempty_roots in simp)
  from accepted_fri_opening_transcript_composition_final_step_evidence_at
      [OF fri_openings out_eq round_bound_rounds nonempty_roots raw_layer]
  obtain actual_chunk axp axp_path axn axn_path where
    auth:
      "fri_layer_chunk_authenticated
        (composition_roots ! (length composition_roots - 1))
        (fri_evidence_layer_len composition_roots (length composition_roots - 1))
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
          (length composition_roots - 1))
        actual_chunk final_state"
    and step:
      "fri_layer_step_evidence
        (composition_roots ! (length composition_roots - 1))
        (composition_bs ! (length composition_roots - 1))
        (fri_evidence_layer_len composition_roots (length composition_roots - 1))
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
          (length composition_roots - 1))
        (2 ^ (length composition_roots - 1))
        (fri_sibling_index
          (fri_evidence_layer_len composition_roots (length composition_roots - 1))
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
            (length composition_roots - 1)))
        axp axp_path axn axn_path
        (fri_evidence_next_idx composition_roots fri_query_idxs round_idx
          (length composition_roots - 1))
        composition_final actual_chunk"
    by blast
  show False
    using missing[of actual_chunk axp axp_path axn axn_path]
      auth step len_bs_roots
    by simp
qed

lemma wp_composition_fri_verifier_tied_final_value_selected_step_missing_gap_zero:
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_selected_step_missing_gap s)
      s \<le> (0::prob)"
proof -
  have
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_selected_step_missing_gap s)
      s \<le> wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono_on_support)
      (rule
        composition_fri_verifier_tied_final_value_selected_step_missing_gap_false_on_support)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis by simp
qed

lemma composition_fri_verifier_tied_final_value_authenticated_replay_gap_imp_selected_step_missing:
  assumes
    "composition_fri_verifier_tied_final_value_authenticated_replay_gap s out"
  shows
    "composition_fri_verifier_tied_final_value_selected_step_missing_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table result final_state round_idx v
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and nonempty: "0 < length composition_bs"
    and round_bound: "round_idx < length fri_query_idxs"
    and forced:
      "generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx
        (length composition_bs - 1) v"
    and neq: "v \<noteq> composition_final"
    and no_merkle: "\<not> partial_merkle_inconsistency_bad s out"
    and recorded_auth:
      "generic_fri_recorded_layer_chunk_authenticated composition_roots
        fri_query_idxs composition_round_layers final_state round_idx
        (length composition_bs - 1)"
    unfolding
      composition_fri_verifier_tied_final_value_authenticated_replay_gap_def
    by blast
  have no_step:
    "\<And>actual_chunk axp axp_path axn axn_path.
      \<not> (fri_layer_chunk_authenticated
          (composition_roots ! (length composition_bs - 1))
          (fri_evidence_layer_len composition_roots (length composition_bs - 1))
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          actual_chunk final_state \<and>
        fri_layer_step_evidence
          (composition_roots ! (length composition_bs - 1))
          (composition_bs ! (length composition_bs - 1))
          (fri_evidence_layer_len composition_roots (length composition_bs - 1))
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          (2 ^ (length composition_bs - 1))
          (fri_sibling_index
            (fri_evidence_layer_len composition_roots (length composition_bs - 1))
            (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
              (length composition_bs - 1)))
          axp axp_path axn axn_path
          (fri_evidence_next_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          composition_final actual_chunk)"
  proof
    fix actual_chunk axp axp_path axn axn_path
    assume step_auth:
      "fri_layer_chunk_authenticated
          (composition_roots ! (length composition_bs - 1))
          (fri_evidence_layer_len composition_roots (length composition_bs - 1))
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          actual_chunk final_state \<and>
        fri_layer_step_evidence
          (composition_roots ! (length composition_bs - 1))
          (composition_bs ! (length composition_bs - 1))
          (fri_evidence_layer_len composition_roots (length composition_bs - 1))
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          (2 ^ (length composition_bs - 1))
          (fri_sibling_index
            (fri_evidence_layer_len composition_roots (length composition_bs - 1))
            (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
              (length composition_bs - 1)))
          axp axp_path axn axn_path
          (fri_evidence_next_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          composition_final actual_chunk"
    have False
      by (rule generic_fri_final_conflict_false_from_authenticated_step
          [OF forced recorded_auth conjunct1[OF step_auth]
            conjunct2[OF step_auth] no_merkle[unfolded out_eq] neq])
    then show False .
  qed
  have witness:
    "\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers result final_state round_idx v.
      out = Some (result, final_state) \<and>
      accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers \<and>
      0 < length composition_bs \<and>
      round_idx < length fri_query_idxs \<and>
      generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx
        (length composition_bs - 1) v \<and>
      v \<noteq> composition_final \<and>
      \<not> partial_merkle_inconsistency_bad s out \<and>
      generic_fri_recorded_layer_chunk_authenticated composition_roots
        fri_query_idxs composition_round_layers final_state round_idx
        (length composition_bs - 1) \<and>
      (\<forall>actual_chunk axp axp_path axn axn_path.
        \<not> (fri_layer_chunk_authenticated
          (composition_roots ! (length composition_bs - 1))
          (fri_evidence_layer_len composition_roots (length composition_bs - 1))
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          actual_chunk final_state \<and>
        fri_layer_step_evidence
          (composition_roots ! (length composition_bs - 1))
          (composition_bs ! (length composition_bs - 1))
          (fri_evidence_layer_len composition_roots (length composition_bs - 1))
          (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          (2 ^ (length composition_bs - 1))
          (fri_sibling_index
            (fri_evidence_layer_len composition_roots (length composition_bs - 1))
            (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx
              (length composition_bs - 1)))
          axp axp_path axn axn_path
          (fri_evidence_next_idx composition_roots fri_query_idxs round_idx
            (length composition_bs - 1))
          composition_final actual_chunk))"
    using out_eq fri_openings nonempty round_bound forced neq no_merkle
      recorded_auth no_step
    by blast
  show ?thesis
    unfolding
      composition_fri_verifier_tied_final_value_selected_step_missing_gap_def
    using assms witness by blast
qed

lemma wp_composition_fri_verifier_tied_final_value_authenticated_replay_gap_bound_from_selected_step_missing:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_selected_step_missing_gap s)
      s \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_authenticated_replay_gap s)
      s \<le> G"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_authenticated_replay_gap s)
      s \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_final_value_selected_step_missing_gap s)
        s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_final_value_authenticated_replay_gap_imp_selected_step_missing)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

lemma composition_fri_verifier_tied_final_value_replay_gap_imp_merkle_or_slot_or_authenticated_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and gap: "composition_fri_verifier_tied_final_value_replay_gap s out"
  shows
    "partial_merkle_inconsistency_bad s out \<or>
     composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
      s out \<or>
     composition_fri_verifier_tied_final_value_authenticated_replay_gap s out"
proof -
  from gap have sampled:
    "composition_fri_verifier_tied_sampled_final_value_conflict s out"
    unfolding composition_fri_verifier_tied_final_value_replay_gap_def
    by simp
  from composition_fri_verifier_tied_sampled_final_value_conflictE[OF sampled]
  obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table round_idx v
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
    and trace_cand: "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and nonempty: "0 < length composition_bs"
    and round_bound: "round_idx < length fri_query_idxs"
    and forced:
      "generic_fri_round_forced_next_value composition_roots composition_bs
        fri_query_idxs composition_round_layers round_idx
        (length composition_bs - 1) v"
    and neq: "v \<noteq> composition_final"
    by blast
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  show ?thesis
  proof (cases "partial_merkle_inconsistency_bad s out")
    case True
    then show ?thesis by simp
  next
    case no_merkle: False
    let ?j = "length composition_bs - 1"
    have len_composition_bs: "length composition_bs = length composition_roots"
      using accepted_fri_opening_transcript_shapes(4)[OF fri_openings] .
    have layer_bound: "?j < length composition_roots"
      using nonempty len_composition_bs by simp
    show ?thesis
    proof (cases
        "generic_fri_recorded_layer_chunk_authenticated composition_roots
          fri_query_idxs composition_round_layers final_state round_idx ?j")
      case True
      have authenticated_gap:
        "composition_fri_verifier_tied_final_value_authenticated_replay_gap
          s out"
        unfolding
          composition_fri_verifier_tied_final_value_authenticated_replay_gap_def
        by (intro exI conjI)
          (rule out_eq, rule fri_openings, rule aligned, rule trace_cand,
            rule comp_cand, rule trace_low, rule comp_not_low, rule nonempty,
            rule round_bound, rule forced, rule neq,
            use no_merkle True in simp_all)
      then show ?thesis by simp
    next
      case missing_recorded: False
      have outcome:
        "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
        using support out_eq by simp
      have challenges:
        "accepted_fri_challenges s (Some (result, final_state))
          trace_bs fri_dg composition_bs"
        using accepted_fri_opening_transcript_challenges[OF fri_openings]
          out_eq by simp
      have degree_bound: "to_nat fri_dg \<le> maxDegree"
        by (rule verify_monad_accepted_fri_challenges_degree_bound
            [OF outcome challenges])
      have round_bound_rounds: "round_idx < rounds"
        using round_bound
          accepted_fri_opening_transcript_shapes(7)[OF fri_openings]
        by simp
      have raw_layer:
        "\<And>raw.
          0 < fri_layer_lengths (length composition_roots)
              (clength * scale) ! ?j \<and>
          fri_layer_indices (length composition_roots) (index (to_nat raw))
            (clength * scale) ! ?j <
          fri_layer_lengths (length composition_roots)
            (clength * scale) ! ?j"
        by (rule accepted_fri_opening_transcript_composition_raw_layer_bound
            [OF fri_openings degree_bound layer_bound])
      from accepted_fri_opening_transcript_composition_selected_chunk_authenticated_at
          [OF fri_openings out_eq round_bound_rounds layer_bound raw_layer]
      obtain auth_chunk where auth:
        "fri_layer_chunk_authenticated (composition_roots ! ?j)
          (fri_layer_lengths (length composition_roots) (clength * scale) ! ?j)
          (fri_layer_indices (length composition_roots)
            (fri_query_idxs ! round_idx) (clength * scale) ! ?j)
          auth_chunk final_state"
        by blast
      have step:
        "fri_round_layer_evidence composition_roots composition_bs
          fri_query_idxs round_idx ?j composition_round_layers"
        by (rule accepted_fri_opening_transcript_composition_round_layer_evidence
            [OF fri_openings round_bound_rounds layer_bound])
      have generic_step:
        "generic_fri_transcript_step_with_authenticated_chunk
          composition_roots composition_bs fri_query_idxs
          composition_round_layers final_state round_idx ?j"
        by (rule generic_fri_transcript_step_with_authenticated_chunkI
            [OF step])
          (use auth in
            \<open>simp add: fri_evidence_layer_len_def
              fri_evidence_layer_idx_def\<close>)
      have slot_gap:
        "generic_fri_authenticated_slot_recorded_chunk_gap
          composition_roots fri_query_idxs composition_round_layers
          final_state"
        by (rule
            generic_fri_transcript_step_auth_missing_imp_authenticated_slot_recorded_chunk_gap
            [OF generic_step missing_recorded])
      have route_slot_gap:
        "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          s out"
        unfolding
          composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_def
        by (intro exI conjI)
          (rule out_eq, rule fri_openings, rule aligned, rule trace_cand,
            rule comp_cand, rule trace_low, rule comp_not_low, rule slot_gap)
      then show ?thesis by simp
    qed
  qed
qed

lemma wp_composition_fri_verifier_tied_final_value_replay_gap_bound_from_merkle_slot_and_authenticated:
  fixes M A R :: prob
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and slot_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> A"
    and replay_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_authenticated_replay_gap s)
      s \<le> R"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap s) s
      \<le> M + A + R"
proof -
  let ?P = "partial_merkle_inconsistency_bad s"
  let ?Q = "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s"
  let ?R =
    "composition_fri_verifier_tied_final_value_authenticated_replay_gap s"
  have event_le:
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap s) s \<le>
     wp_event verify_monad (\<lambda>out. ?P out \<or> ?Q out \<or> ?R out) s"
    by (rule wp_event_mono_on_support)
      (rule
        composition_fri_verifier_tied_final_value_replay_gap_imp_merkle_or_slot_or_authenticated_on_support)
  have union_le:
    "wp_event verify_monad (\<lambda>out. ?P out \<or> ?Q out \<or> ?R out) s \<le>
      wp_event verify_monad ?P s +
      wp_event verify_monad ?Q s +
      wp_event verify_monad ?R s"
  proof -
    have "wp_event verify_monad (\<lambda>out. ?P out \<or> ?Q out \<or> ?R out) s \<le>
        wp_event verify_monad ?P s +
        wp_event verify_monad (\<lambda>out. ?Q out \<or> ?R out) s"
      by (rule wp_event_union_bound)
    also have "... \<le>
        wp_event verify_monad ?P s +
        (wp_event verify_monad ?Q s + wp_event verify_monad ?R s)"
      by (intro add_mono order.refl wp_event_union_bound)
    finally show ?thesis
      by (simp add: algebra_simps)
  qed
  have bounds:
    "wp_event verify_monad ?P s +
      wp_event verify_monad ?Q s +
      wp_event verify_monad ?R s \<le> M + A + R"
    using merkle_bound slot_bound replay_bound
    by (intro add_mono)
  show ?thesis
    by (rule order_trans[OF event_le order_trans[OF union_le bounds]])
qed

lemma wp_composition_fri_verifier_tied_final_value_replay_gap_bound_from_merkle_slot_and_selected_step:
  fixes M A R :: prob
  assumes merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> M"
    and slot_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> A"
    and selected_step_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_selected_step_missing_gap s)
      s \<le> R"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_replay_gap s) s
      \<le> M + A + R"
proof -
  have authenticated_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_final_value_authenticated_replay_gap s)
      s \<le> R"
    by (rule
        wp_composition_fri_verifier_tied_final_value_authenticated_replay_gap_bound_from_selected_step_missing
      [OF selected_step_bound])
  show ?thesis
    by (rule
        wp_composition_fri_verifier_tied_final_value_replay_gap_bound_from_merkle_slot_and_authenticated)
      (rule merkle_bound, rule slot_bound, rule authenticated_bound)
qed

lemma wp_composition_fri_verifier_tied_authenticated_conflict_bound_from_recorded_missing_next_successor_and_final_gap:
  fixes P M N S G :: prob
  assumes partial_merkle_bound:
    "wp_event verify_monad (partial_merkle_inconsistency_bad s) s \<le> P"
    and missing_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s)
        s \<le> M"
    and next_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_next_value_conflict s) s \<le> N"
    and successor_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_sampled_successor_opening_conflict s)
        s \<le> S"
    and final_gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_final_value_replay_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> (P + M) + N + S + G + P"
  by (rule
      wp_composition_fri_verifier_tied_authenticated_conflict_bound_from_recorded_missing_and_branches)
    (rule partial_merkle_bound,
     rule missing_bound,
     rule next_bound,
     rule successor_bound,
     rule wp_composition_fri_verifier_tied_sampled_final_value_bound_from_replay_gap
       [OF final_gap_bound])

lemma wp_composition_fri_verifier_tied_authenticated_conflict_bound_from_all_replay_gaps:
  fixes P M N S G :: prob
  assumes partial_merkle_bound:
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
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> (P + M) + N + S + G + P"
  by (rule
      wp_composition_fri_verifier_tied_authenticated_conflict_bound_from_recorded_missing_next_successor_and_final_gap)
    (rule partial_merkle_bound,
     rule missing_bound,
     rule wp_composition_fri_verifier_tied_sampled_next_value_bound_from_replay_gap
       [OF next_gap_bound],
     rule wp_composition_fri_verifier_tied_sampled_successor_bound_from_replay_gap
       [OF successor_gap_bound],
     rule final_gap_bound)

definition composition_fri_verifier_tied_assignment_auth_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_assignment_auth_gap s out \<longleftrightarrow>
    composition_fri_verifier_tied_sampled_assignment_conflict s out \<and>
    \<not> composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"

definition composition_fri_verifier_tied_same_layer_auth_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_same_layer_auth_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table result final_state.
      out = Some (result, final_state) \<and>
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
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_same_layer_opening_conflict composition_roots
        composition_bs fri_query_idxs composition_round_layers \<and>
      \<not> generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        composition_roots composition_bs fri_query_idxs composition_round_layers
        final_state)"

definition composition_fri_verifier_tied_same_layer_recorded_auth_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_same_layer_recorded_auth_gap s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table result final_state.
      out = Some (result, final_state) \<and>
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
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_same_layer_recorded_auth_gap composition_roots
        composition_bs fri_query_idxs composition_round_layers final_state)"

definition composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap
  :: "('f, 'a) protocol_channel_scheme \<Rightarrow>
      (unit list \<times> ('f, 'a) protocol_channel_scheme) option \<Rightarrow> bool"
where
  "composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap
      s out \<longleftrightarrow>
    (\<exists>trace_roots trace_bs trace_final fri_dg composition_roots
        composition_bs composition_final fri_query_idxs trace_round_layers
        composition_round_layers fr as trace_openings composition_openings
        trace_table composition_table result final_state.
      out = Some (result, final_state) \<and>
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
      \<not> composition_table_low_degree maxDegree composition_table \<and>
      generic_fri_sampled_same_layer_authenticated_recorded_auth_gap
        composition_roots composition_bs fri_query_idxs composition_round_layers
        final_state)"

lemma composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_false_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and event:
      "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
        s out"
  shows False
proof -
  from event obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table result final_state
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and gap:
      "generic_fri_authenticated_slot_recorded_chunk_gap composition_roots
        fri_query_idxs composition_round_layers final_state"
    unfolding
      composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_def
    by blast
  from gap obtain round_idx layer_idx auth_chunk where
    round_bound: "round_idx < length fri_query_idxs"
    and layer_bound: "layer_idx < length composition_roots"
    and missing:
      "\<not> generic_fri_recorded_layer_chunk_authenticated composition_roots
        fri_query_idxs composition_round_layers final_state round_idx
        layer_idx"
    unfolding generic_fri_authenticated_slot_recorded_chunk_gap_def
    by blast
  have support_some:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using support out_eq by simp
  have challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs fri_dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF fri_openings]
      out_eq by simp
  have degree_bound: "to_nat fri_dg \<le> maxDegree"
    by (rule verify_monad_accepted_fri_challenges_degree_bound
        [OF support_some challenges])
  have round_bound_rounds: "round_idx < rounds"
    using round_bound accepted_fri_opening_transcript_shapes(7)[OF fri_openings]
    by simp
  have all_layer_bounds:
    "\<And>raw k. k < length composition_roots \<Longrightarrow>
      0 < fri_layer_lengths (length composition_roots) (clength * scale) ! k \<and>
      fri_layer_indices (length composition_roots) (index (to_nat raw))
        (clength * scale) ! k <
      fri_layer_lengths (length composition_roots) (clength * scale) ! k"
    by (rule accepted_fri_opening_transcript_composition_raw_layer_bound
        [OF fri_openings degree_bound])
  have recorded:
    "generic_fri_recorded_layer_chunk_authenticated composition_roots
      fri_query_idxs composition_round_layers final_state round_idx layer_idx"
    by (rule
        accepted_fri_opening_transcript_composition_recorded_layer_chunk_authenticated_at
        [OF fri_openings out_eq round_bound_rounds layer_bound
          all_layer_bounds])
  show False
    using missing recorded by simp
qed

lemma wp_composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_zero:
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> (0::prob)"
proof -
  have
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> wp_event verify_monad (\<lambda>_. False) s"
    by (rule wp_event_mono_on_support)
      (rule
        composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_false_on_support)
  also have "... = 0"
    unfolding wp_event_def wp_def dist_expect_def by simp
  finally show ?thesis by simp
qed

lemma composition_fri_verifier_tied_recorded_base_chunk_auth_missing_imp_slot_recorded_chunk_gap:
  assumes
    "composition_fri_verifier_tied_recorded_base_chunk_auth_missing s out"
  shows
    "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table round_idx xp xp_path
      xn xn_path result final_state
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and round_bound: "round_idx < length fri_query_idxs"
    and composition_bs_nonempty: "0 < length composition_bs"
    and missing:
      "\<not> fri_layer_chunk_authenticated (composition_roots ! 0)
        (fri_evidence_layer_len composition_roots 0)
        (fri_evidence_layer_idx composition_roots fri_query_idxs round_idx 0)
        (composition_round_layers ! round_idx ! 0) final_state"
    unfolding
      composition_fri_verifier_tied_recorded_base_chunk_auth_missing_def
    by blast
  have len_composition_bs:
    "length composition_bs = length composition_roots"
    using accepted_fri_opening_transcript_shapes(4)[OF fri_openings] .
  have layer_bound: "0 < length composition_roots"
    using composition_bs_nonempty len_composition_bs by simp
  have len_query: "length fri_query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes(7)[OF fri_openings] .
  have round_bound_rounds: "round_idx < rounds"
    using round_bound len_query by simp
  have raw_layer:
    "\<And>raw.
      0 < fri_layer_lengths (length composition_roots) (clength * scale) ! 0 \<and>
      fri_layer_indices (length composition_roots) (index (to_nat raw))
        (clength * scale) ! 0 <
      fri_layer_lengths (length composition_roots) (clength * scale) ! 0"
    by (rule fri_first_layer_raw_bound[OF layer_bound])
  have auth_step:
    "generic_fri_transcript_step_with_authenticated_chunk composition_roots
      composition_bs fri_query_idxs composition_round_layers final_state
      round_idx 0"
    by (rule
        accepted_fri_opening_transcript_composition_step_with_authenticated_chunk_at
        [OF fri_openings out_eq round_bound_rounds layer_bound raw_layer])
  have recorded_missing:
    "\<not> generic_fri_recorded_layer_chunk_authenticated composition_roots
      fri_query_idxs composition_round_layers final_state round_idx 0"
    using missing
    unfolding generic_fri_recorded_layer_chunk_authenticated_def
    by simp
  have slot_gap:
    "generic_fri_authenticated_slot_recorded_chunk_gap composition_roots
      fri_query_idxs composition_round_layers final_state"
    by (rule
        generic_fri_transcript_step_auth_missing_imp_authenticated_slot_recorded_chunk_gap
        [OF auth_step recorded_missing])
  show ?thesis
    unfolding
      composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_def
    by (intro exI conjI)
      (rule out_eq, rule fri_openings, rule aligned, rule trace_cand,
        rule comp_cand, rule trace_low, rule comp_not_low, rule slot_gap)
qed

lemma wp_composition_fri_verifier_tied_recorded_base_chunk_auth_missing_bound_from_slot_recorded_chunk_gap:
  fixes A :: prob
  assumes slot_gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> A"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s)
      s \<le> A"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s)
      s \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
        s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_recorded_base_chunk_auth_missing_imp_slot_recorded_chunk_gap)
  then show ?thesis
    by (rule order_trans[OF _ slot_gap_bound])
qed

lemma composition_fri_verifier_tied_assignment_imp_authenticated_or_auth_gap:
  assumes "composition_fri_verifier_tied_sampled_assignment_conflict s out"
  shows
    "composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out \<or>
     composition_fri_verifier_tied_assignment_auth_gap s out"
  using assms
  unfolding composition_fri_verifier_tied_assignment_auth_gap_def
  by blast

lemma composition_fri_verifier_tied_assignment_auth_gap_imp_same_layer_auth_gap:
  assumes "composition_fri_verifier_tied_assignment_auth_gap s out"
  shows "composition_fri_verifier_tied_same_layer_auth_gap s out"
proof -
  from assms have conflict:
    "composition_fri_verifier_tied_sampled_assignment_conflict s out"
    and no_auth:
    "\<not> composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
      s out"
    unfolding composition_fri_verifier_tied_assignment_auth_gap_def
    by simp_all
  from conflict obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table
    where fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and sampled:
      "generic_fri_sampled_assignment_conflict composition_table
        composition_roots composition_bs composition_final fri_query_idxs
        composition_round_layers"
    unfolding
      composition_fri_verifier_tied_sampled_assignment_conflict_def
    by blast
  from fri_openings obtain result final_state where out_eq:
    "out = Some (result, final_state)"
    unfolding accepted_fri_opening_transcript_def by blast
  have split:
    "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
      composition_table composition_roots composition_bs composition_final
      fri_query_idxs composition_round_layers final_state \<or>
     (generic_fri_sampled_same_layer_opening_conflict composition_roots
        composition_bs fri_query_idxs composition_round_layers \<and>
      \<not> generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        composition_roots composition_bs fri_query_idxs composition_round_layers
        final_state)"
    by (rule
        generic_fri_sampled_assignment_conflict_imp_authenticated_or_same_layer_auth_gap
        [OF sampled])
  then show ?thesis
  proof
    assume auth:
      "generic_fri_sampled_assignment_conflict_with_authenticated_same_layer
        composition_table composition_roots composition_bs composition_final
        fri_query_idxs composition_round_layers final_state"
    have
      "composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
        s out"
      unfolding
        composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer_def
      by (intro exI conjI)
        (rule fri_openings, rule out_eq, rule aligned, rule trace_cand,
          rule comp_cand, rule trace_low, rule comp_not_low, rule auth)
    then show ?thesis
      using no_auth by contradiction
  next
    assume gap:
      "generic_fri_sampled_same_layer_opening_conflict composition_roots
        composition_bs fri_query_idxs composition_round_layers \<and>
       \<not> generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        composition_roots composition_bs fri_query_idxs composition_round_layers
        final_state"
    show ?thesis
      unfolding composition_fri_verifier_tied_same_layer_auth_gap_def
      by (intro exI conjI)
        (rule out_eq, rule fri_openings, rule aligned, rule trace_cand,
          rule comp_cand, rule trace_low, rule comp_not_low, use gap in simp_all)
  qed
qed

lemma composition_fri_verifier_tied_same_layer_auth_gap_imp_recorded_auth_gap:
  assumes "composition_fri_verifier_tied_same_layer_auth_gap s out"
  shows "composition_fri_verifier_tied_same_layer_recorded_auth_gap s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg
      composition_roots composition_bs composition_final fri_query_idxs
      trace_round_layers composition_round_layers fr as trace_openings
      composition_openings trace_table composition_table result final_state
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and same:
      "generic_fri_sampled_same_layer_opening_conflict composition_roots
        composition_bs fri_query_idxs composition_round_layers"
    and no_auth:
      "\<not> generic_fri_sampled_same_layer_opening_conflict_with_authenticated_chunks
        composition_roots composition_bs fri_query_idxs composition_round_layers
        final_state"
    unfolding composition_fri_verifier_tied_same_layer_auth_gap_def
    by blast
  have recorded_gap:
    "generic_fri_sampled_same_layer_recorded_auth_gap composition_roots
      composition_bs fri_query_idxs composition_round_layers final_state"
    by (rule generic_fri_sampled_same_layer_auth_gap_imp_recorded_auth_gap
        [OF same no_auth])
  show ?thesis
    unfolding composition_fri_verifier_tied_same_layer_recorded_auth_gap_def
    by (intro exI conjI)
      (rule out_eq, rule fri_openings, rule aligned, rule trace_cand,
        rule comp_cand, rule trace_low, rule comp_not_low, rule recorded_gap)
qed

lemma composition_fri_verifier_tied_same_layer_recorded_auth_gap_imp_authenticated_recorded_auth_gap_on_support:
  assumes support: "out \<in> set_dist (execute verify_monad s)"
    and gap: "composition_fri_verifier_tied_same_layer_recorded_auth_gap s out"
  shows
    "composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap
      s out"
proof -
  from gap obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table result final_state
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and recorded_gap:
      "generic_fri_sampled_same_layer_recorded_auth_gap composition_roots
        composition_bs fri_query_idxs composition_round_layers final_state"
    unfolding composition_fri_verifier_tied_same_layer_recorded_auth_gap_def
    by blast
  have outcome:
    "Some (result, final_state) \<in> set_dist (execute verify_monad s)"
    using support out_eq by simp
  have challenges:
    "accepted_fri_challenges s (Some (result, final_state))
      trace_bs fri_dg composition_bs"
    using accepted_fri_opening_transcript_challenges[OF fri_openings]
      out_eq by simp
  have degree_bound: "to_nat fri_dg \<le> maxDegree"
    by (rule verify_monad_accepted_fri_challenges_degree_bound
        [OF outcome challenges])
  have len_composition_bs:
    "length composition_bs = length composition_roots"
    using accepted_fri_opening_transcript_shapes(4)[OF fri_openings] .
  have len_query: "length fri_query_idxs = rounds"
    using accepted_fri_opening_transcript_shapes(7)[OF fri_openings] .
  have auth_step:
    "\<And>round_idx layer_idx.
      round_idx < length fri_query_idxs \<Longrightarrow>
      layer_idx < length composition_bs \<Longrightarrow>
      generic_fri_transcript_step_with_authenticated_chunk composition_roots
        composition_bs fri_query_idxs composition_round_layers final_state
        round_idx layer_idx"
  proof -
    fix round_idx layer_idx
    assume round_bound: "round_idx < length fri_query_idxs"
      and layer_bound_bs: "layer_idx < length composition_bs"
    have round_bound_rounds: "round_idx < rounds"
      using round_bound len_query by simp
    have layer_bound_roots: "layer_idx < length composition_roots"
      using layer_bound_bs len_composition_bs by simp
    show
      "generic_fri_transcript_step_with_authenticated_chunk
        composition_roots composition_bs fri_query_idxs
        composition_round_layers final_state round_idx layer_idx"
      by (rule
          accepted_fri_opening_transcript_composition_step_with_authenticated_chunk_at_raw
          [OF fri_openings out_eq degree_bound round_bound_rounds
            layer_bound_roots])
  qed
  have authenticated_recorded_gap:
    "generic_fri_sampled_same_layer_authenticated_recorded_auth_gap
      composition_roots composition_bs fri_query_idxs composition_round_layers
      final_state"
    by (rule
        generic_fri_recorded_auth_gap_imp_authenticated_recorded_auth_gap
        [OF recorded_gap auth_step])
  show ?thesis
    unfolding
      composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap_def
    by (intro exI conjI)
      (rule out_eq, rule fri_openings, rule aligned, rule trace_cand,
        rule comp_cand, rule trace_low, rule comp_not_low,
        rule authenticated_recorded_gap)
qed

lemma composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap_imp_slot_recorded_chunk_gap:
  assumes
    "composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap
      s out"
  shows
    "composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
      s out"
proof -
  from assms obtain trace_roots trace_bs trace_final fri_dg composition_roots
      composition_bs composition_final fri_query_idxs trace_round_layers
      composition_round_layers fr as trace_openings composition_openings
      trace_table composition_table result final_state
    where out_eq: "out = Some (result, final_state)"
    and fri_openings:
      "accepted_fri_opening_transcript s out trace_roots trace_bs
        trace_final fri_dg composition_roots composition_bs
        composition_final fri_query_idxs trace_round_layers
        composition_round_layers"
    and aligned:
      "accepted_with_partial_initial_openings_aligned s out fr trace_roots
        trace_final as fri_dg composition_roots composition_final
        fri_query_idxs trace_openings composition_openings"
    and trace_cand:
      "partial_trace_table_candidate trace_table trace_openings"
    and comp_cand:
      "partial_composition_table_candidate composition_table
        composition_openings"
    and trace_low: "trace_table_low_degree trace_table"
    and comp_not_low:
      "\<not> composition_table_low_degree maxDegree composition_table"
    and gap:
      "generic_fri_sampled_same_layer_authenticated_recorded_auth_gap
        composition_roots composition_bs fri_query_idxs composition_round_layers
        final_state"
    unfolding
      composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap_def
    by blast
  have slot_gap:
    "generic_fri_authenticated_slot_recorded_chunk_gap composition_roots
      fri_query_idxs composition_round_layers final_state"
    by (rule
        generic_fri_authenticated_recorded_auth_gap_imp_slot_recorded_chunk_gap
        [OF gap])
  show ?thesis
    unfolding
      composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap_def
    by (intro exI conjI)
      (rule out_eq, rule fri_openings, rule aligned, rule trace_cand,
        rule comp_cand, rule trace_low, rule comp_not_low, rule slot_gap)
qed

lemma wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_authenticated_and_auth_gap:
  fixes C G :: prob
  assumes authenticated_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
      s \<le> C"
    and auth_gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_assignment_auth_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s
      \<le> C + G"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s \<le>
      wp_event verify_monad
        (\<lambda>out.
          composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer
            s out \<or>
          composition_fri_verifier_tied_assignment_auth_gap s out) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_assignment_imp_authenticated_or_auth_gap)
  also have "... \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_sampled_assignment_conflict_with_authenticated_same_layer s)
        s +
      wp_event verify_monad
        (composition_fri_verifier_tied_assignment_auth_gap s) s"
    by (rule wp_event_union_bound)
  also have "... \<le> C + G"
    by (intro add_mono authenticated_bound auth_gap_bound)
  finally show ?thesis .
qed

lemma wp_composition_fri_verifier_tied_assignment_auth_gap_bound_from_same_layer_auth_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_auth_gap s) s \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_assignment_auth_gap s) s \<le> G"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_assignment_auth_gap s) s \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_same_layer_auth_gap s) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_assignment_auth_gap_imp_same_layer_auth_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

lemma wp_composition_fri_verifier_tied_same_layer_auth_gap_bound_from_recorded_auth_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_recorded_auth_gap s) s
      \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_auth_gap s) s \<le> G"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_auth_gap s) s \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_same_layer_recorded_auth_gap s) s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_same_layer_auth_gap_imp_recorded_auth_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

lemma wp_composition_fri_verifier_tied_same_layer_recorded_auth_gap_bound_from_authenticated_recorded_auth_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap
        s) s \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_recorded_auth_gap s) s
      \<le> G"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_recorded_auth_gap s) s \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap
          s) s"
    by (rule wp_event_mono_on_support)
      (rule
        composition_fri_verifier_tied_same_layer_recorded_auth_gap_imp_authenticated_recorded_auth_gap_on_support)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

lemma wp_composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap_bound_from_slot_recorded_chunk_gap:
  fixes G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> G"
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap
        s) s \<le> G"
proof -
  have "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap
        s) s \<le>
      wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
        s"
    by (rule wp_event_mono)
      (rule
        composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap_imp_slot_recorded_chunk_gap)
  then show ?thesis
    by (rule order_trans[OF _ gap_bound])
qed

lemma wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_auth_gap_and_residuals:
  fixes A P M N S G :: prob
  assumes auth_gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_assignment_auth_gap s) s \<le> A"
    and partial_merkle_bound:
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
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s
      \<le> ((P + M) + N + S + G + P) + A"
  by (rule
      wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_authenticated_and_auth_gap)
    (rule wp_composition_fri_verifier_tied_authenticated_conflict_bound_from_all_replay_gaps
        [OF partial_merkle_bound missing_bound next_gap_bound
          successor_gap_bound final_gap_bound],
     rule auth_gap_bound)

lemma wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_same_layer_auth_gap_and_residuals:
  fixes A P M N S G :: prob
  assumes same_layer_gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_auth_gap s) s \<le> A"
    and partial_merkle_bound:
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
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s
      \<le> ((P + M) + N + S + G + P) + A"
  by (rule
      wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_auth_gap_and_residuals)
    (rule
      wp_composition_fri_verifier_tied_assignment_auth_gap_bound_from_same_layer_auth_gap
        [OF same_layer_gap_bound],
     rule partial_merkle_bound,
     rule missing_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_recorded_auth_gap_and_residuals:
  fixes A P M N S G :: prob
  assumes recorded_gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_recorded_auth_gap s) s
      \<le> A"
    and partial_merkle_bound:
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
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s
      \<le> ((P + M) + N + S + G + P) + A"
  by (rule
      wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_same_layer_auth_gap_and_residuals)
    (rule
      wp_composition_fri_verifier_tied_same_layer_auth_gap_bound_from_recorded_auth_gap
        [OF recorded_gap_bound],
     rule partial_merkle_bound,
     rule missing_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_authenticated_recorded_auth_gap_and_residuals:
  fixes A P M N S G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap
        s) s \<le> A"
    and partial_merkle_bound:
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
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s
      \<le> ((P + M) + N + S + G + P) + A"
  by (rule
      wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_recorded_auth_gap_and_residuals)
    (rule
      wp_composition_fri_verifier_tied_same_layer_recorded_auth_gap_bound_from_authenticated_recorded_auth_gap
        [OF gap_bound],
     rule partial_merkle_bound,
     rule missing_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_slot_recorded_chunk_gap_and_residuals:
  fixes A P M N S G :: prob
  assumes gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap s)
      s \<le> A"
    and partial_merkle_bound:
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
  shows
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s
      \<le> ((P + M) + N + S + G + P) + A"
  by (rule
      wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_authenticated_recorded_auth_gap_and_residuals)
    (rule
      wp_composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap_bound_from_slot_recorded_chunk_gap
        [OF gap_bound],
     rule partial_merkle_bound,
     rule missing_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_composition_fri_verifier_tied_bound_from_sampled_auth_gap_and_residuals:
  fixes R A P M N S G :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and auth_gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_assignment_auth_gap s) s \<le> A"
    and partial_merkle_bound:
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
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s
      \<le> R + (((P + M) + N + S + G + P) + A)"
proof -
  have conflict_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_sampled_assignment_conflict s) s
      \<le> ((P + M) + N + S + G + P) + A"
    by (rule
        wp_composition_fri_verifier_tied_sampled_assignment_conflict_bound_from_auth_gap_and_residuals)
      (rule auth_gap_bound,
       rule partial_merkle_bound,
       rule missing_bound,
       rule next_gap_bound,
       rule successor_gap_bound,
       rule final_gap_bound)
  show ?thesis
    by (rule
        wp_composition_fri_verifier_tied_bound_from_sampled_conflict
          [OF sampled_bound conflict_bound])
qed

lemma wp_composition_fri_verifier_tied_bound_from_sampled_same_layer_auth_gap_and_residuals:
  fixes R A P M N S G :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and same_layer_gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_same_layer_auth_gap s) s \<le> A"
    and partial_merkle_bound:
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
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s
      \<le> R + (((P + M) + N + S + G + P) + A)"
  by (rule
      wp_composition_fri_verifier_tied_bound_from_sampled_auth_gap_and_residuals)
    (rule sampled_bound,
     rule
       wp_composition_fri_verifier_tied_assignment_auth_gap_bound_from_same_layer_auth_gap
        [OF same_layer_gap_bound],
     rule partial_merkle_bound,
     rule missing_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_composition_fri_verifier_tied_bound_from_sampled_recorded_auth_gap_and_residuals:
  fixes R A P M N S G :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and recorded_gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_same_layer_recorded_auth_gap s) s
        \<le> A"
    and partial_merkle_bound:
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
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s
      \<le> R + (((P + M) + N + S + G + P) + A)"
  by (rule
      wp_composition_fri_verifier_tied_bound_from_sampled_same_layer_auth_gap_and_residuals)
    (rule sampled_bound,
     rule
       wp_composition_fri_verifier_tied_same_layer_auth_gap_bound_from_recorded_auth_gap
        [OF recorded_gap_bound],
     rule partial_merkle_bound,
     rule missing_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_composition_fri_verifier_tied_bound_from_sampled_authenticated_recorded_auth_gap_and_residuals:
  fixes R A P M N S G :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap
          s) s \<le> A"
    and partial_merkle_bound:
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
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s
      \<le> R + (((P + M) + N + S + G + P) + A)"
  by (rule
      wp_composition_fri_verifier_tied_bound_from_sampled_recorded_auth_gap_and_residuals)
    (rule sampled_bound,
     rule
       wp_composition_fri_verifier_tied_same_layer_recorded_auth_gap_bound_from_authenticated_recorded_auth_gap
        [OF gap_bound],
     rule partial_merkle_bound,
     rule missing_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma wp_composition_fri_verifier_tied_bound_from_sampled_slot_recorded_chunk_gap_and_residuals:
  fixes R A P M N S G :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          s) s \<le> A"
    and partial_merkle_bound:
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
  shows
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s
      \<le> R + (((P + M) + N + S + G + P) + A)"
  by (rule
      wp_composition_fri_verifier_tied_bound_from_sampled_authenticated_recorded_auth_gap_and_residuals)
    (rule sampled_bound,
     rule
       wp_composition_fri_verifier_tied_same_layer_authenticated_recorded_auth_gap_bound_from_slot_recorded_chunk_gap
        [OF gap_bound],
     rule partial_merkle_bound,
     rule missing_bound,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound)

lemma composition_fri_reachable_partial_candidate_reduction_from_verifier_tied_residual_bounds:
  fixes R A P M N S G T :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and slot_gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          s) s \<le> A"
    and partial_merkle_bound:
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
    and verifier_gap_bound:
      "wp_event verify_monad
        (composition_fri_reachable_verifier_tie_gap s) s \<le> T"
    and total_bound:
      "R + (((P + M) + N + S + G + P) + A) + T
        \<le> composition_fri_error"
  shows "composition_fri_reachable_partial_candidate_reduction_assumption s"
proof -
  have verifier_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_partial_candidate s) s
      \<le> R + (((P + M) + N + S + G + P) + A)"
    by (rule
        wp_composition_fri_verifier_tied_bound_from_sampled_slot_recorded_chunk_gap_and_residuals
        [OF sampled_bound slot_gap_bound partial_merkle_bound missing_bound
          next_gap_bound successor_gap_bound final_gap_bound])
  show ?thesis
    by (rule
        composition_fri_reachable_partial_candidate_reduction_from_verifier_tied_and_gap
        [OF verifier_bound verifier_gap_bound total_bound])
qed

lemma composition_fri_reachable_partial_candidate_reduction_from_verifier_tied_residual_bounds_with_recorded_missing_zero:
  fixes R A P N S G T :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and slot_gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
        s) s \<le> A"
    and partial_merkle_bound:
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
    and verifier_gap_bound:
    "wp_event verify_monad
      (composition_fri_reachable_verifier_tie_gap s) s \<le> T"
    and total_bound:
    "R + (((P + 0) + N + S + G + P) + A) + T
      \<le> composition_fri_error"
  shows "composition_fri_reachable_partial_candidate_reduction_assumption s"
  by (rule composition_fri_reachable_partial_candidate_reduction_from_verifier_tied_residual_bounds
      [where M = 0])
    (rule sampled_bound,
     rule slot_gap_bound,
     rule partial_merkle_bound,
     rule wp_composition_fri_verifier_tied_recorded_base_chunk_auth_missing_zero,
     rule next_gap_bound,
     rule successor_gap_bound,
     rule final_gap_bound,
     rule verifier_gap_bound,
     rule total_bound)

lemma composition_fri_verifier_tied_reduction_from_residual_bounds:
  fixes R A P M N S G :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and slot_gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          s) s \<le> A"
    and partial_merkle_bound:
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
    and total_bound:
      "R + (((P + M) + N + S + G + P) + A)
        \<le> composition_fri_error"
  shows "composition_fri_verifier_tied_reduction s"
  unfolding composition_fri_verifier_tied_reduction_def
  by (rule order_trans[
      OF wp_composition_fri_verifier_tied_bound_from_sampled_slot_recorded_chunk_gap_and_residuals
        [OF sampled_bound slot_gap_bound partial_merkle_bound missing_bound
          next_gap_bound successor_gap_bound final_gap_bound] total_bound])

lemma composition_fri_verifier_tied_reduction_from_residual_bounds_without_recorded_missing:
  fixes R A P N S G :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and slot_gap_bound:
      "wp_event verify_monad
        (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
          s) s \<le> A"
    and partial_merkle_bound:
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
    and total_bound:
      "R + (((P + A) + N + S + G + P) + A)
        \<le> composition_fri_error"
  shows "composition_fri_verifier_tied_reduction s"
proof -
  have missing_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_recorded_base_chunk_auth_missing s)
      s \<le> A"
    by (rule
        wp_composition_fri_verifier_tied_recorded_base_chunk_auth_missing_bound_from_slot_recorded_chunk_gap
        [OF slot_gap_bound])
  show ?thesis
    by (rule composition_fri_verifier_tied_reduction_from_residual_bounds
        [OF sampled_bound slot_gap_bound partial_merkle_bound missing_bound
          next_gap_bound successor_gap_bound final_gap_bound total_bound])
qed

lemma composition_fri_verifier_tied_reduction_from_residual_bounds_with_recorded_missing_zero:
  fixes R A P N S G :: prob
  assumes sampled_bound:
    "wp_event verify_monad
      (composition_fri_bad_with_verifier_tied_sampled_layer_chain s) s \<le> R"
    and slot_gap_bound:
    "wp_event verify_monad
      (composition_fri_verifier_tied_authenticated_slot_recorded_chunk_gap
        s) s \<le> A"
    and partial_merkle_bound:
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
    and total_bound:
    "R + (((P + 0) + N + S + G + P) + A)
      \<le> composition_fri_error"
  shows "composition_fri_verifier_tied_reduction s"
  by (rule composition_fri_verifier_tied_reduction_from_residual_bounds
      [where M = 0, OF sampled_bound slot_gap_bound partial_merkle_bound
        wp_composition_fri_verifier_tied_recorded_base_chunk_auth_missing_zero
        next_gap_bound successor_gap_bound final_gap_bound total_bound])

end

end
